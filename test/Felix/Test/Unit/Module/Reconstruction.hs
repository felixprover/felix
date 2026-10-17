{-# LANGUAGE NoImplicitPrelude #-}

-- Imported reconstruction realizations, cache invalidation, and admission.
module Felix.Test.Unit.Module.Reconstruction (tests) where

import Base
import Felix.Cache.Codec
import Felix.Checking.Authority qualified as Authority
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Core qualified as Core
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Elaboration qualified as Elaboration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Instance qualified as Instance
import Felix.Checking.Module qualified as Module
import Felix.Checking.Notion qualified as Notion
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Checking.Structure.Obligation qualified as Obligation
import Felix.Module (moduleName)
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Provers qualified as Provers
import Felix.Report.Location
import Felix.Report.Diagnostic
import Felix.Source
import Felix.Source.Graph qualified as Graph
import Felix.Store qualified as Store
import Felix.Syntax.Interface qualified as Syntax
import Felix.Syntax.Abstract qualified as Raw
import Felix.Test.Support.Imports (admitTestModule)
import Felix.Test.Unit.Module.Support
import Felix.Verification qualified as Verification

import Control.Exception (bracket)
import Control.Monad (when)
import Data.ByteString qualified as ByteString
import Data.IORef (newIORef, modifyIORef', readIORef, writeIORef)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Encoding
import Data.Vector qualified as Vector
import System.FilePath.Posix ((</>))
import System.Directory (getCurrentDirectory)
import System.IO.Temp qualified as Temp
import Test.Tasty
import Test.Tasty.HUnit

tests :: [TestTree]
tests =
    [ testCase "invalidates imported reconstruction realizations without stale public facts" invalidatesRealizations
    , testCase "rejects corrupted realization provenance and late partial admission" checksRealizationAdmission
    , testCase "reprepares reconstruction fields when target or base changes" changesReconstructionInputs
    , testCase "retains record obligation origins across warm source-only movement" movesObligationOrigins
    ]

movesObligationOrigins :: Assertion
movesObligationOrigins = Temp.withSystemTempDirectory "record-obligation-origins" \root ->
    withAcceptedFixtureVampire "record-obligation-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts root
        cwd <- getCurrentDirectory
        schema <- Encoding.decodeUtf8 <$> ByteString.readFile (cwd </> "test/structure-spikes/carrierless-basic.tex")
        parameter <- Encoding.decodeUtf8 <$> ByteString.readFile (cwd </> "test/structure-spikes/reconstruction-parameter-law-rejected.tex")
        field <- Encoding.decodeUtf8 <$> ByteString.readFile (cwd </> "test/structure-spikes/reconstruction-field-law-rejected.tex")
        opens <- Encoding.decodeUtf8 <$> ByteString.readFile (cwd </> "test/structure-spikes/reconstruction-opens-law-rejected.tex")
        let open = snd <$> (Store.openStore (root </> "store.sqlite") (Identity.theoryId foundation) >>= expectRight)
            write path = ByteString.writeFile (root </> path) . Encoding.encodeUtf8
            localSchema = Text.replace "test/structure-spikes/carrierless-basic.tex" "schema.tex"
            check store source = do
                request <- expectRight (searchedRoot source)
                graph <- expectRightIO (Graph.buildResolvedSourceGraph mounts request)
                outcome <- expectRightIO (Verification.withVerificationSessionUsingStore store \session ->
                    Verification.checkWorkspace session Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand = Parse.NoPresentation
                        , Verification.checkStoreValidationMode = Verification.WarmStoreValidation
                        , Verification.checkModuleJobs = testSequentialJobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = Verification.verificationRequestObserver (\_ _ -> pure ())
                        }) >>= expectRight
                case Verification.checkVerificationResult outcome of
                    Verification.VerificationCheckingFailure _
                        (Verification.VerificationTypedModuleError _
                            (Module.TypedActionFailed (Module.TypedInstanceFailed
                                (Instance.InstanceProofFailed failure@(Proof.ProofRecordObligations context _)))) _) ->
                        pure (Proof.proofErrorLocation failure, context, Proof.proofErrorDiagnostic failure)
                    other -> fail ("expected a record proof preparation failure: " <> show other)
            law context = sole "atlas law" [(obligation, key, occurrence)
                | obligation <- Obligation.contextRequirements context
                , (key, occurrence) <- Map.toAscList (Obligation.recordObligationOrigins obligation)
                , Schema.requirementOccurrenceMarker occurrence == Just (Raw.Marker "coordinate_atlas_bound")]
        write "schema.tex" schema
        write "consumer.tex" (localSchema parameter)
        (beforeLocation, beforeContext, _) <- bracket open Store.closeStore (\store -> check store "consumer.tex")
        (before, beforeKey, beforeOrigin) <- law beforeContext
        write "schema.tex" ("% moved schema\n\n" <> schema)
        write "consumer.tex" ("% moved consumer\n\n\n" <> localSchema parameter)
        bracket open Store.closeStore \store -> do
            (afterLocation, afterContext, _) <- check store "consumer.tex"
            (after, afterKey, afterOrigin) <- law afterContext
            afterKey @?= beforeKey
            Obligation.recordObligationFormula after @?= Obligation.recordObligationFormula before
            locLine afterLocation @?= locLine beforeLocation + 3
            locLine (Schema.requirementOccurrenceLocation afterOrigin) @?=
                locLine (Schema.requirementOccurrenceLocation beforeOrigin) + 2
            locLine (Obligation.recordObligationResult after) @?= locLine (Obligation.recordObligationResult before) + 3
            assertBool "copied origins point at the moved base"
                (all (\(here, kind) -> kind == "copied field base" && locLine here == 10)
                    (Map.elems (Obligation.recordObligationFields after)))
            write "consumer.tex" (localSchema field)
            (_, fieldContext, _) <- check store "consumer.tex"
            (fieldLaw, _, _) <- law fieldContext
            assertBool "replacements retain written field origins"
                (all ((== "written field clause") . snd) (Map.elems (Obligation.recordObligationFields fieldLaw)))
            write "opens.tex" opens
            (opensLocation, opensContext, diagnostic) <- check store "opens.tex"
            (_, opensKey, opensOrigin) <- sole "opens specification"
                [(obligation, key, occurrence)
                | obligation <- Obligation.contextRequirements opensContext
                , (key, occurrence) <- Map.toAscList (Obligation.recordObligationOrigins obligation)
                , Schema.requirementOccurrenceMarker occurrence == Just (Raw.Marker "opens_family")]
            case Schema.requirementOrigin opensKey of
                Schema.FieldSpecificationOrigin _ identity ->
                    assertBool "the opens requirement resolves the actual written field"
                        (any (\obligation -> case Map.lookup identity (Obligation.recordObligationFields obligation) of
                            Just (here, kind) -> locLine here == 7 && kind == "written field clause"
                            Nothing -> False)
                            (Obligation.contextRequirements opensContext))
                _ -> fail "opens_family lost its field-specification origin"
            assertBool "imported requirement has its source location"
                (locLine (Schema.requirementOccurrenceLocation opensOrigin) > 0)
            locLine opensLocation @?= 10
            assertBool "the failed opens claim is exactly the specialized requirement"
                (Obligation.contextIsMatchingRequirement opensContext)
            rendered <- maybe (fail "record failure lost the existing diagnostic") pure diagnostic
            diagnosticPrimary rendered @?= Just opensLocation
            assertBool "rendered failure names the real requirement"
                ("opens_family" `Text.isInfixOf` Text.pack (show (diagnosticNotes rendered)))
            -- Reuse the admitted imports, but send the same missing field
            -- requirement through a real prepared ATP request and a rejecting
            -- resolver. It must keep both its proof location and sidecar.
            let accepted = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation accepted)
            importsWorkspace <- parseFinalWorkspace prelude mounts "topology/topological-space.tex"
            imports <- compileFinalParsedWorkspaceWithResolver foundation prelude accepted importsWorkspace
            write "opens.tex" (Text.replace "    Follows." "    Follows by \\auto{topological_space}." (Text.replace
                "$\\opens[\\OpensCopy{X}{B}]\\subseteq\\pow{\\carrier[\\OpensCopy{X}{B}]}$."
                "$\\opens[\\OpensCopy{X}{B}]\\subseteq\\pow{\\carrier[\\OpensCopy{X}{B}]}$ by \\auto{opens_family}." opens))
            externalWorkspace <- parseFinalWorkspace prelude mounts "opens.tex"
            let parsed = Parsed.parsedWorkspaceRootModule externalWorkspace
                blocks = Parsed.parsedModuleBlocks parsed
            (index, construction, proof) <- sole "external obligation construction"
                [(index, block, mathematicalProof)
                | (index, block@Raw.BlockConstruction{}, Raw.BlockProof _ mathematicalProof _)
                    <- zip3 [0..] blocks (drop 1 blocks)]
            let entries = [Parsed.parsedSyntaxOccurrenceEntry occurrence
                    | occurrence <- Parsed.parsedModuleSyntaxOccurrences parsed
                    , Parsed.parsedSyntaxOccurrenceBlockIndex occurrence == index]
            external <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> imports))
                (Declaration.vampireResolver (pure . counterexampleResolution)) AlwaysMissValidation do
                    prepared <- Declaration.runProspectiveLoweringDriver (Instance.prepareInstance construction (Just proof) entries)
                        >>= either (Declaration.failModuleDriver . show) pure
                    lowered <- Declaration.runProspectiveLoweringDriver (Instance.lowerPreparedInstance prepared)
                        >>= either Declaration.failDeclarationDriver pure
                    Declaration.admitCheckedDeclaration lowered Instance.authorizeCheckedInstance
            case external of
                Declaration.DriverFailed (Declaration.DriverDeclarationFailed failure) _ -> do
                    (here, resolution, statistics) <- maybe (fail "external failure lost its proof location") pure
                        (Declaration.locatedVampireFailure failure)
                    contexts <- sole "external obligation context" (Declaration.declarationRecordObligations failure)
                    assertBool "external failure matches the same requirement"
                        (Obligation.contextIsMatchingRequirement contexts)
                    let reported = Verification.failedVerificationDiagnostic
                            (Verification.FailedVerification here resolution statistics [contexts])
                    locLine here @?= 10
                    diagnosticPrimary reported @?= Just here
                    assertBool "external report retains the field requirement"
                        ("opens_family" `Text.isInfixOf` Text.pack (show (diagnosticNotes reported)))
                Declaration.DriverFailed failure _ -> fail ("external obligation failed before ATP: " <> show failure)
                _ -> fail "the missing opens requirement did not reach the rejecting ATP resolver"

changesReconstructionInputs :: Assertion
changesReconstructionInputs = Temp.withSystemTempDirectory "reconstruction-inputs" \directory ->
    withAcceptedFixtureVampire "reconstruction-inputs-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        bracket (snd <$> (Store.openStore (directory </> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)) Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/reconstruction-import-expression.tex"
            modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
            let parsed = Parsed.parsedWorkspaceRootModule workspace
                claims = [(assumptions, conclusion, expression)
                    | Raw.BlockClaim _ _ _ _ (Raw.Claim assumptions conclusion@(Raw.StmtFormula
                        (Raw.FormulaChain (Raw.ChainBase (expression :| []) _ _ _)))) <- Parsed.parsedModuleBlocks parsed]
            values <- for claims \(assumptions, conclusion, expression) -> do
                driven <- expectRight =<< runModuleDriver foundation (moduleName (Parsed.parsedModuleAddress parsed))
                    (Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> modules))
                    unusedResolver AlwaysMissValidation
                    (Declaration.runProspectiveLoweringDriver do
                        envelope <- Elaboration.elaborateClaimEnvelopeWithFormationObservation id assumptions conclusion
                        case envelope of
                            Left failure -> pure (Left failure)
                            Right (_, context) -> Elaboration.elaborateReconstructionWithBudget
                                (Notion.initialFormationSearchBudget Notion.defaultFormationSearchLimits) context expression)
                case driven of
                    Declaration.DriverSucceeded result _ _ -> expectRight result
                    _ -> fail "changed reconstruction expression did not prepare"
            case values of
                [([original], _, originalAttempts, _), ([], _, targetAttempts, _), ([changed], _, changedAttempts, _)] -> do
                    Schema.resolvedFieldIdentity (Elaboration.elaboratedRecordField changed) @?=
                        Schema.resolvedFieldIdentity (Elaboration.elaboratedRecordField original)
                    for_ [(original, Core.CBound 1), (changed, Core.CBound 0)] \(entry, argument) ->
                        case Elaboration.elaboratedRecordValue entry of
                            Core.CApp (Core.CGlobal projection) (Core.CApp _ actualArgument) -> do
                                projection @?= Schema.resolvedFieldProjection (Elaboration.elaboratedRecordField entry)
                                actualArgument @?= argument
                            _ -> fail "copied value did not retain its written base"
                    (Elaboration.reconstructionAttemptAssertion <$> targetAttempts) @?=
                        (Elaboration.reconstructionAttemptAssertion <$> originalAttempts)
                    assertBool "base change requests different instantiated evidence"
                        ((Elaboration.reconstructionAttemptAssertion <$> changedAttempts) /=
                            (Elaboration.reconstructionAttemptAssertion <$> originalAttempts))
                _ -> fail "target/base mutation did not change the intended field mapping"

data Sources = Sources
    { schemaSource :: !Text
    , baseSource :: !Text
    , producerSource :: !Text
    , consumerSource :: !Text
    }

checksRealizationAdmission :: Assertion
checksRealizationAdmission = Temp.withSystemTempDirectory "realization-admission" \directory ->
    withAcceptedFixtureVampire "realization-admission-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts =<< getCurrentDirectory
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            open = snd <$> (Store.openStore (directory </> "store.sqlite")
                (Identity.theoryId foundation) >>= expectRight)
        (prior, consumerOwner, consumer, consumerProof, key, syntax) <- bracket open Store.closeStore \store -> do
            prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
            workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/reconstruction-import-producer.tex"
            modules <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
            producer <- sole "producer" (take 1 (reverse modules))
            let semantic = completedModuleSemantic producer
                batches = Commit.pendingModulePrefixBatches (Module.completedTypedModulePrefix producer)
                facts = concatMap (Semantic.declarationDeltaFacts . Commit.committedBatchDelta) batches
                propositions = concatMap Commit.committedBatchPropositions batches
                objects = concatMap Commit.committedBatchObjects batches
                parents = [evidence | evidence <- Module.sealedTypedModuleEvidence (Module.finalPreludeModule prelude) : (completedModuleEvidence <$> modules),
                    Semantic.semanticInterfaceAssertedId (Declaration.evidenceInterface evidence)
                        `elem` Semantic.semanticInterfaceDirectInputs semantic]
                alias name = sole "public fact"
                    [fact | batch <- batches, binding <- Semantic.declarationDeltaAliases (Commit.committedBatchDelta batch),
                        Semantic.semanticAliasName binding == Semantic.semanticName name,
                        fact <- facts, Semantic.semanticFactFingerprint fact == Semantic.semanticAliasTarget binding]
                admit rows certificates = admitTestModule (Identity.theoryId foundation) parents semantic objects rows certificates
            portable <- for (concatMap Commit.committedBatchValidationCertificates batches) \certificate ->
                expectRight (decodeCache Authority.getValidationCertificateCache
                    (encodeCache (Authority.putValidationCertificateCache certificate)))
            void (expectRight =<< admit propositions portable)
            projection <- alias "imported_clearprojection_atlas"
            result <- alias "imported_clear"
            other <- sole "different retained proposition" (take 1
                [p | p <- propositions, Identity.checkedPropositionId p /= Semantic.semanticFactProposition projection])
            let substituted = [if Identity.checkedPropositionId p == Semantic.semanticFactProposition projection
                    then other else p | p <- propositions]
            admit substituted portable >>= \case
                Left Declaration.ImportedEvidencePropositionMissing{} -> pure ()
                otherResult -> fail ("altered projection row was not rejected: " <> either show (const "accepted") otherResult)
            wrongReference <- for (zip facts portable) \(fact, certificate) ->
                if Semantic.semanticFactFingerprint fact == Semantic.semanticFactFingerprint projection
                then expectRight (Authority.validationCertificate (Semantic.semanticFactAuthority result)
                    (Authority.validationDirectAuthorization certificate))
                else pure certificate
            admit propositions wrongReference >>= \case
                Left Declaration.ImportedEvidenceCertificateTargetMismatch{} -> pure ()
                otherResult -> fail ("projection authorization reference was not rejected: " <> either show (const "accepted") otherResult)
            equationAuthorization <- sole "retained equation authorization" (take 1
                [authorization | certificate <- portable,
                    let authorization = Authority.validationDirectAuthorization certificate,
                    Authority.CheckedKernelConstruction Authority.CheckedDefinitionEquation{} <- [authorization]])
            missingResultProvenance <- for (zip facts portable) \(fact, certificate) ->
                if Semantic.semanticFactFingerprint fact == Semantic.semanticFactFingerprint result
                then expectRight (Authority.validationCertificate (Authority.validationTarget certificate) equationAuthorization)
                else pure certificate
            admit propositions missingResultProvenance >>= \case
                Left Declaration.ImportedProviderResultRuleAuthorityInvalid{} -> pure ()
                otherResult -> fail ("result registration accepted missing source-proof provenance: "
                    <> either show (const "accepted") otherResult)

            let parsed = Parsed.parsedWorkspaceRootModule workspace
                blocks = Parsed.parsedModuleBlocks parsed
                owner = moduleName (Parsed.parsedModuleAddress parsed)
            anchor <- sole "earlier anchor"
                [block | block@(Raw.BlockClaim _ _ _ (Raw.Marker "imported_anchor") _) <- blocks]
            (index, construction, mathematicalProof) <- sole "construction and its mathematical proof"
                [(index, block, proof) | (index, block@Raw.BlockConstruction{}, Raw.BlockProof _ proof _)
                    <- zip3 [0..] blocks (drop 1 blocks)]
            let entries = [Parsed.parsedSyntaxOccurrenceEntry occurrence
                    | occurrence <- Parsed.parsedModuleSyntaxOccurrences parsed,
                        Parsed.parsedSyntaxOccurrenceBlockIndex occurrence == index]
                anchorAction = do
                    prepared <- Declaration.runProspectiveLoweringDriver (Proof.prepareProof anchor Nothing)
                        >>= either (Declaration.failModuleDriver . show) pure
                    lowered <- Declaration.runProspectiveLoweringDriver (Proof.lowerPreparedProof prepared)
                        >>= either Declaration.failDeclarationDriver pure
                    void (Declaration.admitCheckedDeclaration lowered Proof.authorizeCheckedProof)
            baseline <- expectRight =<< runModuleDriver foundation owner parents resolver AlwaysMissValidation anchorAction
            (prior, priorPrefix) <- case baseline of
                Declaration.DriverSucceeded () evidence prefix -> pure (evidence, prefix)
                _ -> fail "earlier declaration did not admit"
            preparedMathematics <- newIORef False
            authorizedConsequences <- newIORef False
            failed <- expectRight =<< runModuleDriver foundation owner parents resolver AlwaysMissValidation do
                anchorAction
                prepared <- Declaration.runProspectiveLoweringDriver (Instance.prepareInstance construction (Just mathematicalProof) entries)
                    >>= either (Declaration.failModuleDriver . show) pure
                liftIO (writeIORef preparedMathematics True)
                lowered <- Declaration.runProspectiveLoweringDriver (Instance.lowerPreparedInstance prepared)
                    >>= either Declaration.failDeclarationDriver pure
                Declaration.admitCheckedDeclaration lowered \authorization candidates -> do
                    Instance.authorizeCheckedInstance authorization candidates
                    liftIO (writeIORef authorizedConsequences True)
                    -- The existing authorizer boundary may decline final
                    -- admission after all mathematical preparation/authorization.
                    Declaration.failDeclaration Declaration.DeclarationAuthorizationFrontierIncomplete
            assertEqual "mathematical preparation completed before late rejection" True =<< readIORef preparedMathematics
            assertEqual "generated consequences were authorized before late rejection" True =<< readIORef authorizedConsequences
            failedPrefix <- case failed of
                Declaration.DriverFailed (Declaration.DriverDeclarationFailed Declaration.DeclarationAuthorizationFrontierIncomplete) prefix -> pure prefix
                _ -> fail "late authorizer rejection did not abort the declaration"
            Commit.pendingModulePrefixCurrent failedPrefix @?= Commit.pendingModulePrefixCurrent priorPrefix
            (Commit.committedBatchDelta <$> Commit.pendingModulePrefixBatches failedPrefix) @?=
                (Commit.committedBatchDelta <$> Commit.pendingModulePrefixBatches priorPrefix)
            reader <- Store.newStoreCheck store
            expectRightIO (Store.writePendingModulePrefix reader failedPrefix)
            consumerWorkspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/reconstruction-import-consumer.tex"
            let consumerParsed = Parsed.parsedWorkspaceRootModule consumerWorkspace
                consumerBlocks = Parsed.parsedModuleBlocks consumerParsed
            (consumer, consumerProof) <- sole "consumer of the rejected construction"
                [(block, proof) | (block@(Raw.BlockClaim _ _ _ (Raw.Marker "imported_clear_result") _), Raw.BlockProof _ proof _)
                    <- zip consumerBlocks (drop 1 consumerBlocks)]
            let consumerOwner = moduleName (Parsed.parsedModuleAddress consumerParsed)
            rejectUse foundation resolver prior consumerOwner consumer consumerProof AlwaysMissValidation
            key <- expectRight (Semantic.moduleArtefactKey owner (Parsed.parsedModuleId parsed)
                (Semantic.semanticInterfaceDirectInputs semantic) (Identity.theoryId foundation))
            pure (prior, consumerOwner, consumer, consumerProof, key,
                Syntax.moduleSyntaxAssertedId (Parsed.parsedModuleSyntaxInterface parsed))
        bracket open Store.closeStore \store -> do
            reader <- Store.newStoreCheck store
            candidate <- expectRightIO (Store.loadCachedModuleCandidate reader key syntax)
            assertBool "failed declaration did not publish a module artefact" (isNothing candidate)
            rejectUse foundation resolver prior consumerOwner consumer consumerProof (storeValidationPolicy reader)
  where
    rejectUse foundation resolver prior owner consumer proof validation = do
        driven <- expectRight =<< runModuleDriver foundation owner [prior] resolver validation
            (Declaration.runProspectiveLoweringDriver do
                anchor <- Declaration.resolveVisibleFactAliasLowering (Semantic.semanticName "imported_anchor")
                pending <- for ["imported_clear", "imported_clearshape", "imported_clearprojection_atlas"]
                    (Declaration.resolveVisibleFactAliasLowering . Semantic.semanticName)
                attempted <- Proof.prepareProof consumer (Just proof)
                pure (anchor, pending, attempted))
        case driven of
            Declaration.DriverSucceeded (Just _, missing, Left Proof.ProofElaborationFailed{}) _ _ ->
                assertBool "no failed consequence alias became visible" (all isNothing missing)
            _ -> fail "consumer acquired failed construction authority or lost the earlier declaration"

readSources :: IO Sources
readSources = do
    let readSource name = Encoding.decodeUtf8 <$> ByteString.readFile ("test/structure-spikes/" <> name <> ".tex")
    schema <- readSource "carrierless-basic"
    base <- Text.replace "test/structure-spikes/carrierless-basic.tex" "schema.tex"
        <$> readSource "reconstruction-import-base"
    producer <- Text.replace "test/structure-spikes/reconstruction-import-base.tex" "base.tex"
        <$> readSource "reconstruction-import-producer"
    consumer <- Text.replace "test/structure-spikes/reconstruction-import-producer.tex" "producer.tex"
        <$> readSource "reconstruction-import-consumer"
    pure (Sources schema base producer consumer)

writeSources :: FilePath -> Sources -> IO ()
writeSources root sources = for_ [("schema.tex", schemaSource sources), ("base.tex", baseSource sources),
        ("producer.tex", producerSource sources), ("consumer.tex", consumerSource sources)] \(path, source) ->
    ByteString.writeFile (root </> path) (Encoding.encodeUtf8 source)

-- Each case starts from an independently populated store and the same source
-- namespace. Fake ATP acceptance exercises routing; deterministic final proof
-- steps reject the invalid changes. The source family is also real-verified.
invalidatesRealizations :: Assertion
invalidatesRealizations = Temp.withSystemTempDirectory "reconstruction-invalidation" \root ->
    withAcceptedFixtureVampire "reconstruction-invalidation-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        mounts <- exactFixtureMounts root
        baseline <- readSources
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            open label = snd <$> (Store.openStore (root </> label <> ".sqlite")
                (Identity.theoryId foundation) >>= expectRight)
            check store source = do
                request <- expectRight (searchedRoot source)
                graph <- expectRightIO (Graph.buildResolvedSourceGraph mounts request)
                requests <- newIORef (0 :: Int)
                result <- expectRightIO (Verification.withVerificationSessionUsingStore store \session ->
                    Verification.checkWorkspace session Verification.CheckRequest
                        { Verification.checkSourceGraph = graph
                        , Verification.checkPresentationDemand = Parse.NoPresentation
                        , Verification.checkStoreValidationMode = Verification.WarmStoreValidation
                        , Verification.checkModuleJobs = testSequentialJobs
                        , Verification.checkProverJobs = testSequentialJobs
                        , Verification.checkVampire = prover
                        , Verification.checkRequestObserver = Verification.verificationRequestObserver
                            (\_ _ -> modifyIORef' requests (+ 1))
                        }) >>= expectRight
                (,) (Verification.checkVerificationResult result) <$> readIORef requests
            snapshot store = do
                prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
                workspace <- parseFinalWorkspace prelude mounts "producer.tex"
                reader <- Store.newStoreCheck store
                modules <- compileParsedWorkspaceWithReadiness foundation (Module.finalPreludeReadiness prelude)
                    resolver (storeValidationPolicy reader) workspace
                sealed <- sole "producer" (take 1 (reverse modules))
                let parsed = Parsed.parsedWorkspaceRootModule workspace
                    semantic = completedModuleSemantic sealed
                key <- expectRight (Semantic.moduleArtefactKey (moduleName (Parsed.parsedModuleAddress parsed))
                    (Parsed.parsedModuleId parsed) (Semantic.semanticInterfaceDirectInputs semantic)
                    (Identity.theoryId foundation))
                cached <- expectRightIO (Store.loadCachedModuleCandidate reader key
                    (Syntax.moduleSyntaxAssertedId (Parsed.parsedModuleSyntaxInterface parsed)))
                    >>= maybe (fail "missing admitted producer artefact") pure
                let admitted = Store.cachedCandidateSemantic cached
                    propositions = Map.fromList [(Identity.storedPropositionCandidateId p,
                        Identity.storedPropositionCandidateTerm p) | p <- Store.cachedCandidatePropositions cached]
                    facts = Map.fromList [(Semantic.semanticFactFingerprint fact, Semantic.semanticFactProposition fact)
                        | delta <- Semantic.semanticInterfaceDeclarations admitted, fact <- Semantic.declarationDeltaFacts delta]
                aliases <- for [alias | delta <- Semantic.semanticInterfaceDeclarations admitted,
                        alias <- Semantic.declarationDeltaAliases delta] \alias -> do
                    target <- maybe (fail "cached public alias lost its proposition") pure
                        (Map.lookup (Semantic.semanticAliasTarget alias) facts >>= (`Map.lookup` propositions))
                    pure (Semantic.semanticNameText (Semantic.semanticAliasName alias), target)
                admitted @?= semantic
                pure (Parsed.parsedModuleId parsed, admitted, Map.fromList aliases)
        for_ [False, True] \closed -> do
            let form = if closed then "closed" else "family"
                edit transform sources = sources {producerSource = modifyForm closed transform (producerSource sources)}
                body = edit (Text.replace "with \\atlas=\\emptyset"
                    (if closed then "with \\atlas=\\{\\emptyset\\}" else "with \\atlas=X"))
                validProof = edit (Text.replace "    Follows." "    Follows by \\obv{emptyset_subseteq}.")
                invalidProof = edit (Text.replace "    Follows." "    $\\emptyset\\in\\emptyset$.\n    Follows.")
            for_ [("body", body, True), ("proof", validProof, True), ("invalid-proof", invalidProof, False)]
                \(label, change, succeeds) -> do
                    writeSources root baseline
                    coldSnapshot <- bracket (open (form <> "-" <> label)) Store.closeStore \store -> do
                        (cold, _) <- check store "consumer.tex"
                        assertTypedSuccess "baseline imported realizations" cold
                        snapshot store
                    bracket (open (form <> "-" <> label)) Store.closeStore \store -> do
                        (warm, requests) <- check store "consumer.tex"
                        assertTypedSuccess "reopened imported realizations" warm
                        requests @?= 0
                        warmSnapshot <- snapshot store
                        warmSnapshot @?= coldSnapshot
                        writeSources root (change baseline)
                        (changed, _) <- check store "producer.tex"
                        if succeeds then assertTypedSuccess label changed else assertRejected label changed
                        when succeeds do
                            changedSnapshot@(changedSource, _, targets) <- snapshot store
                            let (oldSource, _, oldTargets) = coldSnapshot
                            assertBool "the edited proof/body is reconsidered" (changedSource /= oldSource)
                            when (label == "proof") (targets @?= oldTargets)
                            when (label == "body") do
                                let name = if closed then "imported_closed_clear" else "imported_clear"
                                    target alias = maybe (fail "missing changed public theorem") pure (Map.lookup alias targets)
                                resultTarget <- stripEnvelope <$> target name
                                projectionTarget <- stripEnvelope <$> target (name <> "projection_atlas")
                                case (resultTarget, projectionTarget) of
                                    (Core.CApp _ parameter, Core.CEq Core.TySet _ value) -> value @?= parameter
                                    _ -> fail "changed projection/result has an unexpected envelope"
                                assertBool "body edit changes admitted public targets" (changedSnapshot /= coldSnapshot)
                        when (label == "body") do
                            (stale, _) <- check store "consumer.tex"
                            assertRejected "stale projection consumer" stale
                            let updated = change baseline
                            writeSources root updated {consumerSource = updateProjection closed (consumerSource updated)}
                            (current, _) <- check store "consumer.tex"
                            assertTypedSuccess "updated projection consumer" current
                        when (label == "proof") do
                            (consumer, _) <- check store "consumer.tex"
                            assertTypedSuccess "proof-only edit preserves public facts" consumer
        -- Removing the only imported classification invalidates both forms,
        -- including their all-replaced bases, despite unchanged aggregate Core.
        for_ [False, True] \closed -> do
            let initial = onlyForm closed baseline
            writeSources root initial
            bracket (open (if closed then "closed-evidence" else "family-evidence")) Store.closeStore \store -> do
                (cold, _) <- check store "consumer.tex"
                assertTypedSuccess "base evidence baseline" cold
                writeSources root initial {baseSource = fst (Text.breakOn "\\begin{classification}" (baseSource initial))}
                (missing, _) <- check store "producer.tex"
                assertRejected "removed imported base classification" missing
                writeSources root initial
                (restored, _) <- check store "consumer.tex"
                assertTypedSuccess "restored imported base classification" restored
        for_ [False, True] \closed -> do
            let initial = onlyForm closed baseline
                label = if closed then "closed-schema" else "family-schema"
                parameter = if closed then "\\{\\emptyset\\}" else "X"
                subject = if closed then "\\ImportedClosedClear" else "\\ImportedClear{X}"
                strengthened = initial {schemaSource = Text.replace
                    "\\item\\label{coordinate_atlas_bound} $\\atlas[R]\\subseteq X$."
                    ("\\item\\label{coordinate_atlas_bound} $\\atlas[R]\\subseteq X$.\n"
                        <> "        \\item\\label{coordinate_atlas_full} $\\atlas[R]=X$.") (schemaSource initial)}
            writeSources root initial
            bracket (open label) Store.closeStore \store -> do
                (cold, _) <- check store "consumer.tex"
                assertTypedSuccess "schema mutation baseline" cold
                writeSources root strengthened
                (missingLaw, _) <- check store "producer.tex"
                assertRejected "new schema law needs a proof" missingLaw
                let repaired = strengthened
                        { producerSource = Text.replace "with \\atlas=\\emptyset" ("with \\atlas=" <> parameter)
                            (Text.replace "    Follows."
                                ("    $\\atlas[" <> subject <> "]=" <> parameter
                                    <> "$ by \\obv{coordinate_recordaggregateprojection_atlas}.\n    Follows.")
                                (producerSource strengthened))
                        , consumerSource = updateProjection closed (consumerSource strengthened)
                        }
                writeSources root repaired
                (provedLaw, _) <- check store "consumer.tex"
                assertTypedSuccess "new schema law with its proof" provedLaw
        -- A changed result application must not be hidden by unchanged atlas
        -- values or by the provider's erased, constant mathematical body.
        let initial = onlyForm False baseline
            changed = initial {producerSource = Text.replace "on X based on" "on \\pow{X} based on"
                (Text.replace "on $X$" "on $\\pow{X}$"
                    (Text.replace "\\subseteq X" "\\subseteq\\pow{X}" (producerSource initial)))}
        writeSources root initial
        bracket (open "result-parameter") Store.closeStore \store -> do
            (cold, _) <- check store "consumer.tex"
            assertTypedSuccess "result parameter baseline" cold
            (_, oldSemantic, _) <- snapshot store
            writeSources root changed
            (newProducer, _) <- check store "producer.tex"
            assertTypedSuccess "changed result parameter" newProducer
            (_, newSemantic, _) <- snapshot store
            let registrations = concatMap (\entry -> [rule | Semantic.Registration _ _ (Semantic.RegisterProviderResult rule) <- Semantic.declarationDeltaRegistrations entry]) . Semantic.semanticInterfaceDeclarations
            assertBool "result registration retains the new parameter template"
                (registrations newSemantic /= registrations oldSemantic)
            rule <- sole "changed construction registration" (registrations newSemantic)
            case Semantic.providerResultConclusion rule of
                Semantic.StructureAtomTemplate _ arguments -> case Vector.toList arguments of
                    [Semantic.ResultRuleProviderValue, Semantic.ResultRuleTerm (Semantic.TemplateProvider _ parameters)] ->
                        Vector.toList parameters @?= [Semantic.TemplateVariable (Semantic.ViewVariableIx 0)]
                    _ -> fail "the changed result parameter was erased from its registration"
                _ -> fail "the changed construction lost its structure result"
            (stale, _) <- check store "consumer.tex"
            assertRejected "stale result-parameter consumer" stale
            let updatedConsumer = Text.replace "on $X$" "on $\\pow{X}$"
                    (Text.replace "on X" "on \\pow{X}" (consumerSource changed))
            writeSources root changed {consumerSource = updatedConsumer}
            (current, _) <- check store "consumer.tex"
            assertTypedSuccess "updated result-parameter consumer" current

modifyForm :: Bool -> (Text -> Text) -> Text -> Text
modifyForm closed transform source =
    let (family, instance') = Text.breakOn "\\begin{instance}" source
    in if closed then family <> transform instance' else transform family <> instance'

closedConsumerMarker :: Text
closedConsumerMarker = "\\begin{proposition}\\label{imported_closed_result}"

onlyForm :: Bool -> Sources -> Sources
onlyForm closed sources = sources
    { producerSource = if closed then "\\import{base.tex}\n\n" <> instance' else family
    , consumerSource = if closed then "\\import{producer.tex}\n\n" <> closedConsumer else familyConsumer
    }
  where
    (family, instance') = Text.breakOn "\\begin{instance}" (producerSource sources)
    (familyConsumer, closedConsumer) = Text.breakOn closedConsumerMarker (consumerSource sources)

updateProjection :: Bool -> Text -> Text
updateProjection closed source =
    let (family, instance') = Text.breakOn closedConsumerMarker source
        parameter = if closed then "\\{\\emptyset\\}" else "X"
        update = Text.replace "]=\\emptyset" ("]=" <> parameter)
            . Text.replace "\\atlas=\\emptyset" ("\\atlas=" <> parameter)
    in if closed then family <> update instance' else update family <> instance'

assertRejected :: String -> Verification.VerificationResult -> Assertion
assertRejected label = \case
    Verification.VerificationFailure{} -> pure ()
    Verification.VerificationCheckingFailure{} -> pure ()
    result -> assertFailure (label <> " unexpectedly admitted: " <> show result)

stripEnvelope :: Core.CanonicalTerm Identity.ObjectId -> Core.CanonicalTerm Identity.ObjectId
stripEnvelope = \case
    Core.CForall _ body -> stripEnvelope body
    Core.CImp _ body -> stripEnvelope body
    body -> body
