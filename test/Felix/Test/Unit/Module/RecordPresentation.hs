{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Test.Unit.Module.RecordPresentation (tests) where

import Base
import Felix.Checking.Declaration qualified as Declaration
import Felix.Checking.Foundation qualified as Foundation
import Felix.Checking.Identity qualified as Identity
import Felix.Checking.Module qualified as Module
import Felix.Checking.Semantic qualified as Semantic
import Felix.Checking.Structure.Schema qualified as Schema
import Felix.Parse qualified as Parse
import Felix.Parsed.Module qualified as Parsed
import Felix.Parsed.Workspace qualified as Parsed
import Felix.Provers qualified as Provers
import Felix.Render.Html.Consequences qualified as Consequences
import Felix.Render.Html.Export qualified as Export
import Felix.Render.Html.Output qualified as Output
import Felix.Source
import Felix.Source.Graph qualified as Graph
import Felix.Store qualified as Store
import Felix.Syntax.Abstract qualified as Raw
import Felix.Test.Unit.Module.Support
import Felix.Verification qualified as Verification
import Felix.Workspace qualified as Workspace
import Control.Exception (bracket)
import Data.ByteString qualified as ByteString
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Encoding
import System.Directory (getCurrentDirectory)
import System.FilePath.Posix ((</>))
import System.IO.Temp qualified as Temp
import Test.Tasty
import Test.Tasty.HUnit

tests :: [TestTree]
tests =
    [ testCase "renders admitted conditional record consequences after warm reopening" rendersRecordConsequences
    , testCase "renders exact record headers inside logical bundles" rendersExactHeaders
    , testCase "renders checked closed schema parameters" rendersClosedParameters
    ]

rendersClosedParameters :: Assertion
rendersClosedParameters = Temp.withSystemTempDirectory "record-closed-parameters" \root ->
    withAcceptedFixtureVampire "record-closed-parameters-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        cwd <- getCurrentDirectory
        mounts <- exactFixtureMounts cwd
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        bracket (snd <$> (Store.openStore (root </> "store.sqlite") (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore \store -> do
                prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
                workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/closed-value-instances.tex"
                sealed <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
                entries <- expectRight (Consequences.checkedRecordConsequences [Module.finalPreludeModule prelude]
                    (zip (Module.completedTypedModuleSealed <$> sealed) (Parsed.parsedModuleBlocks <$> toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))))
                let parameter label = do
                        family <- maybe (fail "missing closed-parameter consequence") pure (Map.lookup label entries)
                        result <- sole "public result" [entry | entry <- family, Consequences.consequenceLabel entry == label]
                        case Consequences.consequenceConclusion result of
                            Consequences.ConsequenceStructure _ _ [value] -> pure value
                            _ -> fail "the displayed result lost its schema parameter"
                zero <- parameter "closed_value_zero"
                parameter "closed_value_two" >>= \case
                    Consequences.ConsequenceGlobal _ "suc" [Consequences.ConsequenceGlobal _ "suc" [base]] -> base @?= zero
                    _ -> fail "the displayed numeral lost its checked successor representation"
                parameter "closed_value_comprehension" >>= \case
                    Consequences.ConsequenceSeparation{} -> pure ()
                    _ -> fail "a closed comprehension lost its internal binder"

rendersExactHeaders :: Assertion
rendersExactHeaders = Temp.withSystemTempDirectory "record-exact-header" \root ->
    withAcceptedFixtureVampire "record-exact-header-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        cwd <- getCurrentDirectory
        mounts <- exactFixtureMounts cwd
        let resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
        bracket (snd <$> (Store.openStore (root </> "store.sqlite") (Identity.theoryId foundation) >>= expectRight))
            Store.closeStore \store -> do
                prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
                workspace <- parseFinalWorkspace prelude mounts "test/structure-spikes/construction-classification-bundle.tex"
                sealed <- compileFinalParsedWorkspaceWithResolver foundation prelude resolver workspace
                entries <- expectRight (Consequences.checkedRecordConsequences [Module.finalPreludeModule prelude]
                    (zip (Module.completedTypedModuleSealed <$> sealed) (Parsed.parsedModuleBlocks <$> toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace))))
                family <- maybe (fail "missing exact-header construction") pure (Map.lookup "copy_classified_coordinate" entries)
                assertBool "all public consequences retain the exact-shape conjunct"
                    (not (null family) && all (any containsShape . Consequences.consequenceHeaders) family)
  where
    containsShape (Consequences.ConsequenceExactFields [_] _) = True
    containsShape (Consequences.ConsequenceBinary _ left right) = containsShape left || containsShape right
    containsShape _ = False

rendersRecordConsequences :: Assertion
rendersRecordConsequences = Temp.withSystemTempDirectory "record-consequence-presentation" \root ->
    withAcceptedFixtureVampire "record-presentation-prover" \prover -> do
        foundation <- expectRight Foundation.checkedFoundation
        cwd <- getCurrentDirectory
        mounts <- exactFixtureMounts cwd
        environment <- expectRightIO Workspace.prepareDefaultWorkspaceEnvironment
        hints <- Encoding.decodeUtf8 <$> ByteString.readFile (cwd </> "library/lexicon.tsv")
        let source = "test/structure-spikes/manifolds-0-projection-collision.tex"
            open = snd <$> (Store.openStore (root </> "store.sqlite") (Identity.theoryId foundation) >>= expectRight)
            resolver = Declaration.vampireResolver (Provers.runPreparedTypedProver prover)
            check store = do
                requests <- newIORef (0 :: Int)
                (result, _) <- expectRightIO (checkFileWithStore store Verification.WarmStoreValidation
                    (Verification.verificationRequestObserver (\_ _ -> modifyIORef' requests (+ 1))) prover source)
                assertTypedSuccess "record presentation source" result
                readIORef requests
            snapshot store output = do
                prelude <- expectRightIO (acquireFinalPreludeSession store foundation resolver)
                request <- expectRight (searchedRoot source)
                graph <- expectRightIO (Graph.buildResolvedSourceGraph mounts request)
                execution <- expectRightIO (Parse.parseResolvedSourceGraphExecution (Parse.PersistentParsedArtefacts store)
                    Parse.HtmlPresentationRequested graph (const [Module.sealedTypedModuleSyntax (Module.finalPreludeModule prelude)])
                    (const (Right ())))
                presentation <- case Parse.parseExecutionPresentation execution of
                    Parse.ParseWithPresentation entries -> pure entries
                    _ -> fail "checked HTML lost source presentation"
                let workspace = Parse.parseExecutionWorkspace execution
                    parsed = toList (Parsed.parsedWorkspaceImportedBeforeImporter workspace)
                reader <- Store.newStoreCheck store
                sealed <- compileParsedWorkspaceWithReadiness foundation (Module.finalPreludeReadiness prelude)
                    resolver (storeValidationPolicy reader) workspace
                let associated = zip (Module.completedTypedModuleSealed <$> sealed) (Parsed.parsedModuleBlocks <$> parsed)
                entries <- expectRight (Consequences.checkedRecordConsequences [Module.finalPreludeModule prelude] associated)
                -- Every displayed item retains the exact target of the
                -- admitted alias, not an equation reconstructed from source.
                for_ (concat (Map.elems entries)) \entry -> do
                    target <- sole "admitted consequence target"
                        [target
                        | module' <- sealed
                        , delta <- Semantic.semanticInterfaceDeclarations (completedModuleSemantic module')
                        , alias <- Semantic.declarationDeltaAliases delta
                        , Raw.Marker (Semantic.semanticNameText (Semantic.semanticAliasName alias)) == Consequences.consequenceLabel entry
                        , target <- maybeToList (Declaration.evidenceFactTarget (completedModuleEvidence module')
                            (Semantic.semanticAliasTarget alias))]
                    Consequences.consequenceTarget entry @?= target
                checked <- expectRight (Export.htmlPresentationFromCheckedWorkspace (Module.finalPreludeModule prelude)
                    (Map.fromList (zip (Parsed.parsedModuleAddress <$> parsed) (Module.completedTypedModuleSealed <$> sealed))) workspace presentation)
                prepared <- expectRight (Export.prepareHtmlExport (Workspace.workspaceHtmlMountPrefixes environment) checked hints)
                plan <- expectRightIO (Output.planHtmlOutput output (Export.preparedHtmlExportArtefacts prepared))
                void (expectRightIO (Output.writeHtmlOutput plan))
                page <- Encoding.decodeUtf8 <$> ByteString.readFile (output </> "test/structure-spikes/manifolds-0.html")
                imported <- Encoding.decodeUtf8 <$> ByteString.readFile (output </> "test/structure-spikes/manifolds-0-projection-collision.html")
                raw <- expectRight (Export.htmlPresentationFromParsedWorkspaceWithSyntaxInputs
                    (const [Module.sealedTypedModuleSyntax (Module.finalPreludeModule prelude)]) workspace presentation)
                rawPrepared <- expectRight (Export.prepareHtmlExport (Workspace.workspaceHtmlMountPrefixes environment) raw hints)
                rawPlan <- expectRightIO (Output.planHtmlOutput (output <> "-raw") (Export.preparedHtmlExportArtefacts rawPrepared))
                void (expectRightIO (Output.writeHtmlOutput rawPlan))
                rawPage <- Encoding.decodeUtf8 <$> ByteString.readFile (output <> "-raw" </> "test/structure-spikes/manifolds-0.html")
                assertBool "parse-only source has no checked consequence disclosure"
                    (not ("<summary>Public consequences</summary>" `Text.isInfixOf` rawPage))
                pure (entries, page, imported)
        cold@(entries, page, imported) <- bracket open Store.closeStore \store -> do
            void (check store)
            snapshot store (root </> "cold")
        bracket open Store.closeStore \store -> do
            assertEqual "warm module admission uses no new ATP requests" 0 =<< check store
            warm <- snapshot store (root </> "warm")
            warm @?= cold
        equip <- maybe (fail "missing Equip consequence family") pure (Map.lookup "equip" entries)
        projection <- sole "conditional atlas projection"
            [entry | entry <- equip, Consequences.consequenceLabel entry == "equipprojection_atlas"]
        length (Consequences.consequenceBinders projection) @?= 2
        length (Consequences.consequenceHeaders projection) @?= 2
        case (Consequences.consequenceBinders projection, Consequences.consequenceHeaders projection) of
            ([x, a], [Consequences.ConsequenceStructure _ (Consequences.ConsequenceVariable actualX) [],
                Consequences.ConsequenceGlobal _ "admissible_atlas"
                    [Consequences.ConsequenceVariable actualA, Consequences.ConsequenceVariable parameterX]]) -> do
                        actualX @?= x
                        parameterX @?= x
                        actualA @?= a
            _ -> fail "the displayed projection lost or permuted its complete header"
        case Consequences.consequenceConclusion projection of
            Consequences.ConsequenceBinary "="
                (Consequences.ConsequenceField (Raw.StructSymbol "atlas")
                    (Consequences.ConsequenceGlobal _ "equip" left))
                (Consequences.ConsequenceField (Raw.StructSymbol "atlas")
                    (Consequences.ConsequenceGlobal _ "generated_coordinate_structure" right)) ->
                        left @?= right
            _ -> fail "the displayed conditional projection changed its admitted right-hand side"
        for_ equip \entry -> case Consequences.consequenceLabel entry of
            "equip" -> case Consequences.consequenceConclusion entry of
                Consequences.ConsequenceStructure phrase _ _ ->
                    Schema.structurePhraseMarker phrase @?= "equipped_coordinate_space"
                _ -> fail "the result theorem is not the mathematical schema predicate"
            "equipshape" -> case Consequences.consequenceConclusion entry of
                Consequences.ConsequenceExactFields roles _ -> length roles @?= 3
                _ -> fail "shape was confused with mathematical laws"
            _ -> pure ()
        for_ ["For all sets", "admissible", "has exactly the fields", "equipprojection_atlas"] \fragment ->
            assertBool ("missing consequence content: " <> Text.unpack fragment) (fragment `Text.isInfixOf` page)
        assertBool "imported conditional projection has a citation preview"
            ("data-reference-label=\"equipprojection_atlas\"" `Text.isInfixOf` imported
                && "GeneratedCoordinateStructure" `Text.isInfixOf` imported
                && "For all sets" `Text.isInfixOf` imported)
        assertBool "public consequences do not expose internal selector identities"
            (not ("ObjectId" `Text.isInfixOf` page))
