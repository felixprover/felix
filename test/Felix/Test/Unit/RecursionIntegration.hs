{-# LANGUAGE NoImplicitPrelude #-}
module Felix.Test.Unit.RecursionIntegration (tests) where
import Base hiding (Empty)
import Control.Monad (unless, when)
import Felix.Cache.Codec
import Felix.Checking.Commit qualified as Commit
import Felix.Checking.Notion.SourceEvidence qualified as Source
import Felix.Test.Support.Imports (admitTestModule)
import System.IO.Temp qualified as Temp
import System.Directory (getCurrentDirectory)
import Felix.Parse qualified as Parse
import Felix.Parsed.Workspace qualified as Parsed
import System.FilePath ((</>))
import Test.Tasty
import Test.Tasty.HUnit
import Data.Text.IO qualified as TextIO
import Data.List.NonEmpty qualified as NonEmpty
import Felix.Checking.Declaration qualified as D
import Felix.Checking.Foundation qualified as F
import Felix.Checking.Identity qualified as I
import Felix.Checking.Core
import Felix.Checking.Module qualified as M
import Felix.Checking.Semantic qualified as S
import Felix.Checking.Recursion qualified as R
import Felix.Checking.Recursion.Library qualified as L
import Felix.Checking.Recursion.Construction qualified as C
import Felix.Checking.Proof qualified as Proof
import Felix.Checking.Preparation qualified as Preparation
import Felix.Checking.Datatype.Construction qualified as T
import Felix.Store qualified as Store
import Felix.Test.Unit.Module.Support
import Felix.Module
import Felix.Source
import Felix.Report.Location
import Felix.Math.Codec (hashBlake2b256)
import Felix.Syntax.Abstract qualified as Raw
import Data.List qualified as List
import Data.Text qualified as Text
import Data.Vector qualified as Vector

tests :: TestTree
tests = testGroup "Recursive declarations"
    [ testCase "checks source recursion and its formation boundary" sourceRecursion
    , testCase "publishes binding-owned recursion with actual checked library support" normalizedRecursion
    ]

normalizedRecursion :: Assertion
normalizedRecursion =
    Temp.withSystemTempDirectory "felix-recursion" \directory -> do
        TextIO.writeFile (directory </> "recursion-datatype.tex") (Text.unlines
            [ "\\import{recursion/well-founded-relation.tex}"
            , "\\begin{datatype}\\label{probe_tree}"
            , "Define $\\probetree$ inductively as follows."
            , "\\begin{enumerate}"
            , "\\item[Zero] $\\probezero\\in\\probetree$."
            , "\\item[Successor] $\\probesucc{x}\\in\\probetree$ for $x\\in\\probetree$."
            , "\\item[Witness] $\\probehidden{x}\\in\\probetree$ for $x\\in\\probetree$ and $w\\in\\probetree$."
            , "\\end{enumerate}"
            , "\\end{datatype}"
            , "\\begin{datatype}\\label{probe_witness_data}"
            , "Define $\\probewitness{A}$ inductively as follows."
            , "\\begin{enumerate}"
            , "\\item[Zero] $\\probewitnesszero\\in\\probewitness{A}$."
            , "\\item[Node] $\\probewitnessnode{x}\\in\\probewitness{A}$ for $x\\in\\probewitness{A}$ and $w\\in A$."
            , "\\end{enumerate}"
            , "\\end{datatype}" ])
        publication directory

publication :: FilePath -> Assertion
publication directory = do
    foundation <- expectRight F.checkedFoundation
    plan <- expectRightIO (Store.planStore (Store.ExplicitStore (directory </> "proofs.sqlite")))
    withTestStoreLease plan \lease -> do
      result <- Store.withOpenStore lease (I.theoryId foundation) \_ store -> do
        prelude <- expectRightIO (acquireFinalPreludeSession store foundation finalPreludeResolver)
        storeCheck <- Store.newStoreCheck store
        mounts <- exactFixtureMounts directory
        workspace <- parseFinalWorkspace prelude mounts "recursion-datatype.tex"
        modules <- compileParsedWorkspaceWithReadiness foundation (M.finalPreludeReadiness prelude)
            finalPreludeResolver (storeValidationPolicy storeCheck) workspace
        for_ modules (expectRightIO . Store.writePendingModulePrefix storeCheck . M.completedTypedModulePrefix)
        root <- maybe (fail "no datatype module") pure (listToMaybe (reverse modules))
        let bindings = concatMap (S.semanticEnvironmentBindings . S.declarationDeltaEnvironment)
                (S.semanticInterfaceDeclarations (completedModuleSemantic root))
        datatype <- maybe (fail "no checked datatype") pure (List.find (isJust . S.semanticGlobalBindingDatatype) bindings)
        witnessDatatype <- maybe (fail "no checked witness datatype") pure (List.find
            (\binding -> case S.semanticGlobalBindingKey binding of
                S.SemanticExpressionFunction (Raw.TokenCons (Raw.Command "probewitness") _) -> True
                _ -> False) bindings)
        relative <- expectRight (safeRelativePath "recursion-owner.tex")
        let owner = moduleNameFromParts (sourceNamespaceIdFromDigest (hashBlake2b256 "recursion-owner")) relative
            symbol = Raw.mkMixfixItem [Just (Raw.Command "probeeval"),Nothing] (Raw.Marker "probe_eval") Raw.NonAssoc
            key = S.SemanticExpressionFunction (Raw.mixfixPattern symbol)
            action :: D.ModuleDriver Text ()
            action = for_ [("probeeval",TySet,[]), ("probeother",TySet,[S.ResidualTemplate CFalsum]),
                ("probeprop",TyProp,[]), ("probeidentity",TySet,[]), ("probebinder",TyProp,[]),
                ("probeconstant",TySet,[]), ("probewitnesseval",TySet,[]), ("probeexpose",TySet,[])] \(name,resultType,headers) -> do
                let parameterCount = if resultType == TyProp || name `elem` ["probewitnesseval","probeexpose"] then 1 else 0
                    selectedDatatype = if name == "probewitnesseval" then witnessDatatype else datatype
                    selectedSymbol = Raw.mkMixfixItem (Just (Raw.Command name) : replicate (parameterCount + 1) Nothing) (Raw.Marker name) Raw.NonAssoc
                    selectedKey = if resultType == TySet then S.SemanticExpressionFunction (Raw.mixfixPattern selectedSymbol)
                        else S.SemanticPrefixPredicate name 2
                prepared <- D.runProspectiveLoweringDriver do
                    resolved <- D.resolveVisibleGlobalLowering (S.semanticGlobalBindingKey selectedDatatype)
                    case resolved of
                        Nothing -> pure (Left "datatype not visible")
                        Just (binding,_) -> L.loadCheckedDatatype binding >>= \case
                            Left failure -> pure (Left failure)
                            Right loaded -> do
                                closure <- D.checkedObjectClosureLowering
                                -- Reveal a guarded call only after one public equation,
                                -- so its missing witness is tested by evaluation rather
                                -- than rejected by the original source's formation check.
                                exposed <- if name /= "probeexpose" then pure Nothing else do
                                    let witnessDescription = fromMaybe (impossible "missing witness datatype")
                                            (S.semanticGlobalBindingDatatype witnessDatatype)
                                        keys = S.SemanticExpressionFunction (Raw.mixfixPattern (Raw.mkMixfixItem
                                            [Just (Raw.Command "probewitnesseval"),Nothing,Nothing]
                                            (Raw.Marker "probewitnesseval") Raw.NonAssoc)) :
                                            (S.datatypeCaseConstructor <$> toList (S.datatypeDescriptorCases witnessDescription))
                                    objects <- for keys \entry -> D.resolveVisibleGlobalLowering entry >>= \case
                                        Just (exposedBinding,_) -> pure (S.semanticGlobalTargetObject
                                            (S.semanticGlobalBindingTarget (S.resolvedBindingDeclaration exposedBinding)))
                                        Nothing -> impossible "an exposed fixture binding is unavailable"
                                    case objects of
                                        [function,zero,node] -> pure (Just (function,zero,node))
                                        _ -> impossible "witness fixture constructor order changed"
                                let descriptor = fromMaybe (impossible "fixture datatype descriptor disappeared")
                                        (S.semanticGlobalBindingDatatype selectedDatatype)
                                    branch (clause,constructorDescription) =
                                        let recursive = length (C.recursiveSlots clause)
                                            types = replicate (length (T.clauseArgumentSlots clause)) TySet <> replicate recursive resultType
                                            value = case exposed of
                                              Just (function,zero,node) -> CApp (CApp (CGlobal function) (CBound (fromIntegral (length types))))
                                                  (CApp (CGlobal node) (CGlobal zero))
                                              Nothing -> if name == "probeconstant" || name == "probewitnesseval" then CIntrinsic Empty
                                                  else if name == "probeidentity"
                                                  then foldl' CApp (CGlobal (T.clauseConstructor clause)) [CBound 0 | recursive > 0]
                                                  else if resultType == TyProp
                                                  then if recursive == 0 then CApp (CApp (CIntrinsic Member) (CIntrinsic Empty)) (CBound 0)
                                                      else if name == "probebinder" then CNot (CForall TySet (CNot (CBound 1)))
                                                      else CNot (CBound 0)
                                                  else if recursive == 0 then CIntrinsic Empty
                                                      else CApp (CApp (CIntrinsic PairSet) (CBound 0)) (CBound 0)
                                            description = if name == "probeidentity" then S.TermExpansion
                                                (S.ExpansionProvider (S.GlobalSourceProvider (S.globalBindingRef
                                                    (S.globalBindingRefOwner (S.resolvedBindingRef binding)) (S.datatypeCaseConstructor constructorDescription)))
                                                    (Vector.fromList [S.ExpansionFormal 1 | recursive > 0]))
                                                else if resultType == TySet then S.TermExpansion (S.ExpansionOpaque value)
                                                else S.PropositionExpansion (Source.SourceResidual Nothing) []
                                        in (\checked -> (checked,description)) <$> checkScopedCanonicalCore (I.globalTypingFromClosure closure)
                                            (replicate parameterCount TySet) (foldr CLam value types)
                                case traverse branch (NonEmpty.zip (L.loadedDatatypeClauses loaded) (S.datatypeDescriptorCases descriptor)) of
                                    Left failure -> pure (Left (Text.pack (show failure)))
                                    Right branches -> R.lowerRecursiveDefinition (R.RecursiveDefinitionInput
                                        name selectedKey (S.semanticBindingLabel name) binding
                                            [0 | name == "probewitnesseval"] headers branches)
                declaration <- either D.failModuleDriver pure prepared
                void (D.admitCheckedDeclaration declaration R.authorizeCheckedRecursion)
        published <- runModuleDriver foundation owner [completedModuleEvidence root]
            unusedResolver AlwaysMissValidation action
        (evidence,prefix) <- case published of
            Right (D.DriverSucceeded () evidence prefix) -> do
                expectRightIO (Store.writePendingModulePrefix storeCheck prefix)
                pure (evidence,prefix)
            Right (D.DriverFailed failure _) -> fail (show failure)
            Right (D.DriverSealFailed failure _) -> fail (show failure)
            Left failure -> fail (show failure)
        consumerFile <- expectRight (safeRelativePath "recursion-consumer.tex")
        let consumer = moduleNameFromParts (sourceNamespaceIdFromDigest (hashBlake2b256 "recursion-owner")) consumerFile
        let inspect :: D.ModuleDriver Text ()
            inspect = do
                families <- D.runProspectiveLoweringDriver do
                    found <- D.resolveVisibleGlobalLowering key
                    case found of
                        Nothing -> pure []
                        Just (binding,_) -> D.resolveVisibleRecursiveDefinitionsLowering
                            (S.semanticGlobalTargetObject (S.semanticGlobalBindingTarget (S.resolvedBindingDeclaration binding)))
                unless (length families == 2) (D.failModuleDriver "Set body sharing lost one owned family")
                for_ [1,2,3] \depth -> proveSource (sourceClaim False depth)
                traverse_ proveSource (nestedClaims datatype)
                proveSource (witnessClaim witnessDatatype)
                proveSource (exposedWitnessClaim datatype True)
                proveSourceWith Raw.JustificationImplicit True (factAuditClaim datatype True)
            -- This is the source proof path. Only the recursive declaration
            -- itself uses normalized input until its grammar lands.
            sourceClaim :: Bool -> Int -> Raw.Block
            sourceClaim reflexive depth = Raw.BlockClaim Raw.Proposition Nowhere Nothing
                (Raw.Marker ("probe_source_equation_" <> Text.pack (show depth))) (Raw.Claim [] statement)
              where
                variable = Raw.NamedVar "x"
                expression = fixtureExpression datatype
                x = Raw.ExprVar variable
                successor term = expression "probesucc" [term]
                argument = if depth == 2 then successor x else x
                value = expression "probeeval" [argument]
                pair = fixturePair
                equation = Raw.FormulaChain (Raw.ChainBase
                    ((if reflexive then value else expression "probeeval"
                        [if depth == 3 then expression "probehidden" [argument] else successor argument]) :| [])
                    Raw.Positive (Raw.Relation Nowhere Raw.EqSymbol [])
                    ((if reflexive then value else pair value value) :| []))
                body = if depth == 3 then Raw.Connected Nowhere Raw.Implication
                    (Raw.FormulaChain (Raw.ChainBase (expression "probehidden" [x] :| []) Raw.Positive
                        (Raw.Relation Nowhere Raw.ElementSymbol []) (expression "probetree" [] :| []))) equation
                    else equation
                statement = Raw.StmtFormula (Raw.FormulaQuantified Nowhere Raw.Universally (variable :| [])
                    (Raw.Bounded Nowhere Raw.Positive (Raw.Relation Nowhere Raw.ElementSymbol []) (expression "probetree" [])) body)
            proveSource = proveSourceWith Raw.JustificationDefinition False
            proveSourceWith method initialOnly claim = do
                prepared <- D.runProspectiveLoweringDriver (Proof.prepareProof claim
                    (Just (Raw.Qed Nothing method)))
                    >>= either (D.failModuleDriver . Text.pack . show) pure
                when (initialOnly && not (null (Proof.preparedProofPreparationStatistics prepared)))
                    (D.failModuleDriver "an ordinary proof started recursive preparation")
                lowered <- D.runProspectiveLoweringDriver (Proof.lowerPreparedProof prepared)
                    >>= either (D.failModuleDriver . Text.pack . show) pure
                void (D.admitCheckedDeclaration lowered Proof.authorizeCheckedProof)
        imported <- runModuleDriver foundation consumer [evidence] unusedResolver (storeValidationPolicy storeCheck) inspect
        coldPrefix <- case imported of
            Right (D.DriverSucceeded () _ completed) -> do
                expectRightIO (Store.writePendingModulePrefix storeCheck completed)
                pure completed
            Right (D.DriverFailed failure _) -> fail (show failure)
            Right (D.DriverSealFailed failure _) -> fail (show failure)
            Left failure -> fail (show failure)
        unusedDefinition <- runModuleDriver foundation consumer [evidence] unusedResolver AlwaysMissValidation
            (proveSource (sourceClaim True 1))
        case unusedDefinition of
            Right (D.DriverFailed (D.DriverDeclarationFailed D.KernelDefinitionEvidenceMissing) _) -> pure ()
            other -> assertFailure ("a reflexive proof acquired definition authority: " <> showDriver other)
        unusedFact <- runModuleDriver foundation consumer [evidence] unusedResolver AlwaysMissValidation
            (proveSource (factAuditClaim datatype False))
        case unusedFact of
            Right (D.DriverFailed (D.DriverDeclarationFailed D.KernelDefinitionEvidenceMissing) _) -> pure ()
            other -> assertFailure ("an unused transformed fact acquired definition authority: " <> showDriver other)
        for_ [("sibling scope",scopeGuardClaim datatype True),("variable scrutinee",scopeGuardClaim datatype False),("missing witness",exposedWitnessClaim datatype False)] \(label,claim) -> do
            blocked <- runModuleDriver foundation consumer [evidence] unusedResolver AlwaysMissValidation (proveSource claim)
            case blocked of
                Right (D.DriverFailed (D.DriverActionFailed failure) _) | "ProofObviousInferenceReported" `Text.isInfixOf` failure -> pure ()
                other -> assertFailure ("a blocked " <> label <> " changed behavior: " <> showDriver other)
        reused <- runModuleDriver foundation consumer [evidence] unusedResolver AlwaysMissValidation
            (proveSource (reuseClaim datatype))
        case reused of
            Right (D.DriverFailed (D.DriverActionFailed failure) _)
                | "recursive guards queried: 1; applications reused: 1" `Text.isInfixOf` failure
                , "Obvious phase 4" `Text.isInfixOf` failure -> pure ()
            other -> assertFailure ("completed application reuse or phase accounting was lost: " <> showDriver other)
        -- Give two different siblings only the preparation work of one
        -- completed base equation. An opening must not reset that account.
        measured <- runModuleDriver foundation consumer [evidence] unusedResolver AlwaysMissValidation do
            prepared <- D.runProspectiveLoweringDriver (Proof.prepareProof (budgetClaim datatype False)
                (Just (Raw.Qed Nothing Raw.JustificationDefinition)))
                >>= either (D.failModuleDriver . Text.pack . show) pure
            pure (sum (Preparation.preparationUsedWork . snd <$> Proof.preparedProofPreparationStatistics prepared))
        budget <- case measured of
            Right (D.DriverSucceeded work _ _) -> pure work
            other -> fail (showDriver other)
        limited <- runModuleDriver foundation consumer [evidence] unusedResolver AlwaysMissValidation do
            result <- D.runProspectiveLoweringDriver (Proof.prepareProofWithPreparationWork budget (budgetClaim datatype True)
                (Just (Raw.Qed Nothing Raw.JustificationDefinition)))
            either (D.failModuleDriver . Text.pack . show) (const (pure ())) result
        case limited of
            Right (D.DriverFailed (D.DriverActionFailed failure) _)
                | "automatic local-evidence preparation exhausted" `Text.isInfixOf` failure
                , "Obvious phase 3" `Text.isInfixOf` failure
                , not ("Obvious phase 4" `Text.isInfixOf` failure) -> pure ()
            other -> assertFailure ("prepared siblings restarted their work allowance: " <> showDriver other)
        let batches = Commit.pendingModulePrefixBatches prefix
            deltas = Commit.committedBatchDelta <$> batches
            objects = concatMap Commit.committedBatchObjects batches
            propositions = concatMap Commit.committedBatchPropositions batches
            certificates = concatMap Commit.committedBatchValidationCertificates batches
        assertBool "raw implementations have no automatic definition views"
            (all (null . S.declarationDeltaDefinitionViews) deltas)
        interface <- expectRight (S.semanticInterface owner
            [S.semanticInterfaceAssertedId (completedModuleSemantic root)] deltas)
        decoded <- expectRight (decodeCache S.getSemanticInterfaceCache (encodeCache (S.putSemanticInterfaceCache interface)))
        admitted <- expectRightIO (admitTestModule (I.theoryId foundation) [completedModuleEvidence root]
            decoded objects propositions certificates)
        importedDecoded <- runModuleDriver foundation consumer [admitted] unusedResolver (storeValidationPolicy storeCheck) inspect
        case importedDecoded of
            Right (D.DriverSucceeded () _ completed) ->
                assertEqual "cold and warm source proofs have the same declaration identity"
                    (Commit.pendingModulePrefixCurrent coldPrefix) (Commit.pendingModulePrefixCurrent completed)
            other -> assertFailure (showDriver other)
        corrupted <- traverse corrupt deltas >>= expectRight . S.semanticInterface owner (S.semanticInterfaceDirectInputs interface)
        rejected <- admitTestModule (I.theoryId foundation) [completedModuleEvidence root]
            corrupted objects propositions certificates
        case rejected of
            Left D.BindingConstructionInvalid{} -> pure ()
            Left failure -> assertFailure ("wrong rejection: " <> show failure)
            Right _ -> assertFailure "a swapped equation association survived import"
      void (expectRight result)
  where
    showDriver = \case
        Left failure -> show failure
        Right (D.DriverFailed failure _) -> show failure
        Right (D.DriverSealFailed failure _) -> show failure
        Right D.DriverSucceeded{} -> "unexpected success"
    corrupt delta = do
        environment <- expectRight (S.semanticEnvironmentDelta
            (change <$> S.semanticEnvironmentBindings (S.declarationDeltaEnvironment delta)))
        expectRight (S.declarationInterfaceDelta (S.declarationDeltaSlot delta) (S.declarationDeltaFacts delta)
            (S.declarationDeltaAliases delta) (S.declarationDeltaObjects delta) (S.declarationDeltaPropositions delta)
            (S.declarationDeltaDefinitionViews delta) (S.declarationDeltaRegistrations delta) environment)
    change binding = case S.semanticGlobalBindingRecursion binding of
        Nothing -> binding
        Just descriptor -> S.withSemanticConstruction (S.RecursiveConstruction descriptor
            { S.recursiveDefinitionEquations = NonEmpty.zip (fst <$> S.recursiveDefinitionEquations descriptor)
                (NonEmpty.reverse (snd <$> S.recursiveDefinitionEquations descriptor)) }) binding

fixtureExpression :: S.SemanticGlobalBinding -> Text -> [Raw.Expr] -> Raw.Expr
fixtureExpression datatype name arguments = Raw.ExprOp Nowhere (Raw.MixfixItem pattern' (Raw.Marker name) Raw.NonAssoc) arguments
  where
    known = S.semanticGlobalBindingKey datatype : maybe [] (fmap S.datatypeCaseConstructor . toList . S.datatypeDescriptorCases)
        (S.semanticGlobalBindingDatatype datatype)
    pattern' = fromMaybe (Raw.mixfixPattern (Raw.mkMixfixItem (Just (Raw.Command name) : replicate (length arguments) Nothing)
        (Raw.Marker name) Raw.NonAssoc)) (listToMaybe
            [shape | S.SemanticExpressionFunction shape@(Raw.TokenCons (Raw.Command command) _) <- known, command == name])

fixturePair :: Raw.Expr -> Raw.Expr -> Raw.Expr
fixturePair left right = Raw.ExprOp Nowhere (Raw.mkMixfixItem
    [Just (Raw.Command "upair"),Just Raw.InvisibleBraceL,Nothing,Just Raw.InvisibleBraceR,
     Just Raw.InvisibleBraceL,Nothing,Just Raw.InvisibleBraceR]
    (Raw.Marker "pairset_iff") Raw.NonAssoc) [left,right]

fixtureRelation :: Raw.RelationSymbol -> Raw.Expr -> Raw.Expr -> Raw.Formula
fixtureRelation relation left right = Raw.FormulaChain
    (Raw.ChainBase (left :| []) Raw.Positive (Raw.Relation Nowhere relation []) (right :| []))

nestedClaims :: S.SemanticGlobalBinding -> [Raw.Block]
nestedClaims datatype =
    [ claim "probe_nested_set_1" (fixtureRelation Raw.EqSymbol (value (successor zero)) (pair emptySet emptySet))
    , claim "probe_nested_set_2" (fixtureRelation Raw.EqSymbol (value (successor (successor zero)))
        (pair (pair emptySet emptySet) (pair emptySet emptySet)))
    , claim "probe_negative_prop" (forallA (implies atom (predicate (successor (successor zero)))))
    , claim "probe_negative_fact" (forallA (implies (predicate (successor zero)) (Raw.FormulaNeg Nowhere atom)))
    , claim "probe_computed_constructor" (implies
        (fixtureRelation Raw.ElementSymbol computed (expression "probetree" []))
        (fixtureRelation Raw.EqSymbol (value computed) (pair emptySet emptySet)))
    , claim "probe_binder_congruence" (forallA (Raw.Connected Nowhere Raw.Equivalence
        (Raw.FormulaPredicate Nowhere (Raw.PrefixPredicate "probebinder" 2) (Raw.Marker "probebinder")
            (Raw.ExprVar parameter :| [successor zero]))
        (Raw.FormulaNeg Nowhere (Raw.FormulaQuantified Nowhere Raw.Universally (Raw.NamedVar "z" :| [])
            Raw.Unbounded (Raw.FormulaNeg Nowhere atom)))))
    ]
  where
    expression = fixtureExpression datatype
    zero = expression "probezero" []
    successor term = expression "probesucc" [term]
    value term = expression "probeeval" [term]
    pair = fixturePair
    emptySet = expression "emptyset" []
    computed = expression "probeidentity" [successor zero]
    parameter = Raw.NamedVar "A"
    atom = fixtureRelation Raw.ElementSymbol emptySet (Raw.ExprVar parameter)
    predicate term = Raw.FormulaPredicate Nowhere (Raw.PrefixPredicate "probeprop" 2) (Raw.Marker "probeprop")
        (Raw.ExprVar parameter :| [term])
    implies = Raw.Connected Nowhere Raw.Implication
    forallA = Raw.FormulaQuantified Nowhere Raw.Universally (parameter :| []) Raw.Unbounded
    claim name formula = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker name)
        (Raw.Claim [] (Raw.StmtFormula formula))

factAuditClaim :: S.SemanticGlobalBinding -> Bool -> Raw.Block
factAuditClaim datatype priority = Raw.BlockClaim Raw.Proposition Nowhere Nothing
    (Raw.Marker (if priority then "probe_ordinary_priority" else "probe_unused_fact"))
    (Raw.Claim [] (Raw.StmtFormula (Raw.FormulaQuantified Nowhere Raw.Universally (parameter :| []) Raw.Unbounded body)))
  where
    expression = fixtureExpression datatype
    parameter = Raw.NamedVar "A"
    emptySet = expression "emptyset" []
    atom = fixtureRelation Raw.ElementSymbol emptySet (Raw.ExprVar parameter)
    deep 0 = expression "probezero" []
    deep n = expression "probesucc" [deep (n - 1)]
    premise = Raw.FormulaPredicate Nowhere (Raw.PrefixPredicate "probeprop" 2) (Raw.Marker "probeprop")
        (Raw.ExprVar parameter :| [deep (if priority then 8 else 1 :: Int)])
    body = Raw.Connected Nowhere Raw.Implication premise
        (if priority then Raw.Connected Nowhere Raw.Implication atom
            (Raw.Connected Nowhere Raw.Disjunction atom (Raw.PropositionalConstant Nowhere Raw.IsBottom))
         else fixtureRelation Raw.EqSymbol emptySet emptySet)

witnessClaim :: S.SemanticGlobalBinding -> Raw.Block
witnessClaim datatype = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "probe_witness_application")
    (Raw.Claim [] (Raw.StmtFormula (Raw.FormulaQuantified Nowhere Raw.Universally variables Raw.Unbounded body)))
  where
    expression = fixtureExpression datatype
    a = Raw.NamedVar "A"
    x = Raw.NamedVar "x"
    w = Raw.NamedVar "w"
    variables = a :| [x,w]
    carrier = expression "probewitness" [Raw.ExprVar a]
    node = expression "probewitnessnode" [Raw.ExprVar x]
    conditions = [fixtureRelation Raw.ElementSymbol (Raw.ExprVar x) carrier,
        fixtureRelation Raw.ElementSymbol (Raw.ExprVar w) (Raw.ExprVar a),
        fixtureRelation Raw.ElementSymbol node carrier]
    body = foldr (Raw.Connected Nowhere Raw.Implication)
        (fixtureRelation Raw.EqSymbol (expression "probewitnesseval" [Raw.ExprVar a,node]) (expression "emptyset" [])) conditions

scopeGuardClaim :: S.SemanticGlobalBinding -> Bool -> Raw.Block
scopeGuardClaim datatype siblings = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "probe_scope_guard")
    (Raw.Claim [] (Raw.StmtFormula (if siblings then Raw.Connected Nowhere Raw.Conjunction (scoped True) (scoped False)
        else quantify (implies (member x) (equal x)))))
  where
    expression = fixtureExpression datatype
    variable = Raw.NamedVar "x"
    x = Raw.ExprVar variable
    successor = expression "probesucc" [x]
    quantify = Raw.FormulaQuantified Nowhere Raw.Universally (variable :| []) Raw.Unbounded
    implies = Raw.Connected Nowhere Raw.Implication
    member term = fixtureRelation Raw.ElementSymbol term (expression "probetree" [])
    equal term = fixtureRelation Raw.EqSymbol (expression "probeconstant" [term]) (expression "emptyset" [])
    scoped domain = quantify (implies (member (if domain then x else successor)) (equal successor))

reuseClaim :: S.SemanticGlobalBinding -> Raw.Block
reuseClaim datatype = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "probe_application_reuse")
    (Raw.Claim [] (Raw.StmtFormula (Raw.Connected Nowhere Raw.Conjunction equation
        (Raw.Connected Nowhere Raw.Conjunction equation (Raw.PropositionalConstant Nowhere Raw.IsBottom)))))
  where
    expression = fixtureExpression datatype
    equation = fixtureRelation Raw.EqSymbol (expression "probeeval" [expression "probezero" []]) (expression "emptyset" [])

budgetClaim :: S.SemanticGlobalBinding -> Bool -> Raw.Block
budgetClaim datatype siblings = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "probe_shared_work")
    (Raw.Claim [] (Raw.StmtFormula (if siblings then Raw.Connected Nowhere Raw.Conjunction base successor else base)))
  where
    expression = fixtureExpression datatype
    zero = expression "probezero" []
    emptySet = expression "emptyset" []
    base = fixtureRelation Raw.EqSymbol (expression "probeeval" [zero]) emptySet
    successor = fixtureRelation Raw.EqSymbol (expression "probeeval" [expression "probesucc" [zero]])
        (fixturePair emptySet emptySet)

exposedWitnessClaim :: S.SemanticGlobalBinding -> Bool -> Raw.Block
exposedWitnessClaim datatype present = Raw.BlockClaim Raw.Proposition Nowhere Nothing (Raw.Marker "probe_exposed_witness")
    (Raw.Claim [] (Raw.StmtFormula (Raw.FormulaQuantified Nowhere Raw.Universally
        (a :| [w | present]) Raw.Unbounded body)))
  where
    expression = fixtureExpression datatype
    a = Raw.NamedVar "A"
    w = Raw.NamedVar "w"
    equation = fixtureRelation Raw.EqSymbol
        (expression "probeexpose" [Raw.ExprVar a,expression "probezero" []]) (expression "emptyset" [])
    body = if present then Raw.Connected Nowhere Raw.Implication
        (fixtureRelation Raw.ElementSymbol (Raw.ExprVar w) (Raw.ExprVar a)) equation else equation

-- The same production import path checks declarations, mathematical clients,
-- and failed-declaration atomicity. Construction and corrupt-import checks
-- remain in the normalized fixture above.
sourceRecursion :: Assertion
sourceRecursion = Temp.withSystemTempDirectory "felix-source-recursion" \directory -> do
    repository <- getCurrentDirectory
    foundation <- expectRight F.checkedFoundation
    mounts <- expectRight =<< prepareSourceMounts
        [(sourceMountId "project",directory), (sourceMountId "fixtures",repository),
         (sourceMountId "library",repository </> "library"), (sourceMountId "debug",repository </> "debug")]
    plan <- expectRightIO (Store.planStore (Store.ExplicitStore (directory </> "proofs.sqlite")))
    withTestStoreLease plan \lease -> do
      result <- Store.withOpenStore lease (I.theoryId foundation) \_ store -> do
        prelude <- expectRightIO (acquireFinalPreludeSession store foundation finalPreludeResolver)
        storeCheck <- Store.newStoreCheck store
        let certificates = concatMap Commit.committedBatchValidationCertificates
                . Commit.pendingModulePrefixBatches . M.completedTypedModulePrefix
            compile path = do
                workspace <- parseFinalWorkspace prelude mounts path
                checked <- compileParsedWorkspaceWithReadiness foundation (M.finalPreludeReadiness prelude)
                    finalPreludeResolver (storeValidationPolicy storeCheck) workspace
                for_ checked (expectRightIO . Store.writePendingModulePrefix storeCheck . M.completedTypedModulePrefix)
                pure (workspace,checked)
        for_ ["test/phase5/propositional-recursion-use.tex", "test/phase5/recursion-headers.tex", "test/phase5/recursion-witnesses.tex"] \path -> do
            (workspace,cold) <- compile path
            warm <- compileParsedWorkspaceWithReadiness foundation (M.finalPreludeReadiness prelude)
                finalPreludeResolver (storeValidationPolicy storeCheck) workspace
            assertEqual "source recursion cold/warm interfaces"
                (completedModuleSemantic <$> cold) (completedModuleSemantic <$> warm)
            assertEqual "source recursion cold/warm authority"
                (certificates <$> cold) (certificates <$> warm)
        let base = Text.unlines
                [ "\\begin{recursive-definition}\\label{reject_recursion}"
                , "Define $\\rejectRecursion{A}{p}$ recursively for $p\\in\\plform{A}$ as follows."
                , "\\begin{enumerate}"
                , "\\item[Falsity] $\\rejectRecursion{A}{\\propbot}=\\emptyset$."
                , "\\item[Atom] $\\rejectRecursion{A}{\\propvar{a}}=\\{a\\}$."
                , "\\item[Implication] $\\rejectRecursion{A}{p\\propto q}=\\rejectRecursion{A}{p}$."
                , "\\end{enumerate}\\end{recursive-definition}" ]
            self = "=\\rejectRecursion{A}{p}$"
            header = "\\label{reject_recursion}"
            atom = "\\item[Atom] $\\rejectRecursion{A}{\\propvar{a}}=\\{a\\}$."
            unstored = Text.unlines
                [ "\\begin{datatype}\\label{unstored_tree}"
                , "Define $\\unstoredTree$ inductively as follows."
                , "\\begin{enumerate}"
                , "\\item[Leaf] $\\unstoredLeaf\\in\\unstoredTree$."
                , "\\item[Node] $\\unstoredNode{x}\\in\\unstoredTree$ for $x\\in\\unstoredTree$ and $w\\in\\unstoredTree$."
                , "\\end{enumerate}\\end{datatype}"
                , "\\begin{recursive-definition}\\label{unstored_recursion}"
                , "Define $\\unstoredRecursion{x}$ recursively for $x\\in\\unstoredTree$ as follows."
                , "\\begin{enumerate}"
                , "\\item[Leaf] $\\unstoredRecursion{\\unstoredLeaf}=\\emptyset$."
                , "\\item[Node] $\\unstoredRecursion{\\unstoredNode{x}}=\\unstoredRecursion{w}$."
                , "\\end{enumerate}\\end{recursive-definition}" ]
            mutations =
                [ ("constructed", Text.replace self "=\\rejectRecursion{A}{p\\propto q}$" base)
                , ("changed_parameter", Text.replace self "=\\rejectRecursion{\\emptyset}{p}$" base)
                , ("nonrecursive_field", Text.replace "=\\{a\\}$" "=\\rejectRecursion{A}{a}$" base)
                , ("escaped_variable", Text.replace self "=w$" base)
                , ("unstored_witness", unstored)
                , ("dependent_header", Text.replace header (header <> "\nLet $p\\in A$.") base)
                , ("missing_case", Text.replace atom "" base)
                , ("duplicate_case", Text.replace atom (atom <> "\n" <> atom) base)
                , ("repeated_field", Text.replace "{p\\propto q}" "{p\\propto p}" base)
                , ("wrong_heading", Text.replace "[Atom]" "[Falsity]" base)
                , ("mixed", Text.replace atom "\\item[Atom] $\\rejectRecursion{A}{\\propvar{a}}$ iff $\\top$." base)
                , ("concealed_call", "\\begin{abbreviation}\\label{concealed}\n$\\concealed{p}=p\\propto p$.\n\\end{abbreviation}\n"
                    <> Text.replace self "=\\rejectRecursion{A}{\\concealed{p}}$" base)
                , ("ill_formed_constructor", "\\begin{proposition}\\label{bad_argument}\n"
                    <> "$\\plAtoms{A}{\\propvar{a}}=\\{a\\}$.\n\\end{proposition}\n\\begin{proof}Follows by definition.\\end{proof}")
                , ("missing_header", "\\begin{proposition}\\label{bad_header}\n"
                    <> "$\\guardedConstant{B}{A}{X}{\\propbot}=X$.\n\\end{proposition}\n\\begin{proof}Follows by definition.\\end{proof}")
                ]
        (_,imported) <- compile "test/phase5/recursion-headers.tex"
        root <- maybe (fail "missing recursive source module") pure (listToMaybe (reverse imported))
        for_ mutations \(label,source) -> do
            let path = Text.unpack label <> ".tex"
            TextIO.writeFile (directory </> path) ("\\import{test/phase5/recursion-headers.tex}\n" <> source)
            workspace <- parseFinalWorkspace prelude mounts path
            -- Imports have already passed the ordinary source path. Reuse their
            -- checked closure; inspect the failing root's prefix directly.
            input <- expectRightIO (typedModuleInput foundation (M.finalPreludeReadiness prelude)
                finalPreludeResolver (storeValidationPolicy storeCheck)
                (Parsed.parsedWorkspaceRootModule workspace) [root])
            runTypedModule input >>= \case
                M.TypedModuleFailed (M.TypedActionFailed (M.TypedElaborationFailed _)) prefix ->
                    assertEqual (Text.unpack label <> " leaves no recursive declaration")
                        (if label `elem` ["concealed_call","unstored_witness"] then 1 else 0) (length (Commit.pendingModulePrefixBatches prefix))
                M.TypedModuleFailed (M.TypedActionFailed (M.TypedProofFailed _)) prefix
                    | label `elem` ["ill_formed_constructor","missing_header"] ->
                        assertBool "a failed client publishes nothing" (null (Commit.pendingModulePrefixBatches prefix))
                M.TypedModuleFailed failure _ -> assertFailure (Text.unpack label <> ": " <> show failure)
                _ -> assertFailure (Text.unpack label <> " was not rejected")
        (_,datatypes) <- compile "test/phase5/propositional.tex"
        datatypeRoot <- maybe (fail "missing datatype source module") pure (listToMaybe (reverse datatypes))
        TextIO.writeFile (directory </> "missing-support.tex") ("\\import{test/phase5/propositional.tex}\n" <> base)
        missingSupport <- parseFinalWorkspace prelude mounts "missing-support.tex"
        missingInput <- expectRightIO (typedModuleInput foundation (M.finalPreludeReadiness prelude)
            finalPreludeResolver (storeValidationPolicy storeCheck)
            (Parsed.parsedWorkspaceRootModule missingSupport) [datatypeRoot])
        runTypedModule missingInput >>= \case
            M.TypedModuleFailed (M.TypedDeclarationFailed D.BindingConstructionInvalid{}) prefix ->
                assertBool "missing recursion support publishes nothing" (null (Commit.pendingModulePrefixBatches prefix))
            _ -> assertFailure "a recursive definition without the library construction was not rejected"
        for_ [("partial", Text.replace self "=\\rejectRecursion{A}$" base)] \(label,source) -> do
            let path = label <> ".tex"
            TextIO.writeFile (directory </> path) ("\\import{test/phase5/propositional-recursion.tex}\n" <> source)
            request <- expectRight (searchedRoot path)
            parsed <- Parse.parseSourceWorkspaceWithSyntaxInputs mounts request
                (const [M.sealedTypedModuleSyntax (M.finalPreludeModule prelude)])
            case parsed of
                Left _ -> pure ()
                Right _ -> assertFailure (label <> " unexpectedly parsed")
      void (expectRight result)
