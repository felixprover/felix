{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | A freshly resolved physical source graph.
--
-- Nodes are selected canonical files. Import edges retain every source
-- occurrence, including repeated imports that reach the same node.
module Felix.Source.Graph
    ( SourceNode
    , sourceNodeScanPrefix
    , sourceNodeIdentified
    , sourceNodeLoaded
    , sourceNodeResolved
    , sourceNodeDescriptor
    , sourceNodeContentId
    , SourceImportEdge
    , sourceImportingNode
    , sourceImportReference
    , sourceImportedNode
    , ResolvedSourceGraph
    , sourceGraphRoot
    , sourceGraphRootSource
    , sourceGraphNodes
    , sourceGraphImportEdges
    , sourceGraphImportedBeforeImporter
    , SourcePlanningMeasurements(..)
    , SourceGraphPreparation
    , sourceGraphPreparationGraph
    , sourceGraphPreparationMeasurements
    , buildResolvedSourceGraphMeasured
    , buildResolvedSourceGraph
    ) where

import Base
import Felix.Source
import Felix.Source.Content
    ( IdentifiedLoadedSource
    , SourceContentId
    , identifiedSourceContentId
    , identifiedSourceDescriptor
    , identifiedSourceLoaded
    , identifyLoadedSource
    )
import Felix.Source.Scan
    ( SourceScanFailure(..)
    , SourceScanPrefix
    , forceSourceScanPrefixHandoff
    , renderSourcePrefixError
    , renderSourceScanInvariantError
    , scanSourcePrefix
    , sourcePrefixIdentifiedSource
    , sourcePrefixImports
    )
import Felix.Report.Location (SourceDescriptor)
import Felix.Syntax.Token (Located(..))

import Control.Exception (evaluate)
import Control.Monad (unless)
import Control.Monad.State.Strict
    ( StateT
    , get
    , gets
    , modify'
    , runStateT
    )
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Numeric.Natural (Natural)


data SourceNode = SourceNode
    !SourceScanPrefix
    deriving stock (Show, Eq)

sourceNodeScanPrefix :: SourceNode -> SourceScanPrefix
sourceNodeScanPrefix (SourceNode prefix) = prefix

sourceNodeIdentified :: SourceNode -> IdentifiedLoadedSource
sourceNodeIdentified =
    sourcePrefixIdentifiedSource . sourceNodeScanPrefix

sourceNodeLoaded :: SourceNode -> LoadedSource
sourceNodeLoaded = identifiedSourceLoaded . sourceNodeIdentified

sourceNodeResolved :: SourceNode -> ResolvedSource
sourceNodeResolved = loadedSource . sourceNodeLoaded

sourceNodeDescriptor :: SourceNode -> SourceDescriptor
sourceNodeDescriptor = identifiedSourceDescriptor . sourceNodeIdentified

sourceNodeContentId :: SourceNode -> SourceContentId
sourceNodeContentId = identifiedSourceContentId . sourceNodeIdentified

sourceNodeCanonicalPath :: SourceNode -> CanonicalPath
sourceNodeCanonicalPath =
    resolvedSourceCanonicalPath . sourceNodeResolved


data SourceImportEdge = SourceImportEdge
    !CanonicalPath
    !ImportRef
    !CanonicalPath
    deriving stock (Show, Eq)

sourceImportingNode :: SourceImportEdge -> CanonicalPath
sourceImportingNode (SourceImportEdge importer _reference _imported) =
    importer

sourceImportReference :: SourceImportEdge -> ImportRef
sourceImportReference (SourceImportEdge _importer reference _imported) =
    reference

sourceImportedNode :: SourceImportEdge -> CanonicalPath
sourceImportedNode (SourceImportEdge _importer _reference imported) =
    imported


data ResolvedSourceGraph = ResolvedSourceGraph
    !(NonEmpty SourceNode)
    ![SourceImportEdge]
    deriving stock (Show)

sourceGraphRoot :: ResolvedSourceGraph -> CanonicalPath
sourceGraphRoot =
    sourceNodeCanonicalPath . NonEmpty.last . sourceGraphNodeSpine

sourceGraphRootSource :: ResolvedSourceGraph -> ResolvedSource
sourceGraphRootSource =
    sourceNodeResolved . NonEmpty.last . sourceGraphNodeSpine

sourceGraphNodes :: ResolvedSourceGraph -> [SourceNode]
sourceGraphNodes =
    NonEmpty.toList . sourceGraphNodeSpine

sourceGraphImportEdges :: ResolvedSourceGraph -> [SourceImportEdge]
sourceGraphImportEdges (ResolvedSourceGraph _nodes edges) =
    edges

-- | Deterministic DFS completion order. Imports are visited in textual
-- occurrence order, so every imported node precedes its importer and sibling
-- imports retain their source order.
sourceGraphImportedBeforeImporter :: ResolvedSourceGraph -> NonEmpty SourceNode
sourceGraphImportedBeforeImporter =
    sourceGraphNodeSpine

sourceGraphNodeSpine :: ResolvedSourceGraph -> NonEmpty SourceNode
sourceGraphNodeSpine (ResolvedSourceGraph nodes _edges) =
    nodes


data SourcePlanningMeasurements = SourcePlanningMeasurements
    { sourceGraphPreparationWallNanoseconds :: !Word64
    , sourcePrefixScanCount :: !Natural
    }
    deriving stock (Show, Eq)

data SourceGraphPreparation = SourceGraphPreparation
    { sourceGraphPreparationGraph :: !ResolvedSourceGraph
    , sourceGraphPreparationMeasurements :: !SourcePlanningMeasurements
    }
    deriving stock (Show)


data VisitStatus
    = Visiting
    | Visited
    deriving stock (Show, Eq)

data BuildNode = BuildNode
    !SourceNode
    !VisitStatus

data GraphBuildState = GraphBuildState
    { buildNodes :: !(Map CanonicalPath BuildNode)
    , buildEdgesReversed :: ![SourceImportEdge]
    , buildOrderReversed :: ![SourceNode]
    }

type GraphBuilder = ExceptT SourceError (StateT GraphBuildState IO)

initialGraphBuildState :: GraphBuildState
initialGraphBuildState = GraphBuildState
    { buildNodes = mempty
    , buildEdgesReversed = []
    , buildOrderReversed = []
    }

buildResolvedSourceGraph
    :: SourceMounts
    -> RootRequest
    -> IO (Either SourceError ResolvedSourceGraph)
buildResolvedSourceGraph mounts request =
    fmap sourceGraphPreparationGraph
        <$> buildResolvedSourceGraphMeasured mounts request

buildResolvedSourceGraphMeasured
    :: SourceMounts
    -> RootRequest
    -> IO (Either SourceError SourceGraphPreparation)
buildResolvedSourceGraphMeasured mounts request = do
    started <- getMonotonicTimeNSec
    built <- buildResolvedSourceGraphUnmeasured mounts request
    case built of
        Left failure ->
            pure (Left failure)
        Right graph -> do
            nodeCount <- evaluate (length (sourceGraphNodes graph))
            _edgeCount <- evaluate (length (sourceGraphImportEdges graph))
            finished <- getMonotonicTimeNSec
            pure
                (Right
                    (SourceGraphPreparation
                        graph
                        (SourcePlanningMeasurements
                            (finished - started)
                            (fromIntegral nodeCount))))

buildResolvedSourceGraphUnmeasured
    :: SourceMounts
    -> RootRequest
    -> IO (Either SourceError ResolvedSourceGraph)
buildResolvedSourceGraphUnmeasured mounts request = do
    resolvedRoot <- resolveRoot mounts request
    case resolvedRoot of
        Left err ->
            pure (Left err)
        Right rootSource -> do
            loadedRoot <- loadResolvedSource rootSource
            case loadedRoot of
                Left err ->
                    pure (Left err)
                Right root -> do
                    (result, finalState) <- runStateT
                        (runExceptT do
                            rootNode <- insertFreshNode root
                            visitNode
                                mounts
                                (sourceNodeCanonicalPath rootNode)
                                [])
                        initialGraphBuildState
                    pure case result of
                        Left err ->
                            Left err
                        Right () ->
                            case NonEmpty.nonEmpty
                                (reverse (buildOrderReversed finalState)) of
                                Nothing ->
                                    Left
                                        (SourceGraphInvariantViolation
                                            "source graph has no root node")
                                Just order ->
                                    Right
                                        (ResolvedSourceGraph
                                            order
                                            (reverse
                                                (buildEdgesReversed
                                                    finalState))
                                        )

insertFreshNode :: LoadedSource -> GraphBuilder SourceNode
insertFreshNode loaded = do
    state <- get
    let source = loadedSource loaded
        canonical = resolvedSourceCanonicalPath source
    case Map.lookup canonical (buildNodes state) of
        Just _ ->
            throwE
                (SourceGraphInvariantViolation
                    "attempted to allocate a duplicate canonical source node")
        Nothing -> do
            identified <- liftIO
                (identifyLoadedSource loaded)

            prefix <- case scanSourcePrefix identified of
                Left (SourceInputFailure failure) ->
                    throwE
                        (SourceImportDiscoveryFailed
                            source
                            (renderSourcePrefixError failure))
                Left (SourceScannerInvariantFailure failure) ->
                    throwE
                        (SourceGraphScanningInvariantViolation
                            source
                            (renderSourceScanInvariantError failure))
                Right result -> pure result
            liftIO
                (evaluate (forceSourceScanPrefixHandoff prefix))
            let node = SourceNode prefix
            modify' \current ->
                current
                    { buildNodes =
                        Map.insert
                            canonical
                            (BuildNode node Visiting)
                            (buildNodes current)
                    }
            pure node

visitNode
    :: SourceMounts
    -> CanonicalPath
    -> [SourceCycleStep]
    -> GraphBuilder ()
visitNode mounts canonical path = do
    node <- lookupBuildNode canonical
    references <- discoverNodeImports node
    traverse_ (visitImport mounts node path) references
    modify' \state ->
        state
            { buildNodes =
                Map.adjust
                    (\(BuildNode currentNode _status) ->
                        BuildNode currentNode Visited)
                    canonical
                    (buildNodes state)
            , buildOrderReversed =
                node : buildOrderReversed state
            }

lookupBuildNode :: CanonicalPath -> GraphBuilder SourceNode
lookupBuildNode canonical = do
    nodes <- gets buildNodes
    case Map.lookup canonical nodes of
        Nothing ->
            throwE
                (SourceGraphInvariantViolation
                    "source graph contains an unknown canonical path")
        Just (BuildNode node _status) ->
            pure node

discoverNodeImports :: SourceNode -> GraphBuilder [ImportRef]
discoverNodeImports node = do
    traverse
        (validateImport (sourceNodeResolved node))
        (sourcePrefixImports prefix)
  where
    SourceNode prefix = node

validateImport
    :: ResolvedSource
    -> Located FilePath
    -> GraphBuilder ImportRef
validateImport source locatedPath =
    case importRef (startPos locatedPath) (unLocated locatedPath) of
        Left err ->
            throwE
                (InvalidImportPath
                    source
                    (startPos locatedPath)
                    (unLocated locatedPath)
                    err)
        Right reference ->
            pure reference

visitImport
    :: SourceMounts
    -> SourceNode
    -> [SourceCycleStep]
    -> ImportRef
    -> GraphBuilder ()
visitImport mounts importerNode path reference = do
    let importer = sourceNodeResolved importerNode
        importerCanonical = sourceNodeCanonicalPath importerNode
    imported <- liftEitherIO (resolveImport mounts importer reference)
    let importedCanonical = resolvedSourceCanonicalPath imported
    existing <- gets (Map.lookup importedCanonical . buildNodes)
    case existing of
        Nothing -> do
            loaded <- liftEitherIO (loadResolvedSource imported)
            importedNode <- insertFreshNode loaded
            appendEdge importerCanonical reference importedCanonical
            let step = sourceCycleStep importer reference imported
            visitNode mounts (sourceNodeCanonicalPath importedNode) (path <> [step])
        Just (BuildNode importedNode status) -> do
            unless
                (sourceNodeResolved importedNode == imported)
                (throwE
                    (SourceGraphInvariantViolation
                        "canonical source attribution changed within one graph"))
            appendEdge importerCanonical reference importedCanonical
            case status of
                Visited ->
                    pure ()
                Visiting -> do
                    let step = sourceCycleStep importer reference imported
                    case cycleSuffix imported (path <> [step]) of
                        Just cycleSteps ->
                            throwE (SourceImportCycle cycleSteps)
                        Nothing ->
                            throwE
                                (SourceGraphInvariantViolation
                                    "cycle target is absent from the DFS path")

appendEdge
    :: CanonicalPath
    -> ImportRef
    -> CanonicalPath
    -> GraphBuilder ()
appendEdge importer reference imported =
    modify' \state ->
        state
            { buildEdgesReversed =
                SourceImportEdge importer reference imported
                    : buildEdgesReversed state
            }

cycleSuffix
    :: ResolvedSource
    -> [SourceCycleStep]
    -> Maybe (NonEmpty SourceCycleStep)
cycleSuffix repeatedSource path =
    NonEmpty.nonEmpty
        (List.dropWhile
            ((/= resolvedSourceCanonicalPath repeatedSource)
                . resolvedSourceCanonicalPath
                . cycleImporter)
            path)

liftEitherIO :: IO (Either SourceError a) -> GraphBuilder a
liftEitherIO action =
    liftIO action >>= either throwE pure
