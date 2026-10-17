{-# LANGUAGE OverloadedStrings #-}

module Felix.Test.Unit.HtmlLayout (unitTests) where

import Base
import Felix.Source
import Felix.Source.Graph
import Felix.Render.Html.Layout
import Felix.Test.Temp (withTemporaryDirectory)

import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as Text
import System.Directory qualified as Directory
import System.FilePath.Posix qualified as Posix
import Test.Tasty
import Test.Tasty.HUnit


unitTests :: TestTree
unitTests =
    testGroup "HTML layout"
        [ testCase
            "encodes URL segments canonically"
            encodesUrlSegments
        , testCase
            "renders relative typed URLs"
            rendersRelativeUrls
        , testCase
            "separates mounted route namespaces"
            separatesMountedNamespaces
        , testCase
            "routes searched and exact roots identically"
            routesRootFormsIdentically
        , testCase
            "requires an explicit mount for an external root"
            requiresExternalMount
        , testCase
            "reports URL and destination collisions independently"
            reportsRouteCollisions
        , testCase
            "rejects ancestor and descendant destinations"
            rejectsNestedDestinations
        , testCase
            "reserves the synthetic declaration index route"
            reservesDeclarationIndexRoute
        , testCase
            "is independent of graph and configuration traversal order"
            isTraversalOrderIndependent
        ]


encodesUrlSegments :: Assertion
encodesUrlSegments = do
    let accepted =
            [ ("AZaz09-._~", "AZaz09-._~")
            , ("#?% \\", "%23%3F%25%20%5C")
            , ("über", "%C3%BCber")
            , ("%2f", "%252f")
            ]
    for_ accepted \(decoded, expected) ->
        assertEqual
            ("encoded segment " <> Text.unpack decoded)
            (Right expected)
            (renderUrlSegment <$> urlSegment decoded)
    let rejected =
            [ ("", EmptyUrlSegment)
            , (".", DotUrlSegment ".")
            , ("..", DotUrlSegment "..")
            , ("a/b", UrlSegmentContainsSeparator "a/b")
            ]
    for_ rejected \(decoded, expected) ->
        assertEqual
            ("rejected segment " <> Text.unpack decoded)
            (Left expected)
            (urlSegment decoded)
    assertEqual
        "fragment encoding"
        "#name%23%C3%BC"
        (renderUrlFragment "name#ü")

rendersRelativeUrls :: Assertion
rendersRelativeUrls = do
    let cases =
            [ ( ["library", "nested", "über"]
              , ["_static", "naproche-html.js"]
              , "../../_static/naproche-html.js"
              )
            , ( ["first", "entry"]
              , ["second", "entry"]
              , "../second/entry"
              )
            , ( ["mount", "entry"]
              , ["mount", "a?b"]
              , "a%3Fb"
              )
            , ( ["library", "everything", "declarations"]
              , ["library", "everything"]
              , "../everything"
              )
            ]
    for_ cases \(currentSegments, targetSegments, expected) -> do
        current <- expectRight (urlPath currentSegments)
        target <- expectRight (urlPath targetSegments)
        assertEqual
            "relative URL"
            expected
            (renderRelativeUrlPath current target)
    current <- expectRight (urlPath ["mount", "entry"])
    target <- expectRight (urlPath ["mount", "ü"])
    assertEqual
        "encoded path and fragment remain separate"
        "%C3%BC#part%23%3F"
        ( renderRelativeUrlPath current target
            <> renderUrlFragment "part#?"
        )

separatesMountedNamespaces :: Assertion
separatesMountedNamespaces =
    withTemporaryDirectory "felix-html-layout-mounts" \temp -> do
        let mountSpecifications =
                [ ("project", [])
                , ("library", ["library"])
                , ("debug", ["debug"])
                , ("external", ["external"])
                ]
        roots <- for mountSpecifications \(ident, _prefix) -> do
            let root = temp Posix.</> Text.unpack ident
            Directory.createDirectory root
            writeTheory (root Posix.</> "entry.tex") []
            pure (sourceMountId ident, root)
        mounts <- expectRight =<< prepareSourceMounts roots
        routes <- for mountSpecifications \(ident, prefix) -> do
            let sourcePath =
                    temp
                        Posix.</> Text.unpack ident
                        Posix.</> "entry.tex"
            request <- expectRight =<< existingRoot sourcePath
            graph <- expectRight =<< buildResolvedSourceGraph mounts request
            layout <-
                expectRight
                    (layoutHtmlSourceGraph
                        [ (sourceMountId configuredId, configuredPrefix)
                        | (configuredId, configuredPrefix) <-
                            mountSpecifications
                        ]
                        graph)
            route <- requireRootRoute graph layout
            pure
                ( ident
                , renderUrlPath (routeUrlPath route)
                , safeRelativePathFilePath
                    (routeDestination route)
                , prefix
                )
        assertEqual
            "mount URLs"
            [ ("project", "/entry")
            , ("library", "/library/entry")
            , ("debug", "/debug/entry")
            , ("external", "/external/entry")
            ]
            [ (ident, url) | (ident, url, _destination, _prefix) <- routes ]
        assertEqual
            "mount destinations"
            [ ("project", "entry.html")
            , ("library", "library/entry.html")
            , ("debug", "debug/entry.html")
            , ("external", "external/entry.html")
            ]
            [ (ident, destination)
            | (ident, _url, destination, _prefix) <- routes
            ]

routesRootFormsIdentically :: Assertion
routesRootFormsIdentically =
    withTemporaryDirectory "felix-html-layout-root-forms" \temp -> do
        let libraryRoot = temp Posix.</> "library"
            entry = libraryRoot Posix.</> "entry.tex"
        Directory.createDirectory libraryRoot
        writeTheory entry []
        mounts <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "project", temp)
            , (sourceMountId "library", libraryRoot)
            ]
        searched <- expectRight (searchedRoot "library/entry.tex")
        exact <- expectRight =<< existingRoot entry
        searchedGraph <-
            expectRight =<< buildResolvedSourceGraph mounts searched
        exactGraph <-
            expectRight =<< buildResolvedSourceGraph mounts exact
        let configuration =
                [ (sourceMountId "project", [])
                , (sourceMountId "library", ["library"])
                ]
        searchedLayout <-
            expectRight
                (layoutHtmlSourceGraph configuration searchedGraph)
        exactLayout <-
            expectRight
                (layoutHtmlSourceGraph configuration exactGraph)
        searchedRoute <-
            requireRootRoute searchedGraph searchedLayout
        exactRoute <-
            requireRootRoute exactGraph exactLayout
        assertEqual "selected route" searchedRoute exactRoute
        assertEqual
            "most-specific URL"
            "/library/entry"
            (renderUrlPath (routeUrlPath searchedRoute))

requiresExternalMount :: Assertion
requiresExternalMount =
    withTemporaryDirectory "felix-html-layout-external" \temp -> do
        let projectRoot = temp Posix.</> "project"
            externalRoot = temp Posix.</> "vendor"
            externalEntry = externalRoot Posix.</> "entry.tex"
        Directory.createDirectory projectRoot
        Directory.createDirectory externalRoot
        writeTheory externalEntry []
        request <- expectRight =<< existingRoot externalEntry
        projectMounts <- expectRight =<< prepareSourceMounts
            [(sourceMountId "project", projectRoot)]
        outsideResult <-
            buildResolvedSourceGraph projectMounts request
        case outsideResult of
            Left RootOutsideConfiguredMount{} ->
                pure ()
            result ->
                assertFailure
                    ("expected external root rejection, got "
                        <> show result)
        mounted <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "project", projectRoot)
            , (sourceMountId "external", externalRoot)
            ]
        graph <- expectRight =<< buildResolvedSourceGraph mounted request
        layout <-
            expectRight
                (layoutHtmlSourceGraph
                    [ (sourceMountId "project", [])
                    , (sourceMountId "external", ["vendor"])
                    ]
                    graph)
        route <- requireRootRoute graph layout
        assertEqual
            "external URL"
            "/vendor/entry"
            (renderUrlPath (routeUrlPath route))

reportsRouteCollisions :: Assertion
reportsRouteCollisions = do
    reportsPageCollisions
    reportsAssetUrlCollision

reportsPageCollisions :: Assertion
reportsPageCollisions =
    withTemporaryDirectory "felix-html-layout-page-collision" \temp -> do
        let firstRoot = temp Posix.</> "first"
            secondRoot = temp Posix.</> "second"
            firstEntry = firstRoot Posix.</> "two" Posix.</> "a.tex"
        Directory.createDirectory firstRoot
        Directory.createDirectory secondRoot
        Directory.createDirectory (firstRoot Posix.</> "two")
        writeTheory (secondRoot Posix.</> "a.tex") []
        writeTheory firstEntry ["a.tex"]
        mounts <- expectRight =<< prepareSourceMounts
            [ (sourceMountId "first", firstRoot)
            , (sourceMountId "second", secondRoot)
            ]
        request <- expectRight =<< existingRoot firstEntry
        graph <- expectRight =<< buildResolvedSourceGraph mounts request
        let configuration =
                [ (sourceMountId "first", ["one"])
                , (sourceMountId "second", ["one", "two"])
                ]
        case layoutHtmlSourceGraph configuration graph of
            Left
                (CollidingHtmlRoutes
                    [HtmlUrlRouteCollision url owners]
                    [HtmlDestinationRouteCollision destination
                        destinationOwners]) -> do
                            assertEqual
                                "canonical URL collision"
                                "/one/two/a"
                                (renderUrlPath url)
                            assertEqual
                                "URL owners"
                                (NonEmpty.toList owners)
                                (NonEmpty.toList destinationOwners)
                            assertEqual
                                "destination collision"
                                "one/two/a.html"
                                (safeRelativePathFilePath destination)
            result ->
                assertFailure
                    ("expected paired route collisions, got "
                        <> show result)

reportsAssetUrlCollision :: Assertion
reportsAssetUrlCollision =
    withTemporaryDirectory "felix-html-layout-asset-collision" \temp -> do
        let entry =
                temp
                    Posix.</> "_static"
                    Posix.</> "naproche-html.js.tex"
        Directory.createDirectory (temp Posix.</> "_static")
        writeTheory entry []
        writeTheory
            (temp Posix.</> "entry.tex")
            ["_static/naproche-html.js.tex"]
        mounts <- expectRight =<< prepareSourceMounts
            [(sourceMountId "project", temp)]
        request <-
            expectRight
                (searchedRoot "entry.tex")
        graph <- expectRight =<< buildResolvedSourceGraph mounts request
        case
            layoutHtmlSourceGraph
                [(sourceMountId "project", [])]
                graph of
            Left
                (CollidingHtmlRoutes
                    [HtmlUrlRouteCollision url _owners]
                    []) ->
                        assertEqual
                            "page/asset URL collision"
                            "/_static/naproche-html.js"
                            (renderUrlPath url)
            result ->
                assertFailure
                    ("expected URL-only asset collision, got "
                        <> show result)

rejectsNestedDestinations :: Assertion
rejectsNestedDestinations =
    withTemporaryDirectory "felix-html-layout-nested" \temp -> do
        let nestedDirectory = temp Posix.</> "a.html"
        Directory.createDirectory nestedDirectory
        writeTheory (temp Posix.</> "a.tex") []
        writeTheory (nestedDirectory Posix.</> "b.tex") []
        writeTheory
            (temp Posix.</> "entry.tex")
            ["a.tex", "a.html/b.tex"]
        mounts <- expectRight =<< prepareSourceMounts
            [(sourceMountId "project", temp)]
        request <- expectRight (searchedRoot "entry.tex")
        graph <- expectRight =<< buildResolvedSourceGraph mounts request
        case layoutHtmlSourceGraph
                [(sourceMountId "project", [])]
                graph of
            Left
                (CollidingHtmlRoutes
                    []
                    [NestedHtmlDestinationRouteCollision
                        ancestor
                        ancestorOwner
                        descendant
                        descendantOwner]) -> do
                            assertEqual
                                "ancestor destination"
                                "a.html"
                                (safeRelativePathFilePath ancestor)
                            assertEqual
                                "ancestor owner"
                                "a.tex"
                                (pageOwnerPath ancestorOwner)
                            assertEqual
                                "descendant destination"
                                "a.html/b.html"
                                (safeRelativePathFilePath descendant)
                            assertEqual
                                "descendant owner"
                                "a.html/b.tex"
                                (pageOwnerPath descendantOwner)
            result ->
                assertFailure
                    ("expected nested destination collision, got "
                        <> show result)
  where
    pageOwnerPath = \case
        HtmlPage source ->
            safeRelativePathFilePath
                (resolvedSourceRelativePath source)
        HtmlAsset HtmlSupportScriptAsset ->
            "<support script>"
        HtmlAsset HtmlStylesheetAsset ->
            "<stylesheet>"
        HtmlDeclarationIndex{} ->
            "<declaration index>"

reservesDeclarationIndexRoute :: Assertion
reservesDeclarationIndexRoute =
    withTemporaryDirectory "felix-html-layout-declarations" \temp -> do
        Directory.createDirectory (temp Posix.</> "entry")
        writeTheory (temp Posix.</> "entry" Posix.</> "declarations.tex") []
        writeTheory
            (temp Posix.</> "entry.tex")
            ["entry/declarations.tex"]
        mounts <- expectRight =<< prepareSourceMounts
            [(sourceMountId "project", temp)]
        request <- expectRight (searchedRoot "entry.tex")
        graph <- expectRight =<< buildResolvedSourceGraph mounts request
        case layoutHtmlSourceGraph
                [(sourceMountId "project", [])]
                graph of
            Left
                (CollidingHtmlRoutes
                    [HtmlUrlRouteCollision path owners]
                    [HtmlDestinationRouteCollision destination
                        destinationOwners]) -> do
                            assertEqual "declaration URL"
                                "/entry/declarations"
                                (renderUrlPath path)
                            assertEqual "declaration destination"
                                "entry/declarations.html"
                                (safeRelativePathFilePath destination)
                            assertEqual "collision owners"
                                (NonEmpty.toList owners)
                                (NonEmpty.toList destinationOwners)
            result ->
                assertFailure
                    ("expected declaration-index collision, got "
                        <> show result)

isTraversalOrderIndependent :: Assertion
isTraversalOrderIndependent =
    withTemporaryDirectory "felix-html-layout-order" \temp -> do
        writeTheory (temp Posix.</> "a.tex") []
        writeTheory (temp Posix.</> "b.tex") []
        let root = temp Posix.</> "entry.tex"
        writeTheory root ["a.tex", "b.tex"]
        mounts <- expectRight =<< prepareSourceMounts
            [(sourceMountId "project", temp)]
        request <- expectRight (searchedRoot "entry.tex")
        firstGraph <-
            expectRight =<< buildResolvedSourceGraph mounts request
        writeTheory root ["b.tex", "a.tex"]
        secondGraph <-
            expectRight =<< buildResolvedSourceGraph mounts request
        let firstConfiguration =
                [ (sourceMountId "unused", ["unused"])
                , (sourceMountId "project", [])
                ]
        firstLayout <-
            expectRight
                (layoutHtmlSourceGraph
                    firstConfiguration
                    firstGraph)
        for_
            (zip
                (cycle [firstGraph, secondGraph])
                (List.permutations firstConfiguration))
            \(orderedGraph, configuration) -> do
                layout <-
                    expectRight
                        (layoutHtmlSourceGraph
                            configuration
                            orderedGraph)
                assertEqual
                    "route table"
                    firstLayout
                    layout

        let collidingConfiguration =
                [ (sourceMountId "z", ["same"])
                , (sourceMountId "a", ["same"])
                , (sourceMountId "project", [])
                ]
            expectedCollision =
                layoutHtmlSourceGraph
                    collidingConfiguration
                    firstGraph
        for_
            (zip
                (cycle [firstGraph, secondGraph])
                (List.permutations collidingConfiguration))
            \(orderedGraph, configuration) ->
                assertEqual
                    "collision diagnostic"
                    expectedCollision
                    (layoutHtmlSourceGraph
                        configuration
                        orderedGraph)


requireRootRoute
    :: ResolvedSourceGraph
    -> HtmlLayout
    -> IO HtmlRoute
requireRootRoute graph layout =
    case htmlPageRoute layout (sourceGraphRootSource graph) of
        Just route ->
            pure route
        Nothing ->
            assertFailure "layout omitted the root source"
                >> pure (impossible "requireRootRoute: assertFailure returned")

writeTheory :: FilePath -> [FilePath] -> IO ()
writeTheory path imports =
    writeFile path
        (unlines
            (["\\import{" <> imported <> "}" | imported <- imports]
                <> [ "\\begin{axiom}\\label{route_fixture}"
                   , "  $x = x$."
                   , "\\end{axiom}"
                   ]))

expectRight :: (Show e, HasCallStack) => Either e a -> IO a
expectRight = \case
    Left err ->
        assertFailure ("expected Right, got Left " <> show err)
    Right value ->
        pure value
