{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Pure browser and destination routing for a resolved source graph.
module Felix.Render.Html.Layout
    ( UrlSegment
    , UrlSegmentError(..)
    , urlSegment
    , renderUrlSegment
    , UrlPath
    , urlPath
    , renderUrlPath
    , renderRelativeUrlPath
    , renderUrlFragment
    , HtmlRoute
    , routeDestination
    , routeUrlPath
    , HtmlAsset(..)
    , allHtmlAssets
    , HtmlRouteOwner(..)
    , HtmlUrlRouteCollision(..)
    , HtmlDestinationRouteCollision(..)
    , HtmlLayoutError(..)
    , renderHtmlLayoutError
    , HtmlLayout
    , htmlPageRoutes
    , htmlPageRoute
    , htmlAssetRoute
    , htmlSupportScriptRoute
    , htmlStylesheetRoute
    , htmlDeclarationIndexRoute
    , htmlLayoutDestinations
    , htmlMountUrlPrefixes
    , layoutHtmlSources
    , layoutHtmlSourceGraph
    ) where

import Base
import Felix.Source
import Felix.Source.Graph

import Control.Exception (Exception)
import Data.Bifunctor (first)
import Data.ByteString qualified as ByteString
import Data.Char (chr)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text qualified as Text
import Data.Text.Encoding qualified as TextEncoding
import Data.Word (Word8)
import System.FilePath.Posix qualified as Posix


-- | One canonical percent-encoded URL path segment.
newtype UrlSegment = UrlSegment Text
    deriving stock (Show, Eq, Ord)

data UrlSegmentError
    = EmptyUrlSegment
    | DotUrlSegment !Text
    | UrlSegmentContainsSeparator !Text
    | UrlSegmentContainsNull !Text
    deriving stock (Show, Eq)

urlSegment :: Text -> Either UrlSegmentError UrlSegment
urlSegment decoded
    | Text.null decoded =
        Left EmptyUrlSegment
    | decoded == "." || decoded == ".." =
        Left (DotUrlSegment decoded)
    | "/" `Text.isInfixOf` decoded =
        Left (UrlSegmentContainsSeparator decoded)
    | "\0" `Text.isInfixOf` decoded =
        Left (UrlSegmentContainsNull decoded)
    | otherwise =
        Right (UrlSegment (percentEncodeUtf8 decoded))

renderUrlSegment :: UrlSegment -> Text
renderUrlSegment (UrlSegment encoded) =
    encoded


-- | A root-relative URL path. Its segments are already encoded.
newtype UrlPath = UrlPath [UrlSegment]
    deriving stock (Show, Eq, Ord)

urlPath :: [Text] -> Either UrlSegmentError UrlPath
urlPath =
    fmap UrlPath . traverse urlSegment

renderUrlPath :: UrlPath -> Text
renderUrlPath (UrlPath segments) =
    "/" <> Text.intercalate "/" (renderUrlSegment <$> segments)

-- | Render a target path relative to the directory of a current page.
renderRelativeUrlPath :: UrlPath -> UrlPath -> Text
renderRelativeUrlPath
    (UrlPath currentPageSegments)
    (UrlPath targetSegments) =
        case (remainingCurrent, remainingTarget, reverse targetSegments) of
            -- A target equal to the current page's URL directory is still a
            -- sibling document, not the directory resource denoted by ".".
            -- Repeat its final segment explicitly so extensionless child
            -- routes can link back to their parent page.
            ([], [], finalTarget : _) ->
                "../" <> renderUrlSegment finalTarget
            _ ->
                case relativeSegments of
                    [] -> "."
                    _ -> Text.intercalate "/" relativeSegments
  where
    currentDirectorySegments =
        case reverse currentPageSegments of
            [] ->
                []
            _page : directoryReversed ->
                reverse directoryReversed
    (remainingCurrent, remainingTarget) =
        dropCommonPrefix currentDirectorySegments targetSegments
    relativeSegments =
        replicate (length remainingCurrent) ".."
            <> (renderUrlSegment <$> remainingTarget)

-- | Render an exact source marker as an encoded URL fragment.
renderUrlFragment :: Text -> Text
renderUrlFragment marker =
    "#" <> percentEncodeUtf8 marker


data HtmlRoute = HtmlRoute
    { routeDestination :: !SafeRelativePath
    , routeUrlPath :: !UrlPath
    }
    deriving stock (Show, Eq)

data HtmlAsset
    = HtmlSupportScriptAsset
    | HtmlStylesheetAsset
    deriving stock (Show, Eq, Ord, Enum, Bounded)

allHtmlAssets :: [HtmlAsset]
allHtmlAssets = [minBound .. maxBound]

data HtmlRouteOwner
    = HtmlPage !ResolvedSource
    | HtmlAsset !HtmlAsset
    | HtmlDeclarationIndex !ResolvedSource
    deriving stock (Show, Eq, Ord)

data HtmlUrlRouteCollision = HtmlUrlRouteCollision
    !UrlPath
    !(NonEmpty HtmlRouteOwner)
    deriving stock (Show, Eq)

data HtmlDestinationRouteCollision = HtmlDestinationRouteCollision
        !SafeRelativePath
        !(NonEmpty HtmlRouteOwner)
    | NestedHtmlDestinationRouteCollision
        !SafeRelativePath
        !HtmlRouteOwner
        !SafeRelativePath
        !HtmlRouteOwner
    deriving stock (Show, Eq)

data HtmlLayoutError
    = DuplicateHtmlMountId !SourceMountId
    | InvalidHtmlMountPrefixSegment
        !SourceMountId
        !Text
        !UrlSegmentError
    | DuplicateHtmlMountPrefix
        ![Text]
        !(NonEmpty SourceMountId)
    | MissingHtmlMountPrefix !SourceMountId
    | MissingHtmlRootSource !ResolvedSource
    | InvalidHtmlRouteSegment
        !HtmlRouteOwner
        !Text
        !UrlSegmentError
    | InvalidHtmlRouteDestination
        !HtmlRouteOwner
        !FilePath
        !RelativePathError
    | CollidingHtmlRoutes
        ![HtmlUrlRouteCollision]
        ![HtmlDestinationRouteCollision]
    deriving stock (Show, Eq)

instance Exception HtmlLayoutError

renderHtmlLayoutError :: HtmlLayoutError -> Text
renderHtmlLayoutError = \case
    DuplicateHtmlMountId mount ->
        "HTML mount is configured more than once: "
            <> quoteText (sourceMountIdText mount)
    InvalidHtmlMountPrefixSegment mount segment _problem ->
        "HTML mount " <> quoteText (sourceMountIdText mount)
            <> " has invalid route segment " <> quoteText segment
    DuplicateHtmlMountPrefix prefix mounts ->
        "HTML route prefix " <> quoteText (Text.intercalate "/" prefix)
            <> " is shared by mounts "
            <> Text.intercalate ", "
                (quoteText . sourceMountIdText <$> toList mounts)
    MissingHtmlMountPrefix mount ->
        "no HTML route prefix is configured for mount "
            <> quoteText (sourceMountIdText mount)
    MissingHtmlRootSource source ->
        "the selected HTML root is not present in the rendered source set: "
            <> quoteText
                (sourceMountIdText (resolvedSourceMount source)
                    <> ":"
                    <> Text.pack
                        (safeRelativePathFilePath
                            (resolvedSourceRelativePath source)))
    InvalidHtmlRouteSegment owner segment _problem ->
        renderOwner owner <> " has invalid route segment " <> quoteText segment
    InvalidHtmlRouteDestination owner path _problem ->
        renderOwner owner <> " has invalid HTML destination " <> quotePath path
    CollidingHtmlRoutes urlCollisions destinationCollisions ->
        "HTML routes collide: "
            <> Text.intercalate "; "
                ( (renderUrlCollision <$> urlCollisions)
                    <> (renderDestinationCollision <$> destinationCollisions)
                )
  where
    renderUrlCollision (HtmlUrlRouteCollision path owners) =
        "URL " <> quoteText (renderUrlPath path)
            <> " is owned by "
            <> Text.intercalate ", " (renderOwner <$> toList owners)

    renderDestinationCollision
            (HtmlDestinationRouteCollision path owners) =
        "destination "
            <> quotePath (safeRelativePathFilePath path)
            <> " is owned by "
            <> Text.intercalate ", " (renderOwner <$> toList owners)
    renderDestinationCollision
            (NestedHtmlDestinationRouteCollision
                ancestor ancestorOwner descendant descendantOwner) =
        "destination " <> quotePath (safeRelativePathFilePath ancestor)
            <> " for " <> renderOwner ancestorOwner
            <> " is an ancestor of "
            <> quotePath (safeRelativePathFilePath descendant)
            <> " for " <> renderOwner descendantOwner

renderOwner :: HtmlRouteOwner -> Text
renderOwner = \case
    HtmlPage source ->
        "page "
            <> quoteText
                (sourceMountIdText (resolvedSourceMount source)
                    <> ":"
                    <> Text.pack
                        (safeRelativePathFilePath
                            (resolvedSourceRelativePath source)))
    HtmlAsset asset ->
        case asset of
            HtmlSupportScriptAsset -> "support script"
            HtmlStylesheetAsset -> "stylesheet"
    HtmlDeclarationIndex root ->
        "declaration index for "
            <> quoteText
                (sourceMountIdText (resolvedSourceMount root)
                    <> ":"
                    <> Text.pack
                        (safeRelativePathFilePath
                            (resolvedSourceRelativePath root)))

quotePath :: FilePath -> Text
quotePath = Text.pack . show

quoteText :: Text -> Text
quoteText = Text.pack . show

data HtmlLayout = HtmlLayout
    !(Map ResolvedSource HtmlRoute)
    !(Map HtmlAsset HtmlRoute)
    !HtmlRoute
    !(Map SourceMountId UrlPath)
    deriving stock (Show, Eq)

htmlPageRoutes :: HtmlLayout -> [(ResolvedSource, HtmlRoute)]
htmlPageRoutes (HtmlLayout routes _assets _declarations _mountPrefixes) =
    Map.toAscList routes

htmlPageRoute :: HtmlLayout -> ResolvedSource -> Maybe HtmlRoute
htmlPageRoute (HtmlLayout routes _assets _declarations _mountPrefixes) source =
    Map.lookup source routes

htmlAssetRoute :: HtmlLayout -> HtmlAsset -> HtmlRoute
htmlAssetRoute (HtmlLayout _pages assets _declarations _mountPrefixes) asset =
    fromMaybe
        (impossible ("HTML layout is missing asset " <> show asset))
        (Map.lookup asset assets)

htmlSupportScriptRoute :: HtmlLayout -> HtmlRoute
htmlSupportScriptRoute layout =
    htmlAssetRoute layout HtmlSupportScriptAsset

htmlStylesheetRoute :: HtmlLayout -> HtmlRoute
htmlStylesheetRoute layout =
    htmlAssetRoute layout HtmlStylesheetAsset

htmlDeclarationIndexRoute :: HtmlLayout -> HtmlRoute
htmlDeclarationIndexRoute
        (HtmlLayout _pages _assets declarations _mountPrefixes) =
    declarations

htmlLayoutDestinations :: HtmlLayout -> [SafeRelativePath]
htmlLayoutDestinations layout =
    [ routeDestination route
    | (_source, route) <- htmlPageRoutes layout
    ]
        <> [ routeDestination (htmlAssetRoute layout asset)
           | asset <- allHtmlAssets
           ]
        <> [routeDestination (htmlDeclarationIndexRoute layout)]

htmlMountUrlPrefixes :: HtmlLayout -> Map SourceMountId UrlPath
htmlMountUrlPrefixes (HtmlLayout _routes _assets _declarations mountPrefixes) =
    mountPrefixes


data ValidatedMountPrefix = ValidatedMountPrefix
    ![Text]
    ![UrlSegment]

layoutHtmlSourceGraph
    :: [(SourceMountId, [Text])]
    -> ResolvedSourceGraph
    -> Either HtmlLayoutError HtmlLayout
layoutHtmlSourceGraph specifications graph =
    layoutHtmlSources
        specifications
        (sourceGraphRootSource graph)
        (sourceNodeResolved <$> sourceGraphNodes graph)

layoutHtmlSources
    :: [(SourceMountId, [Text])]
    -> ResolvedSource
    -> [ResolvedSource]
    -> Either HtmlLayoutError HtmlLayout
layoutHtmlSources specifications rootSource inputSources = do
    prefixes <- validateMountPrefixes specifications
    let sources =
            List.sort
                inputSources
        usedMounts =
            Set.fromList (resolvedSourceMount <$> sources)
        missingMounts =
            usedMounts `Set.difference` Map.keysSet prefixes
    case Set.lookupMin missingMounts of
        Just missing ->
            Left (MissingHtmlMountPrefix missing)
        Nothing -> do
            pageEntries <-
                traverse
                    (makePageRoute prefixes)
                    sources
            assetEntries <- traverse makeAssetRoute allHtmlAssets
            rootRoute <-
                maybe
                    (Left (MissingHtmlRootSource rootSource))
                    Right
                    (List.lookup rootSource pageEntries)
            declarations <- makeDeclarationIndexRoute rootSource rootRoute
            let ownedRoutes =
                    [ (HtmlPage source, route)
                    | (source, route) <- pageEntries
                    ]
                        <> [ (HtmlAsset asset, route)
                           | (asset, route) <- assetEntries
                           ]
                        <> [(HtmlDeclarationIndex rootSource, declarations)]
                urlCollisions =
                    collectUrlCollisions ownedRoutes
                destinationCollisions =
                    collectDestinationCollisions ownedRoutes
                        <> collectNestedDestinationCollisions ownedRoutes
            if null urlCollisions && null destinationCollisions
                then
                    Right
                        (HtmlLayout
                            (Map.fromList pageEntries)
                            (Map.fromList assetEntries)
                            declarations
                            (Map.map
                                (\(ValidatedMountPrefix _decoded encoded) ->
                                    UrlPath encoded)
                                prefixes))
                else
                    Left
                        (CollidingHtmlRoutes
                            urlCollisions
                            destinationCollisions)

makeAssetRoute :: HtmlAsset -> Either HtmlLayoutError (HtmlAsset, HtmlRoute)
makeAssetRoute asset = do
    let owner = HtmlAsset asset
        components = htmlAssetComponents asset
    encoded <- encodeRouteSegments owner components
    route <- makeRoute owner components encoded
    pure (asset, route)

makeDeclarationIndexRoute
    :: ResolvedSource
    -> HtmlRoute
    -> Either HtmlLayoutError HtmlRoute
makeDeclarationIndexRoute rootSource rootRoute = do
    declarationSegment <-
        first
            (InvalidHtmlRouteSegment owner "declarations")
            (urlSegment "declarations")
    makeRoute
        owner
        destinationComponents
        (rootUrlComponents <> [declarationSegment])
  where
    owner = HtmlDeclarationIndex rootSource
    destinationComponents =
        replaceFinalComponent
            (Text.pack . Posix.dropExtension . Text.unpack)
            (Text.pack
                <$> relativePathComponents
                    (routeDestination rootRoute))
            <> ["declarations.html"]
    UrlPath rootUrlComponents = routeUrlPath rootRoute

validateMountPrefixes
    :: [(SourceMountId, [Text])]
    -> Either HtmlLayoutError (Map SourceMountId ValidatedMountPrefix)
validateMountPrefixes specifications =
    case duplicateValues (fst <$> specifications) of
        duplicate : _ ->
            Left (DuplicateHtmlMountId duplicate)
        [] -> do
            validated <- traverse validatePrefix (List.sort specifications)
            case duplicatePrefixGroups validated of
                duplicate : _ ->
                    Left duplicate
                [] ->
                    Right
                        (Map.fromList
                            [ (mount, prefix)
                            | (mount, _decoded, prefix) <- validated
                            ])
  where
    validatePrefix (mount, decoded) = do
        encoded <- traverse
            (\segment ->
                first
                    (InvalidHtmlMountPrefixSegment mount segment)
                    (urlSegment segment))
            decoded
        Right
            ( mount
            , decoded
            , ValidatedMountPrefix decoded encoded
            )

duplicatePrefixGroups
    :: [(SourceMountId, [Text], ValidatedMountPrefix)]
    -> [HtmlLayoutError]
duplicatePrefixGroups validated =
    [ DuplicateHtmlMountPrefix prefix (firstMount :| otherMounts)
    | (prefix, mounts) <-
        Map.toAscList
            (Map.fromListWith (<>)
                [ (decoded, [mount])
                | (mount, decoded, _prefix) <- validated
                ])
    , firstMount : secondMount : remainingMounts <-
        [List.sort mounts]
    , let otherMounts = secondMount : remainingMounts
    ]

duplicateValues :: Ord a => [a] -> [a]
duplicateValues values =
    [ value
    | (value, multiplicity) <-
        Map.toAscList
            (Map.fromListWith (+)
                [(value, 1 :: Int) | value <- values])
    , multiplicity > 1
    ]

makePageRoute
    :: Map SourceMountId ValidatedMountPrefix
    -> ResolvedSource
    -> Either HtmlLayoutError (ResolvedSource, HtmlRoute)
makePageRoute prefixes source = do
    prefix <- case Map.lookup (resolvedSourceMount source) prefixes of
        Nothing ->
            Left
                (MissingHtmlMountPrefix
                    (resolvedSourceMount source))
        Just found ->
            Right found
    let sourceComponents =
            Text.splitOn
                "/"
                (Text.pack
                    (safeRelativePathFilePath
                        (resolvedSourceRelativePath source)))
        destinationComponents =
            replaceFinalComponent
                (\component ->
                    dropFinalExtension component <> ".html")
                sourceComponents
        urlComponents =
            replaceFinalComponent
                dropFinalExtension
                sourceComponents
        ValidatedMountPrefix decodedPrefix encodedPrefix =
            prefix
        owner = HtmlPage source
    encodedPageComponents <-
        encodeRouteSegments owner urlComponents
    route <-
        makeRoute
            owner
            (decodedPrefix <> destinationComponents)
            (encodedPrefix <> encodedPageComponents)
    Right (source, route)

replaceFinalComponent :: (a -> a) -> [a] -> [a]
replaceFinalComponent transform components =
    case reverse components of
        [] ->
            []
        final : precedingReversed ->
            reverse precedingReversed <> [transform final]

dropFinalExtension :: Text -> Text
dropFinalExtension component =
    case Text.breakOnEnd "." component of
        ("", _suffix) ->
            component
        (".", _suffix) ->
            component
        (prefix, _suffix) ->
            Text.dropEnd 1 prefix

makeRoute
    :: HtmlRouteOwner
    -> [Text]
    -> [UrlSegment]
    -> Either HtmlLayoutError HtmlRoute
makeRoute owner destinationComponents encodedUrlComponents = do
    let destinationSpelling =
            List.intercalate
                "/"
                (Text.unpack <$> destinationComponents)
    destination <-
        first
            (InvalidHtmlRouteDestination
                owner
                destinationSpelling)
            (safeRelativePath destinationSpelling)
    Right
        HtmlRoute
            { routeDestination = destination
            , routeUrlPath = UrlPath encodedUrlComponents
            }

encodeRouteSegments
    :: HtmlRouteOwner
    -> [Text]
    -> Either HtmlLayoutError [UrlSegment]
encodeRouteSegments owner =
    traverse
        (\decoded ->
            first
                (InvalidHtmlRouteSegment owner decoded)
                (urlSegment decoded))

collectUrlCollisions
    :: [(HtmlRouteOwner, HtmlRoute)]
    -> [HtmlUrlRouteCollision]
collectUrlCollisions ownedRoutes =
    [ HtmlUrlRouteCollision path owners
    | (path, collidingOwners) <-
        Map.toAscList
            (Map.fromListWith (<>)
                [ (routeUrlPath route, [owner])
                | (owner, route) <- ownedRoutes
                ])
    , owners <-
        collisionOwners collidingOwners
    ]

collectDestinationCollisions
    :: [(HtmlRouteOwner, HtmlRoute)]
    -> [HtmlDestinationRouteCollision]
collectDestinationCollisions ownedRoutes =
    [ HtmlDestinationRouteCollision destination owners
    | (destination, collidingOwners) <-
        Map.toAscList
            (Map.fromListWith (<>)
                [ (routeDestination route, [owner])
                | (owner, route) <- ownedRoutes
                ])
    , owners <-
        collisionOwners collidingOwners
    ]

collectNestedDestinationCollisions
    :: [(HtmlRouteOwner, HtmlRoute)]
    -> [HtmlDestinationRouteCollision]
collectNestedDestinationCollisions ownedRoutes =
    take 1
        [ NestedHtmlDestinationRouteCollision
            ancestor
            ancestorOwner
            descendant
            descendantOwner
        | ( (ancestorComponents, ancestor, ancestorOwner)
            , (descendantComponents, descendant, descendantOwner)
            ) <- zip destinations (drop 1 destinations)
        , strictComponentPrefix ancestorComponents descendantComponents
        ]
  where
    destinations =
        List.sort
            [ ( relativePathComponents destination
              , destination
              , owner
              )
            | (owner, route) <- ownedRoutes
            , let destination = routeDestination route
            ]

relativePathComponents :: SafeRelativePath -> [FilePath]
relativePathComponents =
    Posix.splitDirectories . safeRelativePathFilePath

strictComponentPrefix :: [FilePath] -> [FilePath] -> Bool
strictComponentPrefix possibleAncestor possibleDescendant =
    length possibleAncestor < length possibleDescendant
        && possibleAncestor `List.isPrefixOf` possibleDescendant

collisionOwners :: [HtmlRouteOwner] -> [NonEmpty HtmlRouteOwner]
collisionOwners owners =
    case List.sort owners of
        firstOwner : secondOwner : rest ->
            [firstOwner :| (secondOwner : rest)]
        _ ->
            []

dropCommonPrefix :: Eq a => [a] -> [a] -> ([a], [a])
dropCommonPrefix (left : lefts) (right : rights)
    | left == right =
        dropCommonPrefix lefts rights
dropCommonPrefix left right =
    (left, right)


htmlAssetComponents :: HtmlAsset -> [Text]
htmlAssetComponents = \case
    HtmlSupportScriptAsset ->
        ["_static", "naproche-html.js"]
    HtmlStylesheetAsset ->
        ["_static", "naproche-html.css"]

percentEncodeUtf8 :: Text -> Text
percentEncodeUtf8 =
    Text.pack
        . concatMap encodeByte
        . ByteString.unpack
        . TextEncoding.encodeUtf8

encodeByte :: Word8 -> String
encodeByte byte
    | isUnreservedAscii byte =
        [chr (fromIntegral byte)]
    | otherwise =
        [ '%'
        , hexadecimalDigit (byte `div` 16)
        , hexadecimalDigit (byte `mod` 16)
        ]

isUnreservedAscii :: Word8 -> Bool
isUnreservedAscii byte =
    isAsciiUpper byte
        || isAsciiLower byte
        || isAsciiDigit byte
        || byte `elem` fmap (fromIntegral . fromEnum) ("-._~" :: String)

isAsciiUpper :: Word8 -> Bool
isAsciiUpper byte =
    byte >= 65 && byte <= 90

isAsciiLower :: Word8 -> Bool
isAsciiLower byte =
    byte >= 97 && byte <= 122

isAsciiDigit :: Word8 -> Bool
isAsciiDigit byte =
    byte >= 48 && byte <= 57

hexadecimalDigit :: Word8 -> Char
hexadecimalDigit value
    | value < 10 =
        chr (fromIntegral value + fromEnum '0')
    | otherwise =
        chr (fromIntegral value - 10 + fromEnum 'A')
