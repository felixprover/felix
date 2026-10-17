{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- | Browser-facing routing authority for one rendered HTML page.
module Felix.Render.Html.Context
    ( HtmlRenderEnvironment
    , htmlRenderEnvironment
    , HtmlRenderContext
    , HtmlRenderContextError(..)
    , htmlRenderContext
    , htmlRenderContextFromEnvironment
    , htmlRenderContextAtRoute
    , htmlCurrentSource
    , htmlCurrentPageUrl
    , htmlCurrentPageLabel
    , htmlRouteNamespaces
    , htmlSourceUrl
    , htmlSourceLabel
    , htmlSourcePageHref
    , htmlSourceFragmentHref
    , htmlAssetHref
    , htmlSupportScriptHref
    , htmlStylesheetHref
    , htmlDeclarationIndexHref
    ) where

import Base
import Felix.Source
import Felix.Render.Html.Layout

import Control.Exception (Exception)
import Data.Map.Strict qualified as Map
import Data.Text qualified as Text


data HtmlRenderContextError
    = HtmlCurrentSourceNotRouted !ResolvedSource
    | HtmlReferencedSourceNotRouted !ResolvedSource
    deriving stock (Show, Eq)

instance Exception HtmlRenderContextError

data HtmlRenderContext = HtmlRenderContext
    { contextCurrentSource :: !ResolvedSource
    , contextCurrentPageUrl :: !UrlPath
    , contextEnvironment :: !HtmlRenderEnvironment
    }
    deriving stock (Show, Eq)

data HtmlRenderEnvironment = HtmlRenderEnvironment
    { environmentSourceUrls :: !(Map ResolvedSource UrlPath)
    , environmentRouteNamespaces :: !(Map SourceMountId UrlPath)
    , environmentAssetUrls :: !(Map HtmlAsset UrlPath)
    , environmentDeclarationIndexUrl :: !UrlPath
    }
    deriving stock (Show, Eq)

htmlRenderEnvironment :: HtmlLayout -> HtmlRenderEnvironment
htmlRenderEnvironment layout =
    HtmlRenderEnvironment
        { environmentSourceUrls =
            Map.fromList
                [ (source, routeUrlPath route)
                | (source, route) <- htmlPageRoutes layout
                ]
        , environmentRouteNamespaces =
            htmlMountUrlPrefixes layout
        , environmentAssetUrls =
            Map.fromList
                [ (asset, routeUrlPath (htmlAssetRoute layout asset))
                | asset <- allHtmlAssets
                ]
        , environmentDeclarationIndexUrl =
            routeUrlPath (htmlDeclarationIndexRoute layout)
        }

htmlRenderContext
    :: HtmlLayout
    -> ResolvedSource
    -> Either HtmlRenderContextError HtmlRenderContext
htmlRenderContext layout =
    htmlRenderContextFromEnvironment
        (htmlRenderEnvironment layout)

htmlRenderContextFromEnvironment
    :: HtmlRenderEnvironment
    -> ResolvedSource
    -> Either HtmlRenderContextError HtmlRenderContext
htmlRenderContextFromEnvironment environment currentSource = do
    currentPageUrl <-
        maybe
            (Left (HtmlCurrentSourceNotRouted currentSource))
            Right
            (Map.lookup
                currentSource
                (environmentSourceUrls environment))
    Right
        HtmlRenderContext
            { contextCurrentSource = currentSource
            , contextCurrentPageUrl = currentPageUrl
            , contextEnvironment = environment
            }

-- | Render a synthetic page at a reserved route while retaining the selected
-- root as its source owner for labels and source-relative navigation.
htmlRenderContextAtRoute
    :: HtmlRenderEnvironment
    -> ResolvedSource
    -> HtmlRoute
    -> Either HtmlRenderContextError HtmlRenderContext
htmlRenderContextAtRoute environment owner route = do
    _ownerUrl <-
        maybe
            (Left (HtmlCurrentSourceNotRouted owner))
            Right
            (Map.lookup owner (environmentSourceUrls environment))
    Right
        HtmlRenderContext
            { contextCurrentSource = owner
            , contextCurrentPageUrl = routeUrlPath route
            , contextEnvironment = environment
            }

htmlCurrentSource :: HtmlRenderContext -> ResolvedSource
htmlCurrentSource =
    contextCurrentSource

htmlCurrentPageUrl :: HtmlRenderContext -> UrlPath
htmlCurrentPageUrl =
    contextCurrentPageUrl

htmlCurrentPageLabel :: HtmlRenderContext -> Text
htmlCurrentPageLabel context =
    resolvedSourceLabel (contextCurrentSource context)

htmlRouteNamespaces
    :: HtmlRenderContext
    -> Map SourceMountId UrlPath
htmlRouteNamespaces =
    environmentRouteNamespaces . contextEnvironment

htmlSourceUrl
    :: HtmlRenderContext
    -> ResolvedSource
    -> Either HtmlRenderContextError UrlPath
htmlSourceUrl HtmlRenderContext{contextEnvironment} source =
    maybe
        (Left (HtmlReferencedSourceNotRouted source))
        Right
        (Map.lookup source (environmentSourceUrls contextEnvironment))

htmlSourceLabel
    :: HtmlRenderContext
    -> ResolvedSource
    -> Either HtmlRenderContextError Text
htmlSourceLabel context source = do
    _url <- htmlSourceUrl context source
    Right (resolvedSourceLabel source)

htmlSourcePageHref
    :: HtmlRenderContext
    -> ResolvedSource
    -> Either HtmlRenderContextError Text
htmlSourcePageHref context source =
    renderRelativeUrlPath
        (contextCurrentPageUrl context)
        <$> htmlSourceUrl context source

htmlSourceFragmentHref
    :: HtmlRenderContext
    -> ResolvedSource
    -> Text
    -> Either HtmlRenderContextError Text
htmlSourceFragmentHref context source fragment = do
    target <- htmlSourceUrl context source
    let encodedFragment =
            renderUrlFragment fragment
    Right
        (if target == contextCurrentPageUrl context
            then encodedFragment
            else
                renderRelativeUrlPath
                    (contextCurrentPageUrl context)
                    target
                    <> encodedFragment)

htmlAssetHref :: HtmlRenderContext -> HtmlAsset -> Text
htmlAssetHref context asset =
    renderRelativeUrlPath
        (contextCurrentPageUrl context)
        ( fromMaybe
            (impossible ("HTML render environment is missing asset " <> show asset))
            (Map.lookup
                asset
                (environmentAssetUrls (contextEnvironment context)))
        )

htmlSupportScriptHref :: HtmlRenderContext -> Text
htmlSupportScriptHref context =
    htmlAssetHref context HtmlSupportScriptAsset

htmlStylesheetHref :: HtmlRenderContext -> Text
htmlStylesheetHref context =
    htmlAssetHref context HtmlStylesheetAsset

htmlDeclarationIndexHref :: HtmlRenderContext -> Text
htmlDeclarationIndexHref context =
    renderRelativeUrlPath
        (contextCurrentPageUrl context)
        (environmentDeclarationIndexUrl
            (contextEnvironment context))

resolvedSourceLabel :: ResolvedSource -> Text
resolvedSourceLabel source =
    sourceMountIdText (resolvedSourceMount source)
        <> ":"
        <> Text.pack
            (safeRelativePathFilePath
                (resolvedSourceRelativePath source))
