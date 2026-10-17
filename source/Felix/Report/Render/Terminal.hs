{-# LANGUAGE NoImplicitPrelude #-}

-- | Plain, deterministic terminal layout for one primary diagnostic.
module Felix.Report.Render.Terminal
    ( terminalDiagnosticWidth
    , renderTerminalDiagnostic
    , renderTerminalDiagnosticWithWidth
    ) where

import Base hiding (pretty)
import Felix.Report.Diagnostic
import Felix.Report.Location

import Data.Text qualified as Text
import Prettyprinter
    ( Doc
    , LayoutOptions(..)
    , PageWidth(..)
    , defaultLayoutOptions
    , emptyDoc
    , hang
    , indent
    , layoutPretty
    , pretty
    , vsep
    , (<+>)
    )
import Prettyprinter.Render.Text (renderStrict)

-- | Batch diagnostics use one width in terminals, redirected output, and
-- tests.  Adaptive layout belongs to a later presentation layer.
terminalDiagnosticWidth :: Int
terminalDiagnosticWidth = 100

renderTerminalDiagnostic :: Diagnostic -> Text
renderTerminalDiagnostic =
    renderTerminalDiagnosticWithWidth terminalDiagnosticWidth

renderTerminalDiagnosticWithWidth :: Int -> Diagnostic -> Text
renderTerminalDiagnosticWithWidth width diagnostic =
    renderStrict
        (layoutPretty options (diagnosticDocument diagnostic))
  where
    options = defaultLayoutOptions
        { layoutPageWidth = AvailablePerLine (max 1 width) 1.0
        }

diagnosticDocument :: Diagnostic -> Doc ()
diagnosticDocument diagnostic =
    vsep
        ( [ header ]
            <> maybe [] (pure . locationDocument)
                (diagnosticPrimary diagnostic)
            <> [emptyDoc, diagnosticMessage diagnostic]
            <> (noteDocument <$> diagnosticNotes diagnostic)
            <> (helpDocument <$> diagnosticHelp diagnostic)
        )
  where
    header =
        pretty (severityText (diagnosticSeverity diagnostic)
            <> "[" <> diagnosticCodeText (diagnosticCode diagnostic) <> "]:")
            <+> pretty (diagnosticTitle diagnostic)

severityText :: DiagnosticSeverity -> Text
severityText = \case
    DiagnosticError -> "error"
    DiagnosticWarning -> "warning"

locationDocument :: Location -> Doc ()
locationDocument location =
    indent 2 (pretty ("-->" :: Text) <+> pretty (colonLocation location))

colonLocation :: Location -> Text
colonLocation location =
    Text.pack (locFile location)
        <> ":" <> Text.pack (show (locLine location))
        <> ":" <> Text.pack (show (locColumn location))

noteDocument :: Doc () -> Doc ()
noteDocument = hang 6 . (pretty ("note:" :: Text) <+>)

helpDocument :: Doc () -> Doc ()
helpDocument = hang 6 . (pretty ("help:" :: Text) <+>)
