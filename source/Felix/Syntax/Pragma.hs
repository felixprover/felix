{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Felix.Syntax.Pragma
    ( SourceMixfixLevel
    , sourceMixfixLevelValue
    , SyntaxPragma(..)
    , SyntaxPragmaProblem(..)
    , SyntaxPragmaError(..)
    , SyntaxPragmaLineEnding(..)
    , renderSyntaxPragmaError
    , parseSyntaxPragmaLine
    ) where

import Base

import Felix.Report.Location
import Felix.Syntax.Abstract (Associativity(..))

import Control.DeepSeq (NFData)
import Control.Monad (unless, when)
import Data.Bifunctor (first)
import Data.Char (ord)
import Data.Text qualified as Text
import Data.Word (Word8)


newtype SourceMixfixLevel = SourceMixfixLevel Word8
    deriving stock (Show, Eq, Ord)
    deriving newtype (NFData)

sourceMixfixLevelValue :: SourceMixfixLevel -> Word8
sourceMixfixLevelValue (SourceMixfixLevel level) =
    level

data SyntaxPragma = LocatedFixityPragma
    { syntaxPragmaLocation :: !Location
    , syntaxPragmaAssociativity :: !Associativity
    , syntaxPragmaLevel :: !SourceMixfixLevel
    } deriving stock (Show, Eq)

instance Locatable SyntaxPragma where
    locate = syntaxPragmaLocation

data SyntaxPragmaProblem
    = SyntaxPragmaMissingSpaceAfterPrefix
    | SyntaxPragmaMissingKeyword
    | SyntaxPragmaUnknownKeyword !Text
    | SyntaxPragmaMissingLevel
    | SyntaxPragmaInvalidLevel
    | SyntaxPragmaLevelOutOfRange
    | SyntaxPragmaTrailingContent
    | SyntaxPragmaLoneCarriageReturn
    deriving stock (Show, Eq)

data SyntaxPragmaError
    = InvalidSyntaxPragma !Location !SyntaxPragmaProblem
    | SyntaxPragmaLocationOutOfRange !FilePath !Int !Int
    deriving stock (Show, Eq)

-- | Physical line termination retained by source scanning until syntax
-- pragma interpretation is demanded.
data SyntaxPragmaLineEnding
    = SyntaxPragmaLineFeed
    | SyntaxPragmaCrLf
    | SyntaxPragmaEndOfFile
    deriving stock (Show, Eq)

renderSyntaxPragmaError :: SyntaxPragmaError -> Text
renderSyntaxPragmaError = \case
    InvalidSyntaxPragma location problem ->
        locationToText location
            <> ": "
            <> renderSyntaxPragmaProblem problem
    SyntaxPragmaLocationOutOfRange file line column ->
        Text.pack file
            <> ": syntax pragma location is out of range at "
            <> Text.pack (show line)
            <> ":"
            <> Text.pack (show column)

renderSyntaxPragmaProblem :: SyntaxPragmaProblem -> Text
renderSyntaxPragmaProblem = \case
    SyntaxPragmaMissingSpaceAfterPrefix ->
        "expected horizontal space after %!"
    SyntaxPragmaMissingKeyword ->
        "missing syntax pragma keyword"
    SyntaxPragmaUnknownKeyword keyword ->
        "unknown syntax pragma keyword " <> Text.pack (show keyword)
    SyntaxPragmaMissingLevel ->
        "missing syntax pragma level"
    SyntaxPragmaInvalidLevel ->
        "syntax pragma level must use ASCII decimal digits"
    SyntaxPragmaLevelOutOfRange ->
        "syntax pragma level must be between 0 and 7"
    SyntaxPragmaTrailingContent ->
        "unexpected trailing syntax pragma content"
    SyntaxPragmaLoneCarriageReturn ->
        "a syntax pragma line must end with LF, CRLF, or end of file"

parseSyntaxPragmaLine
    :: SourceDescriptor
    -> FilePath
    -> Int
    -> SyntaxPragmaLineEnding
    -> Text
    -> Either SyntaxPragmaError SyntaxPragma
parseSyntaxPragmaLine descriptor file lineNumber lineEnding rawLine = do
    let horizontalPrefix =
            Text.takeWhile isHorizontalSpace rawLine
        column =
            Text.length horizontalPrefix + 1
    location <-
        first
            (const
                (SyntaxPragmaLocationOutOfRange
                    file
                    lineNumber
                    column))
            (mkLocationChecked descriptor lineNumber column)
    let invalid
            :: SyntaxPragmaProblem
            -> Either SyntaxPragmaError a
        invalid =
            Left . InvalidSyntaxPragma location
        afterPrefix =
            Text.drop 2
                (Text.dropWhile isHorizontalSpace rawLine)
    when
        (lineEnding == SyntaxPragmaEndOfFile
            && Text.isSuffixOf "\r" rawLine)
        (invalid SyntaxPragmaLoneCarriageReturn)
    afterPrefixSpace <-
        case Text.uncons afterPrefix of
            Nothing ->
                invalid SyntaxPragmaMissingKeyword
            Just (char, _)
                | not (isHorizontalSpace char) ->
                    invalid SyntaxPragmaMissingSpaceAfterPrefix
            Just{} ->
                Right (Text.dropWhile isHorizontalSpace afterPrefix)
    when
        (Text.null afterPrefixSpace)
        (invalid SyntaxPragmaMissingKeyword)
    let (keyword, afterKeyword) =
            Text.break isHorizontalSpace afterPrefixSpace
    associativity <-
        case keyword of
            "infixl" ->
                Right LeftAssoc
            "infixr" ->
                Right RightAssoc
            "infix" ->
                Right NonAssoc
            _ ->
                invalid (SyntaxPragmaUnknownKeyword keyword)
    afterKeywordSpace <-
        case Text.uncons afterKeyword of
            Nothing ->
                invalid SyntaxPragmaMissingLevel
            Just{} ->
                Right (Text.dropWhile isHorizontalSpace afterKeyword)
    when
        (Text.null afterKeywordSpace)
        (invalid SyntaxPragmaMissingLevel)
    let (digits, trailing) =
            Text.span isAsciiDigit afterKeywordSpace
    when
        (Text.null digits)
        (invalid SyntaxPragmaInvalidLevel)
    level <-
        maybe
            (invalid SyntaxPragmaLevelOutOfRange)
            (Right . SourceMixfixLevel)
            (sourceLevel digits)
    unless
        (Text.null (Text.dropWhile isHorizontalSpace trailing))
        (invalid SyntaxPragmaTrailingContent)
    pure
        LocatedFixityPragma
            { syntaxPragmaLocation = location
            , syntaxPragmaAssociativity = associativity
            , syntaxPragmaLevel = level
            }

isHorizontalSpace :: Char -> Bool
isHorizontalSpace char =
    char == ' ' || char == '\t'

isAsciiDigit :: Char -> Bool
isAsciiDigit char =
    '0' <= char && char <= '9'

sourceLevel :: Text -> Maybe Word8
sourceLevel =
    Text.foldl' step (Just 0)
  where
    step Nothing _ =
        Nothing
    step (Just current) char =
        let next =
                current * 10
                    + fromIntegral (ord char - ord '0')
        in
            if next <= 7
                then Just next
                else Nothing
