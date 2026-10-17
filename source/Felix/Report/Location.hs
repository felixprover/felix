{-# LANGUAGE DerivingStrategies #-}

module Felix.Report.Location
    ( SourceDescriptor
    , Location
    , LocationConstructionError(..)
    , sourceDescriptor
    , sourceDescriptorForPath
    , anonymousSourceDescriptor
    , sourceDescriptorDisplayPath
    , sourceDescriptorIdentityPath
    , mkLocationChecked
    , mkLocation
    , locSourceDescriptor
    , locFile
    , locLine
    , locColumn
    , fromSourcePosChecked
    , advanceSourceLocation
    , prettyLocation
    , prettyLocationPair
    , locationToText
    , preferKnownLocation
    , Locatable(..)
    , pattern Nowhere
    ) where

import Base
import Text.Megaparsec (PosState(..), reachOffset)
import Text.Megaparsec.Pos
    ( SourcePos(..)
    , defaultTabWidth
    , mkPos
    , unPos
    )
import Data.Bits
import Control.DeepSeq (NFData(..))
import Data.Text qualified as Text

-- | Immutable diagnostic provenance, retained only by its users. Anonymous
-- syntax has no physical source; neither case confers source/proof authority.
data SourceDescriptor
    = AnonymousSource
    | PhysicalSource !Text !Text
    deriving stock (Show, Eq, Ord)

instance NFData SourceDescriptor where
    rnf AnonymousSource = ()
    rnf (PhysicalSource identity display) = rnf identity `seq` rnf display

instance Hashable SourceDescriptor where
    hashWithSalt salt AnonymousSource = hashWithSalt salt (0 :: Int)
    hashWithSalt salt (PhysicalSource identity display) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` identity `hashWithSalt` display

sourceDescriptor :: FilePath -> FilePath -> SourceDescriptor
-- The presentation wire already uses this reserved pair for anonymous input.
sourceDescriptor "<anonymous>" "<anonymous>" = AnonymousSource
sourceDescriptor identity display = PhysicalSource (Text.pack identity) (Text.pack display)

sourceDescriptorForPath :: FilePath -> SourceDescriptor
sourceDescriptorForPath path = sourceDescriptor path path

anonymousSourceDescriptor :: SourceDescriptor
anonymousSourceDescriptor = AnonymousSource

sourceDescriptorDisplayPath :: SourceDescriptor -> FilePath
sourceDescriptorDisplayPath AnonymousSource = "<anonymous>"
sourceDescriptorDisplayPath (PhysicalSource _ display) = Text.unpack display

sourceDescriptorIdentityPath :: SourceDescriptor -> Maybe FilePath
sourceDescriptorIdentityPath AnonymousSource = Nothing
sourceDescriptorIdentityPath (PhysicalSource identity _) = Just (Text.unpack identity)

-- | Checked coordinates and their immutable source, or no source position.
-- Coordinates retain the previous 24-bit line / 24-bit column bounds.
-- Constructors and Generic are unavailable to clients.
data Location
    = SourceLocation !SourceDescriptor {-# UNPACK #-} !Word64
    | NoLocation
    deriving stock (Eq)

instance NFData Location where
    rnf NoLocation = ()
    rnf (SourceLocation source coordinates) = rnf source `seq` rnf coordinates

instance Hashable Location where
    hashWithSalt salt NoLocation = hashWithSalt salt (0 :: Int)
    hashWithSalt salt (SourceLocation source coordinates) =
        salt `hashWithSalt` (1 :: Int) `hashWithSalt` source `hashWithSalt` coordinates

-- Cross-source value ordering uses physical identity then display spelling.
-- Diagnostic aggregation retains source-graph order; it never sorts by this
-- instance. Within one source, coordinates keep their previous order.
instance Ord Location where
    compare NoLocation NoLocation = EQ
    compare NoLocation _ = GT
    compare _ NoLocation = LT
    compare (SourceLocation source left) (SourceLocation other right) =
        compare source other <> compare left right

data LocationConstructionError
    = LocationCoordinateOutOfRange !Int !Int
    deriving stock (Show, Eq)

lineShift :: Int
lineShift = 24

coordMask :: Word64
coordMask = 0xFFFFFF

mkLocationChecked
    :: SourceDescriptor
    -> Int
    -> Int
    -> Either LocationConstructionError Location
mkLocationChecked descriptor line column
    | line < 0
        || column < 0
        || lineWord > coordMask
        || columnWord > coordMask =
            Left (LocationCoordinateOutOfRange line column)
    | otherwise =
        Right (SourceLocation descriptor ((lineWord `shiftL` lineShift) .|. columnWord))
    where
        lineWord = fromIntegral line :: Word64
        columnWord = fromIntegral column :: Word64

mkLocation :: SourceDescriptor -> Int -> Int -> Location
mkLocation descriptor line column =
    either
        (impossible . ("mkLocation: " <>) . show)
        id
        (mkLocationChecked descriptor line column)

locSourceDescriptor :: Location -> Maybe SourceDescriptor
locSourceDescriptor NoLocation = Nothing
locSourceDescriptor (SourceLocation source _) = Just source

locFile :: Location -> FilePath
locFile = maybe "<nowhere>" sourceDescriptorDisplayPath . locSourceDescriptor

locLine :: Location -> Int
locLine NoLocation = -1
locLine (SourceLocation _ coordinates) = fromIntegral (coordinates `shiftR` lineShift)

locColumn :: Location -> Int
locColumn NoLocation = -1
locColumn (SourceLocation _ coordinates) = fromIntegral (coordinates .&. coordMask)

instance Show Location where
    showsPrec p loc =
        showParen (p > appPrec) $
            showString "Location {locFile = "
            . shows (locFile loc)
            . showString ", locLine = "
            . shows (locLine loc)
            . showString ", locColumn = "
            . shows (locColumn loc)
            . showString "}"
      where
        appPrec = 10

fromSourcePosChecked
    :: SourceDescriptor
    -> SourcePos
    -> Either LocationConstructionError Location
fromSourcePosChecked descriptor pos =
    mkLocationChecked
        descriptor
        (unPos (sourceLine pos))
        (unPos (sourceColumn pos))

-- | Advance a source location exactly as Megaparsec advances over the same
-- text. Source locations are one-based, tabs use Megaparsec's default tab
-- stops, and newline handling comes from the parser's stream instance.
advanceSourceLocation :: Location -> Text -> Location
advanceSourceLocation location consumed =
    case locSourceDescriptor location of
        Nothing -> location
        Just descriptor ->
            let initialState =
                    PosState
                        { pstateInput = consumed
                        , pstateOffset = 0
                        , pstateSourcePos =
                            SourcePos
                                (locFile location)
                                (mkPos (locLine location))
                                (mkPos (locColumn location))
                        , pstateTabWidth = defaultTabWidth
                        , pstateLinePrefix = ""
                        }
                (_line, finalState) =
                    reachOffset (Text.length consumed) initialState
            in either
                (impossible . ("advanceSourceLocation: " <>) . show)
                id
                (fromSourcePosChecked
                    descriptor
                    (pstateSourcePos finalState))

prettyLocation :: Location -> String
prettyLocation loc =
    locFile loc <> " " <> show (locLine loc) <> ":" <> show (locColumn loc)

-- | Render two locations together, qualifying equal display paths when they
-- refer to different physical files.
prettyLocationPair :: Location -> Location -> (String, String)
prettyLocationPair firstLocation secondLocation =
    if locFile firstLocation == locFile secondLocation
        && firstIdentity /= secondIdentity
        && isJust firstIdentity
        && isJust secondIdentity
        then
            ( qualify firstIdentity firstLocation
            , qualify secondIdentity secondLocation
            )
        else
            (prettyLocation firstLocation, prettyLocation secondLocation)
  where
    firstIdentity =
        presentationIdentity <$> locSourceDescriptor firstLocation
    secondIdentity =
        presentationIdentity <$> locSourceDescriptor secondLocation

    presentationIdentity source =
        fromMaybe (sourceDescriptorDisplayPath source) (sourceDescriptorIdentityPath source)

    qualify identity location =
        locFile location
            <> " (canonical "
            <> maybe "<unknown>" show identity
            <> ") "
            <> show (locLine location)
            <> ":"
            <> show (locColumn location)

locationToText :: Location -> Text
locationToText loc = Text.pack (prettyLocation loc)

preferKnownLocation :: Location -> Location -> Location
preferKnownLocation actual fallback
    | actual == Nowhere = fallback
    | otherwise = actual

-- | Things that have a location.
class Locatable a where
    locate :: a -> Location

pattern Nowhere :: Location
pattern Nowhere = NoLocation

instance Locatable Location where
    locate = id

instance Locatable a => Locatable [a] where
    locate []    = Nowhere
    locate (x:_) = locate x

instance Locatable a => Locatable (Maybe a) where
    locate Nothing  = Nowhere
    locate (Just x) = locate x

instance Locatable a => Locatable (NonEmpty a) where
    locate (x :| _) = locate x
