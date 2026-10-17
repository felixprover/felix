{-# LANGUAGE NoImplicitPrelude #-}

-- | Lowercase hexadecimal byte presentation.
module Felix.Text.Hex (lowerHexText) where

import Base

import Data.ByteArray.Encoding (Base(Base16), convertToBase)
import Data.ByteString (ByteString)
import Data.Text.Encoding qualified as Text


lowerHexText :: ByteString -> Text
lowerHexText =
    Text.decodeUtf8 . convertToBase Base16
