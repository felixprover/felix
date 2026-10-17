module InternalCarrierImport where

import Felix.Checking.GlobalTyping.Internal (GlobalTyping(..))

unavailableConstructor :: GlobalTyping global
unavailableConstructor = GlobalTyping (const Nothing)
