module PublicCarrierConstructor where

import Felix.Checking.GlobalTyping (GlobalTyping(GlobalTyping))

unavailableConstructor :: GlobalTyping global
unavailableConstructor = GlobalTyping (const Nothing)
