module ParsedSourceUpdate where

import Felix.Parsed.Module (ParsedModule, parsedModuleIdentifiedSource)
import Felix.Source.Content (IdentifiedLoadedSource)

replace :: IdentifiedLoadedSource -> ParsedModule -> ParsedModule
replace supplied original = original { parsedModuleIdentifiedSource = supplied }
