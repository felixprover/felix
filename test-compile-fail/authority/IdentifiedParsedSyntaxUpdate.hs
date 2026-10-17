module IdentifiedParsedSyntaxUpdate where

import Felix.Parsed.Module (IdentifiedParsedModule, identifiedParsedModuleSyntaxInterface)
import Felix.Syntax.Interface (ModuleSyntaxInterface)

replace :: ModuleSyntaxInterface -> IdentifiedParsedModule -> IdentifiedParsedModule
replace supplied original = original { identifiedParsedModuleSyntaxInterface = supplied }
