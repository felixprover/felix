module CalculationLawUpdate where

import Felix.Checking.Calculation
import Felix.Checking.Semantic (SemanticRelationComposition)

bad :: SemanticRelationComposition -> CheckedCompositionLaw -> CheckedCompositionLaw
bad metadata law = law {compositionLawMetadata = metadata}
