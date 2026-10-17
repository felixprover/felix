module Felix.Test.Unit (fastTests, acceptanceTests) where


import Felix.Test.Unit.Abstract qualified as Abstract
import Felix.Test.Unit.Backend qualified as Backend
import Felix.Test.Unit.Binding qualified as Binding
import Felix.Test.Unit.BoundedInteger qualified as BoundedInteger
import Felix.Test.Unit.Calculation qualified as Calculation
import Felix.Test.Unit.CommandLine qualified as CommandLine
import Felix.Test.Unit.Concrete qualified as Concrete
import Felix.Test.Unit.Conversion qualified as Conversion
import Felix.Test.Unit.Core qualified as Core
import Felix.Test.Unit.Declaration qualified as Declaration
import Felix.Test.Unit.Elaboration qualified as Elaboration
import Felix.Test.Unit.Earley qualified as Earley
import Felix.Test.Unit.Foundation qualified as Foundation
import Felix.Test.Unit.Html qualified as Html
import Felix.Test.Unit.HtmlLayout qualified as HtmlLayout
import Felix.Test.Unit.HtmlMarkup qualified as HtmlMarkup
import Felix.Test.Unit.HtmlOutput qualified as HtmlOutput
import Felix.Test.Unit.Identity qualified as Identity
import Felix.Test.Unit.Datatype qualified as Datatype
import Felix.Test.Unit.Recursion qualified as Recursion
import Felix.Test.Unit.CodecAdmission qualified as CodecAdmission
import Felix.Test.Unit.Kernel qualified as Kernel
import Felix.Test.Unit.LibraryQuality qualified as LibraryQuality
import Felix.Test.Unit.Lexicon qualified as Lexicon
import Felix.Test.Unit.Location qualified as Location
import Felix.Test.Unit.LooseDeduction qualified as LooseDeduction
import Felix.Test.Unit.Materialization qualified as Materialization
import Felix.Test.Unit.MathCodec qualified as MathCodec
import Felix.Test.Unit.Module qualified as Module
import Felix.Test.Unit.Notion qualified as Notion
import Felix.Test.Unit.Obvious qualified as Obvious
import Felix.Test.Unit.OutputPlan qualified as OutputPlan
import Felix.Test.Unit.ParsedPayload qualified as ParsedPayload
import Felix.Test.Unit.Preparation qualified as Preparation
import Felix.Test.Unit.Provers qualified as Provers
import Felix.Test.Unit.Record qualified as Record
import Felix.Test.Unit.Semantic qualified as Semantic
import Felix.Test.Unit.Source qualified as Source
import Felix.Test.Unit.SourceScanBenchmark qualified as SourceScanBenchmark
import Felix.Test.Unit.Store qualified as Store
import Felix.Test.Unit.StructureSchema qualified as StructureSchema
import Felix.Test.Unit.Token qualified as Token
import Test.Tasty

fastTests :: TestTree
fastTests = testGroup "unit tests"
    [ Abstract.unitTests
    , Backend.unitTests
    , Binding.unitTests
    , BoundedInteger.unitTests
    , Calculation.unitTests
    , CommandLine.unitTests
    , Concrete.unitTests
    , Conversion.unitTests
    , Core.unitTests
    , Declaration.unitTests
    , Elaboration.unitTests
    , Earley.unitTests
    , Foundation.unitTests
    , Identity.unitTests
    , Datatype.unitTests
    , Recursion.unitTests
    , CodecAdmission.unitTests
    , Html.unitTests
    , HtmlLayout.unitTests
    , HtmlMarkup.unitTests
    , HtmlOutput.unitTests
    , Kernel.unitTests
    , LibraryQuality.unitTests
    , Lexicon.unitTests
    , Location.unitTests
    , LooseDeduction.unitTests
    , Materialization.unitTests
    , MathCodec.unitTests
    , Module.fastTests
    , Notion.unitTests
    , Obvious.unitTests
    , OutputPlan.unitTests
    , ParsedPayload.unitTests
    , Preparation.unitTests
    , Provers.unitTests
    , Record.unitTests
    , Semantic.unitTests
    , Source.unitTests
    , SourceScanBenchmark.unitTests
    , Store.unitTests
    , StructureSchema.unitTests
    , Token.unitTests
    ]

acceptanceTests :: TestTree
acceptanceTests = Module.acceptanceTests
