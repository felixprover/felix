{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}

module Felix.Test.Unit.Earley (unitTests) where

import Base
import Control.DeepSeq (rnf)
import Data.Text qualified as Text
import Felix.Parsed.Payload qualified as Payload
import Felix.Report.Location (anonymousSourceDescriptor)
import Felix.Syntax.Concrete qualified as Concrete
import Felix.Syntax.Earley qualified as Session
import Felix.Syntax.Interface qualified as Interface
import Felix.Syntax.Lexicon (builtins)
import Felix.Test.SourceScan.Adapter (scanTestSource)
import Test.Tasty
import Test.Tasty.HUnit
import Text.Earley qualified as Earley

type Grammar = forall r. Earley.Grammar r (Earley.Prod r String Char String)

unitTests :: TestTree
unitTests = testGroup "Earley sessions"
    [ testCase "preserves results and reports across independent chunks" isolation
    , testCase "preserves deferred concrete payloads and source locations" concreteIsolation
    , testCase "stops after consumer rejection without demanding later input" stopsAtRejection
    , testCase "does no grammar work for an empty module" emptyModule
    , testCase "scales across repeated inputs without changing results" scaling
    ]

letters :: Grammar
letters = pure (many (Earley.satisfy (== 'a')) Earley.<?> "letters")

leftRecursive :: Grammar
leftRecursive = mdo
    xs <- Earley.rule (((<>) <$> xs <*> ((:[]) <$> Earley.satisfy (== 'a'))) <|> pure "")
    pure xs

nullable :: Grammar
nullable = mdo
    xs <- Earley.rule (xs <|> pure "")
    pure xs

ambiguous :: Grammar
ambiguous = pure (pure "first" <|> pure "second" <|> pure "first")

isolation :: Assertion
isolation = do
    let check :: Grammar -> [String] -> Assertion
        check grammar inputs = do
            let observe (values, report) = (values, show report)
                expected = map (observe . Earley.fullParses (Earley.parser grammar)) inputs
                eager acc _ result = rnf (observe result) `seq` Right (result : acc)
                deferred acc _ result = length (fst result) `seq` Right (result : acc)
                run consume = fmap (map observe . reverse)
                    (Session.foldParses grammar id consume [] inputs :: Either () [([String], Earley.Report String String)])
            run eager @?= Right expected
            run deferred @?= Right expected
    for_ [[], ["", "a", "x", "aa", "ax", ""], ["x", "aa", "", "a", "ax"]] \inputs -> do
        check letters inputs
        check leftRecursive inputs
        check nullable inputs
        check ambiguous inputs

concreteIsolation :: Assertion
concreteIsolation = do
    delta <- either (assertFailure . show) pure (Interface.canonicalSyntaxDelta [])
    interface <- either (assertFailure . show) pure (Interface.moduleSyntaxInterface [] delta)
    chunks <- fmap concat $ for [1..32] \line -> do
        let source = Text.replicate line "\n"
                <> "\\begin{axiom}\\label{session}\n"
                <> (if line `mod` 5 == 0 then "$x \\unknown y$.\n" else "$x=x$.\n")
                <> "\\end{axiom}\n"
        either assertFailure (pure . snd)
            (scanTestSource anonymousSourceDescriptor "session.tex" source)
    let grammar = Concrete.grammar builtins
        -- Raw Eq/Show omit variable locations; the canonical codec retains them.
        blockBytes block = Payload.canonicalParsedPayloadBytes
            (Payload.canonicalParsedPayload [] [block] [] (Interface.moduleSyntaxAssertedId interface))
        observe (values, report) = (map (either show (show . blockBytes)) values, show report)
        consume acc _ result = length (fst result) `seq` Right (result : acc)
    for_ [chunks, reverse chunks, chunks <> reverse chunks] \inputs -> do
        let actual = Session.foldParses grammar id consume [] inputs
            expected = map (observe . Earley.fullParses (Earley.parser grammar)) inputs
        -- Observe payloads only after all chunks have run and the session has ended.
        fmap (map observe . reverse) actual @?= (Right expected :: Either () [([String], String)])

stopsAtRejection :: Assertion
stopsAtRejection = for_ [1..4 :: Int] \boundary -> do
    let consume n _ (values, report) = rnf (values, show report) `seq`
            if n + 1 == boundary then Left (n + 1) else Right (n + 1)
        inputs = replicate boundary "aaa" <> [error "read input after rejected validation"]
    Session.foldParses letters id consume 0 inputs @?= Left boundary

emptyModule :: Assertion
emptyModule =
    Session.foldParses (error "initialized grammar for empty module")
        id (\n _ (_ :: ([String], Earley.Report String String)) -> Right (n + 1))
        (0 :: Int) [] @?= (Right 0 :: Either () Int)

scaling :: Assertion
scaling = for_ [1, 8, 32, 128, 1024 :: Int] \count -> do
    let consume n _ (values, report) = rnf (values, show report) `seq` Right (n + 1)
    Session.foldParses letters id consume (0 :: Int) (replicate count "aaa")
        @?= (Right count :: Either () Int)
