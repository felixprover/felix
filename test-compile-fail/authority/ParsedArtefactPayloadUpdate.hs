module ParsedArtefactPayloadUpdate where

import Felix.Parsed.Payload (ParsedArtefact, parsedArtefactPayload, CanonicalParsedPayload)

replace :: CanonicalParsedPayload -> ParsedArtefact -> ParsedArtefact
replace supplied original = original { parsedArtefactPayload = supplied }
