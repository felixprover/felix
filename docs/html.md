# HTML output

## Generating and viewing pages

Add `--html` to a verification command:

```sh
stack exec felix -- library/set.tex --html
```

Felix writes the pages to `./html` after verification and notation checks
succeed. The export includes the selected theory and all its imports. The
selected theory's page links to the full list of theories and a declaration
index. Each page shows its imports and the theories that import it within
this export. The index has optional JavaScript filters; links also work
without JavaScript.

To browse the export locally with the repository's [Caddyfile](../Caddyfile),
run this from the repository root:

```sh
caddy run --config Caddyfile
```

Open `http://localhost:1111` and select a theory page. The configuration
handles Felix's links, which omit the `.html` extension.

Each export replaces the contents of `html/`. Keep handwritten pages and
other files elsewhere. Missing notation or a rendering failure leaves the
previous export unchanged.

## Defining notation

The file [library/lexicon.tsv](../library/lexicon.tsv) defines how notation
appears in HTML. If you use a different library through `NAPROCHE_LIB`, edit
that library's `lexicon.tsv` instead. These entries change the display;
mathematical notation and its meaning are declared in the Felix source.

Each row has four columns separated by **literal tabs**, with no header:

1. **Category:** the kind of notation, listed below.
2. **Marker:** the notation's identifier, usually its declaration label.
3. **Arity:** the number of arguments passed to the template.
4. **Template:** the MathML used to display it.

For example, `\groupHomSet{G}{H}` is declared with the label `group_hom_set`.
This row displays it as `Hom(G,H)`:

```tsv
operator	group_hom_set	2	<mi>Hom</mi><mo>(</mo><x1/><mo>,</mo><x2/><mo>)</mo>
```

`<x1/>` inserts the first argument and `<x2/>` the second. Slots are numbered
from 1 and must not exceed the arity. The template uses MathML, not LaTeX:
`<mi>` marks a name, `<mo>` an operator or delimiter, and `<mn>` a number.
Use `<msub>` and `<msup>` for subscripts and superscripts, and `<mrow>` to
group several elements. Write `&lt;` for a literal less-than sign in markup.

| Category | Use | Arity |
| --- | --- | --- |
| `operator` | Term notation, such as `\groupHomSet{G}{H}` | Number of argument positions in the notation |
| `relation` | A relation sign, such as `\subseteq` | Parameters of the sign, excluding its left and right operands |
| `predicate` | A prefix predicate | Number of predicate arguments |
| `phrase` | A symbolic phrase or a bare commentary command | Always 0 |
| `structop` | A structure field | 1 with an explicit structure, 0 when it is omitted |

A relation template supplies only the sign. For example, the row for
`\subseteq` has no slots; Felix places the two operands around it:

```tsv
relation	subseteq	0	<mo>⊆</mo>
```

The category, marker, and arity together identify a row. To change existing
notation, edit its row rather than adding a duplicate. A missing-notation
message gives the category, marker, and arity that Felix needs.

### Structure fields

For `structop`, the marker is the field command without its backslash.
An explicit structure is the template's single argument. These rows display
`\opens` and `\opens[X]` separately:

```tsv
structop	opens	0	<mi mathvariant="script">O</mi>
structop	opens	1	<msub><mi mathvariant="script">O</mi><x1/></msub>
```

The second template places `X` in a subscript. Supply both rows if you use
both forms. The template does not determine which structure an omitted
argument refers to; the usual [structure rules](structures.md) still apply.

### Commentary symbols

A bare command used only in commentary can have a `phrase` entry without a
formal declaration. Use its command name without the backslash as the marker:

```tsv
phrase	teeone	0	<msub><mi>T</mi><mn>1</mn></msub>
```

You can then write `$\teeone$` in commentary to display a subscripted T.
For a phrase that already has a formal declaration, use its declared marker.

## Writing commentary

Section headings and prose appear alongside formal declarations in source
order. Commentary supports basic formatting and references such as `\ref`,
`\cref`, and `\obv`:

```latex
\section{Set equality}

We use \emph{extensionality}; see \ref{setext}.
The two inclusions are \(A\subseteq B\) and \(B\subseteq A\).
```

References link to declarations and offer previews. A reference in commentary
has no effect on a formal proof. A formal declaration may also have a title,
as in `\begin{proposition}[Composition]\label{composition}`; its label still
identifies the declaration for links and citations.

Use `$...$` or `\(...\)` for inline mathematics, and `\[...\]` for display
mathematics. Felix produces MathML directly. It supports a subset of LaTeX,
including Greek letters, fractions written with a slash, subscripts,
superscripts, and familiar operators. For example:

```latex
\[
    x\mapsto axa^{-1}
\]
```

Use braces for a multi-character subscript or exponent, as in `x^{12}`.
`$$...$$` is not supported.

Declared notation can appear inside commentary mathematics and uses the same
rendering templates as formal statements. For example, `x\mapsto\pow{A}`
works. Each declared command must still accept its complete argument syntax;
`x\mapsto\pow{A^{-1}}` works only if that `\pow` application is valid Felix
syntax in the current theory.

Unsupported commentary remains visible as source text with a warning.
Declared notation must still parse unambiguously. Displayed commentary
mathematics is not a checked assertion.

## Fixing rendering errors

Every verification checks the notation file, even without `--html` and when
proofs are reused from the store. `--parseonly` skips these checks. Editing
only the notation file does not invalidate unchanged proofs; rerun the same
verification command to check the new display.

For a missing hint, add the requested category, marker, and arity. For an
invalid row, check the tabs, duplicate entries, arity, and slot numbers.
Missing hints cause exit status 1; an unreadable or malformed notation file
causes exit status 2.
