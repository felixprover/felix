# Structures in Felix

Felix structures are records represented as sets. The root `record` has no
required fields; `onesorted structure` adds a carrier. A structure phrase such
as “group” specifies the fields and laws a record must satisfy. The record,
its carrier, and its operations are separate mathematical objects.

## Declaring a structure

A declaration starts from `record`, `onesorted structure`, or one or more
existing structure phrases. Fields are introduced after `equipped with`; laws
follow after `such that`.

```tex
\begin{struct}\label{pointed_magma}
    A pointed magma $A$ is a magma equipped with
    \begin{enumerate}
        \item\label{pointed_magma_point}
            a point $\point[A]\in\carrier[A]$;
    \end{enumerate}
    such that
    \begin{enumerate}
        \item\label{pointed_magma_idempotent}
            $\mul[A](\point[A],\point[A])=\point[A]$.
    \end{enumerate}
\end{struct}
```

Only descendants of `onesorted structure` have `\carrier`. They inherit this
field; declaring a new field with that name is rejected. A child may add laws
without adding fields. Use `record` when there is no distinguished carrier.

For `A` declared as a one-sorted structure, `$x\in A$` means
`$x\in\carrier[A]$`. For a record without a carrier, name the intended
set-valued field explicitly.

A mathematical operation field is a set-coded function graph. Its declaration
should give its exact domain and codomain:

```tex
$\mul[A]:\carrier[A]\times\carrier[A]\to\carrier[A]$
```

Use ordinary application, such as `\mul[A](x,y)`, for these operations.
Logical functions of type `\Set\to\Set` use the separate `\Apply{F}{x}`
syntax.

If a field needs no restriction beyond being a set, write:

```tex
\item\label{pointed_magma_payload}
    a set $\payload[A]$;
```

The variable in brackets must be the structure being declared (`A` here).
A field without a specification may omit the brackets and description:

```tex
\item a set $\payload$;
\item $\payload$;
```

End every field declaration with a semicolon. Labels and descriptive prose
are optional. The prose alone imposes no mathematical requirement: write the
domain and codomain of an operation explicitly.

A child may add requirements on an inherited field in its laws, but may not
redeclare or replace the field. Multiple parents can share inherited fields;
each shared field occurs only once, and incompatible inheritance is rejected.
A child may combine parents with and without carriers. Parent order affects
positional record construction, described below, but not the inherited laws.

## Named field laws

Felix generates theorems for the fields of constructed records and reducts.
Their names use the field name without its leading backslash. For example,
a structure labeled `pointed_magma` has
`pointed_magmaaggregateprojection_point` for its `\point` field and
`pointed_magmareductprojection_carrier` for its inherited carrier.
These names continue to refer to the same fields if you reorder fields or
parents. Use the field names rather than numeric suffixes when citing them.

## Named inheritance laws

An inheritance theorem is named `<child label>inherit_<ancestor label>` when
the ancestor is unambiguous. For example,
`groupinherit_monoid` names the implication from a group to a monoid. Written
parent order does not change the name.

When a declaration inherits the same parameterized parent at different
arguments, label each complete direct application explicitly:

```tex
\begin{struct}\label{biaction}
    Let $R,S$ be scalar bases.
    A biaction $M$ over $R$ and $S$ is
    a left action over $R$ \label{biaction_left}
    and a left action over $S$ \label{biaction_right}.
\end{struct}
```

Cite these inheritance facts as `biaction_left` and `biaction_right`. Distinct
labels are required to distinguish the two applications. For an ambiguous
ancestor further up the hierarchy, use a direct-parent theorem followed by
that parent's inheritance theorems.

## Structure parameters

Parameters constrain a structure without becoming record fields. They are
declared before the structure sentence:

```tex
\begin{struct}\label{coordinate_record}
    Let $X$ be a set.
    A coordinate record $R$ on $X$ is a record equipped with
    \begin{enumerate}
        \item a set $\atlas[R]$;
    \end{enumerate}
    such that
    \begin{enumerate}
        \item $\atlas[R]\subseteq X$.
    \end{enumerate}
\end{struct}
```

Here `X` is a parameter, `\atlas[R]` is the sole stored field, and the subset
condition is a law. There is no carrier. Equality of exact coordinate records
depends on their atlas fields, not on which parameter was used to describe
them. The same distinction applies to one-sorted structures:

```tex
\begin{struct}\label{left_module}
    Let $R$ be a ring.
    A left module $M$ over $R$ is a commutative group equipped with
    \begin{enumerate}
        \item\label{module_scalar_graph}
            a scalar multiplication
            $\scalarMul[M]:
                \carrier[R]\times\carrier[M]\to\carrier[M]$;
    \end{enumerate}
    such that
    \begin{enumerate}
        % module laws
    \end{enumerate}
\end{struct}
```

“`M` is a left module over `R`” includes the requirement that `R` is a ring.
Parameters affect record equality only through the stored field values.

## Structure assumptions and omitted operations

A structure assumption may introduce one subject with the singular phrase or
several subjects with its plural:

```tex
Let $G$ be a group.
Let $R,S$ be records.
Let $G,H$ be groups.
Let $M,N$ be left modules over $R$.
Let $G,H$ be finite groups.
```

The singular form uses the indefinite article; the grouped form requires at
least two displayed variables, omits the article, and uses the structure
noun's plural. Thus `Let $G$ be groups` and `Let $G,H$ be a group` are both
rejected.

Each named variable receives the stated structure and modifiers separately.
In `Let $M,N$ be left modules over $R$.`, both modules have the same parameter
`R`.

Structure phrases may also have modifiers and a shared `such that` clause:

```tex
Let $X$ be a finite topological space that is compact.
Let $G,H$ be groups such that $G\ne H$.
```

Each modifier may use its subject's structure assumption. Modifiers are
otherwise independent: one cannot establish the domain needed by another.
The `such that` clause is checked afterwards and may use all the completed
structure and modifier assumptions.

You may omit a field's bracketed structure when exactly one declared
structure in scope provides that field. With two groups in scope, specify
which group supplies the operation:

```tex
Let $G,H$ be groups.
% Plain group multiplication is ambiguous here.
$\mul[G](g,g)=g$ and $\mul[H](h,h)=h$.
```

Several structures may be in scope if only one provides the requested field.
A compound term does not become an implicit field source merely because it
satisfies a structure predicate; write it in brackets explicitly.

Calculations use the same receiver resolution and formation checks as ordinary
assertions. A contextual abbreviation referring to `\leq` freezes its selected
structure for that link. The generic set-relation composition law then matches
its expanded predicate just as it matches an explicit `\mathrel{\leq[X]}`
link. The classification `quasiorder_relation_transitive` supplies the
transitivity condition from the quasiordered-set notion, including inherited
structure evidence. No separate composition registration is needed for each
kind of ordered structure.

Membership in a onesorted structure retains the carrier interpretation during
equality transport. Thus `a\in G=H` concludes membership in the selected
carrier projection of `H`. Use explicit carrier expressions when composing
with relations on sets, such as `\subseteq`.

## Rendering hosted fields

To customize a field's HTML notation, use a `structop` row in `lexicon.tsv`.
Use arity 1 for an explicit bracketed structure, represented by `<x1/>`, and
arity 0 when the structure is omitted. Supply separate templates if you use
both forms. A plain operator hint does not cover structure fields.

These templates change the display only. They do not choose which structure
an operation belongs to.

## Constructing records

The aggregate `\structure[SCHEMA]{FIELDS}` constructs a record from field
values. Entries may be positional, in declaration order,

```tex
\structure[pointed magma]{X,m,p}
```

or named, in any order:

```tex
\structure[pointed magma]{
    \point=p,
    \mul=m,
    \carrier=X
}
```

Use either positional or named entries in one aggregate. Supply every field
exactly once. Named entries are usually clearer for structures with several
fields.

The annotation may include parameters, as in
`\structure[left module over R]{...}`. It determines which fields the entries
fill, but is not stored in the record. Records with the same fields and values
are equal regardless of their annotations.

The annotation may be omitted only when the immediate phrase supplies one
unambiguous schema:

```tex
$\structure{X,m,p}$ is a pointed magma.
```

Elsewhere, supply the annotation explicitly.

An aggregate has exactly the selected fields. You must still prove their
specifications and the structure laws. For example, assigning `m` to `\mul`
does not prove that `m` has the required domain and codomain.

The fieldless aggregate `\structure[record]{}` is `\emptyset`. A structure
with no fields may still impose laws, which need a separate proof.

## Open and exact structure facts

Ordinary structure predicates allow extra fields. A pointed magma is also a
magma while keeping its point field. Write

```tex
$A$ is an exact pointed magma.
```

when `A` must have precisely that structure's fields. An exact pointed magma
is not an exact magma, since it has the additional point field.

An ordinary `record` may have any fields; an exact `record` has none and is
therefore the empty set. An arbitrary set need not be a record.

Citing a structure definition with `\auto{...}` or `\obv{...}` also exposes
its direct inheritance theorems. For example, citing `semigroup` makes
the implication from semigroup to magma available without another proof step.
Cite the parent definition too when another inheritance step is needed.

To use a parent's individual field requirements or laws, cite that parent's
definition or the particular law.

To discard the child's additional fields, use a reduct:

```tex
\reduct[magma]{A}
```

If `A` is a pointed magma, this keeps its carrier and multiplication and is an
exact magma. Each retained field has the same value as in `A`.

Two exact records with the same fields are equal if all their field values
are equal. To prove `$A=B$`, establish the exact structure facts and field
equalities, then use `by structure extensionality`:

```tex
$A$ is an exact pointed magma.
$B$ is an exact pointed magma.
$\carrier[A]=\carrier[B]$.
$\mul[A]=\mul[B]$.
$\point[A]=\point[B]$.
Follows by structure extensionality.
```

`Follows by extensionality.` uses the same rule when these facts are available;
otherwise it tries set extensionality. Ordinary structure assumptions allow
extra fields and are insufficient for this rule. Parameters and laws are not
fields, so they need no separate equality proofs. For two exact fieldless
records, no field equalities are needed.

## Reconstruction

A reconstruction copies fields from an existing record and replaces those
named after `with`:

```tex
$topological space based on M$
$topological space based on M with \carrier=U and \opens=O$
```

The result has exactly the target structure's fields; extra fields of the
base are discarded. The target need not be an ancestor of the base's structure,
but every field must either be available from the base or supplied explicitly.
Separately declared fields remain different even if their names match.

Replacements are simultaneous: each expression refers to the surrounding
context, not to earlier replacements. Put nested reconstructions in
parentheses to make clear which `with` and `and` belong together.

Felix must know the base's record fields, even if all fields are replaced.
It can obtain them from a structure assumption or proved structure fact, an
annotated aggregate, or a registered result classification. If a local alias
is not recognized as a record, state its structure fact explicitly first.

You must still prove that the reconstructed record satisfies the target's
field requirements and laws. Copying fields alone does not establish them.
When two unrelated structures use the same field name, an explicit reduct
can select the intended field, as in `\atlas[\reduct[coordinate datum]{N}]`.

## Named instances and construction families

A named instance defines a record with no parameters and proves that it
satisfies its structure's requirements. See `two_point_indiscrete_space` in
[topological-space.tex](../library/topology/topological-space.tex).

Felix also provides its exact field set and projection equations. Projection
theorems use the instance label and field name, for example
`two_point_indiscrete_spaceprojection_carrier` and
`two_point_indiscrete_spaceprojection_opens`.
The order of named entries does not affect these names.

For a family depending on parameters, use a `construction`. It combines a
record definition with a proof that the result satisfies the stated structure.
This example forgets the atlas of an equipped coordinate space:

```tex
\begin{construction}\label{underlying_topological_space}
    Let $M$ be an equipped coordinate space.
    The topological space $\UnderlyingTopologicalSpace{M}=
        topological space based on M$.
\end{construction}
\begin{proof}
    $\opens[M]$ is a topology on $\carrier[M]$
        by \obv{topological_space_opens_form_topology}.
    Follows by \auto{topology_family,
        topological_spaceaggregateprojection_carrier,
        topological_spaceaggregateprojection_opens}.
\end{proof}
```

The proof must immediately follow the construction. It establishes the field
requirements and laws. Felix then provides these public facts:

- `underlying_topological_space`: the result is a topological space;
- `underlying_topological_spaceshape`: it has exactly the target fields;
- `underlying_topological_spaceprojection_carrier` and
  `underlying_topological_spaceprojection_opens`: its field values.

All these facts retain the construction's parameters and hypotheses, even
when an individual field equation would need fewer assumptions.

The [complete example](../test/structure-spikes/manifolds-0.tex) supplies the
auxiliary vocabulary and uses these facts to prove that the construction
equals `\reduct[topological space]{M}`.

Use symbolic notation for the construction's name and list each set parameter
once, in header order. Recursive constructions and names written as noun
phrases are not supported. The body must be an aggregate or reconstruction.
An aggregate may omit its annotation here; an explicit annotation must agree
with the result structure, including its parameters.

Construction hypotheses must fit the notion system's rules for result
classifications, including its atomic and whole premise forms. They guard the
body during elaboration and condition the proved public results. The named
set function is total; writing it does not require these hypotheses. Ordinary
definition headers have a separate source-call contract. For an unsupported
result classification, use an ordinary definition followed by a separate
theorem or classification.

For example, copying a coordinate record `R` on `X` into one on `Y` requires
`$\atlas[R]\subseteq Y$`. Replacing its atlas by `B` while keeping parameter
`X` requires `$B\subseteq X$`. The
[reconstruction examples](../test/structure-spikes/reconstruction-law-transport.tex)
show both proofs.

Carriers may be empty when the field requirements and laws allow it. To choose
an element of a carrier, supply a witness or establish that it is inhabited.

In generated HTML, aggregates appear as angle-bracket records. Their pop-overs
show the structure and field assignments. Verified constructions and instances
list their theorems under “Public consequences”, including the hypotheses
needed to use them.

For the separate higher-order expression language, see
[The Felix foundation](foundation.md#concrete-higher-order-syntax). For
library-level ontology and notation conventions, see
[the library style guide](../library/STYLE.md) and
[notation index](../library/NOTATION.md).
