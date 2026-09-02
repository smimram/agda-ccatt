# Equivalence between formulations of universal arrows for bicategories

An Agda formalization of two definitions of a *biuniversal arrow* — the
bicategorical analogue of a universal arrow — together with a proof that they
agree.

Fix a pseudofunctor `F : C → D` between bicategories and an object `y` of `D`.
Both definitions start from the same data:

- an object `ȳ` of `C`;
- a 1-cell `u : F ȳ → y` in `D`;
- for every object `x` of `C` and every 1-cell `f : F x → y`, a 1-cell
  `f̄ : x → ȳ` together with an **invertible** 2-cell `ε_f : u ∘ F f̄ ⇒ f`.

In the Agda, `f̄` is written `⇑₁ f`, and `⇑₂` is the corresponding lifting of
2-cells; the overlines below are spelled out that way when the argument is a
composite.

They differ in how 2-cells are handled.

**First formulation** (`Universal`, from `universal1.tex`) — a genuine universal
property. For every `α : u ∘ F g ⇒ f` there is a *unique* `α' : g ⇒ f̄` with

    ε_f • (u ◁ F α') = α

and the 2-cell `η_g := (id_{u ∘ F g})'` is required to be invertible.

**Second formulation** (`UniversalHA`, from `universal2.tex`) — the same notion
presented algebraically, in the half-adjoint style (hence `HA`): nothing is
asserted to be unique, and the lifting of 2-cells is given as data instead.

- for every `f : x → ȳ` an invertible `η_f : f ⇒ ⇑₁(u ∘ F f)`, subject to the
  triangle identity `ε_{u ∘ F f} • (u ◁ F η_f) = id`;
- for every `α : f ⇒ g` between 1-cells `F x → y`, a 2-cell `ᾱ : f̄ ⇒ ḡ`,
  compatible with the equality of 2-cells, and natural in the two senses
  `α • ε_f = ε_g • (u ◁ F ᾱ)` and `⇑₂(u ◁ F α) • η_f = η_g • α`.

The second is what one actually wants when *building* a biuniversal arrow by
hand; the first is what one wants when *using* it. `Universal.agda` proves them
equivalent: two translations `Universal→UniversalHA` and
`UniversalHA→Universal`, mutually inverse in the sense that a round trip leaves
`ȳ`, `u`, `⇑₁` and `ε` unchanged on the nose and returns `⇑₂` and `η` up to the
equality of 2-cells (`Universal-roundtrip-⇑₂`/`-η`,
`UniversalHA-roundtrip-⇑₂`/`-η`).

Going from the universal property to the algebraic form is largely bookkeeping.
The other direction rests on one lemma, `◁-faithful`: whiskering by `u` and
applying `F` is faithful on 2-cells between 1-cells `x → ȳ`. That is what stands
in for the missing uniqueness clause, and it is exactly where the two conditions
that look like clutter in the second formulation — compatibility of `⇑₂` with
the equality of 2-cells, and invertibility of `η` — are used.

## The setoid approach

Bicategories are formalized *setoid-enriched*: 2-cells are not compared with
propositional equality but with a given equivalence relation `_≈_`, so that the
2-cells between two objects form a category — the hom-category — whose morphism
equality is a setoid equality. Nothing is quotiented and nothing needs
transport, at the cost of carrying compatibility conditions such as `F-cong` by
hand.

Composition is written in the usual order, not the diagrammatic one used in the
`.tex` notes: where a note writes `F f̄ ⨟ u` the Agda reads `u ∘₁ F₁ (⇑₁ f)`, and
where it writes `α ⨟ β` the Agda reads `β • α`.

## Files

- `Category.agda` — setoid-enriched categories; invertible morphisms, and
  isomorphisms derived from them.
- `Functor.agda` — functors between those.
- `Bicategory.agda` — bicategories, taking the hom-categories as primitive.
- `Bifunctor.agda` — pseudofunctors (homomorphisms of bicategories).
- `Universal.agda` — both definitions of a biuniversal arrow, and their
  equivalence.
- `adjunction/NaturalTransformation.agda` — natural transformations, and the
  functor category.
- `adjunction/Adjunction.agda` — adjunctions and adjoint equivalences between
  categories, the 1-categorical warm-up.
- `adjunction/PseudonaturalTransformation.agda` — pseudonatural
  transformations between pseudofunctors: the naturality square commutes only
  up to an invertible 2-cell.
- `adjunction/Biadjunction.agda` — biadjunctions, as a pair of pseudofunctors
  together with a pseudonatural family of equivalences `D (L A , B) ≃ C (A , R B)`.
- `adjunction/UniversalBiadjunction.agda` — the pointwise presentation: a
  pseudofunctor admitting a biuniversal arrow to every object, i.e. having a
  right biadjoint.
- `universal1.tex`, `universal2.tex` — the notes the two formulations
  transcribe.

Dependency order: `Category → Functor → Bicategory → Bifunctor → Universal`;
in `adjunction/`, `NaturalTransformation → Adjunction`,
`Bifunctor → PseudonaturalTransformation`, and `Biadjunction` on top of
`Bifunctor`, `NaturalTransformation` and `Adjunction`.

## Building

This directory is its own Agda library root (`ua.agda-lib`), independent from
the rest of the repository, and depends only on the standard library. Run from
*this* directory:

```sh
agda --build-library
```

The library sets `--allow-unsolved-metas`, so a successful run can still hide
holes and unsolved metavariables. To check for real, bypass the flag — the
horizontal composition of a bicategory is a record field and hence not
injective for unification, so unsolved metas are a genuine hazard here:

```sh
agda --no-libraries -i. -i/path/to/agda-stdlib/src Universal.agda
```

`Universal` is the top of the dependency graph, so this checks everything.
It currently succeeds: no holes, no postulates, no unsolved metavariables.

Tested with Agda 2.8.0 and agda-stdlib v2.4.

## Status

The equivalence is complete. There is as yet no example instance of either
record, so the definitions have never been exercised on a concrete bicategory,
and none of the special cases the notes are aiming at — terminal objects,
adjunctions — have been derived. Pseudonatural transformations and
biadjunctions are defined but not yet exercised either: there is no identity
and no vertical composition of pseudonatural transformations (the identity one
needs Kelly's lemma `unitˡ⇒ id₁ ≈ unitʳ⇒ id₁`, which is not available yet), and
no example of a biadjunction. The two presentations of a biadjunction are not
connected either: `UniversalBiadjunction` yields `R₀`, `R₁` and `R₂`, but
turning those into a `Bifunctor` and then into a `Biadjunction` needs the
compositor of `R` and is a real proof. Composition of pseudofunctors,
modifications and the unit-counit formulation of a biadjunction are also still
missing.

## Tool disclosure

This is mostly auto-formalized with Claude (Opus 5).
