# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with
code in this directory.

## What this is

An exploratory formalization aiming at the **equivalence between formulations
of universal arrows for bicategories** (see `README.md`). Bicategories are
formalized in the **setoid approach**: 2-cells are not compared with
propositional equality but with a given equivalence relation `_≈_`, so that the
2-cells between two objects form a *category* (the hom-category) whose morphism
equality is a setoid equality. Nothing is quotiented and nothing needs
transport.

This directory is its own Agda library root (`ua.agda-lib`, flag
`--allow-unsolved-metas`), independent from the rest of the repository. It
depends only on `standard-library`. Toolchain in use: Agda 2.8.0, agda-stdlib
v2.4.

## Build

```sh
agda --build-library     # everything
agda Bicategory.agda     # single module, faster feedback
```

Run from *this* directory — the `.agda-lib` here is what makes imports resolve.

Type-checking is the only correctness check, and `--allow-unsolved-metas` means
a "successful" run can still hide holes and unsolved metavariables. Always
check explicitly:

```sh
grep -n '{!!}' *.agda
agda --no-libraries -i. -i/path/to/agda-stdlib/src Universal.agda   # strict
```

`Universal` is the top of the dependency graph, so checking it checks
everything. The second command bypasses the `.agda-lib` flags entirely, so
unsolved metas become errors. This matters more than usual here (see "Explicit arguments"
below).

## Current state

**Everything type-checks, with no holes, no postulates and no unsolved metas.**
The main result of the directory is done: both formulations of a biuniversal
arrow are stated (`Universal` and `UniversalHA`) and proved equivalent, by two
translations that are mutually inverse up to `_≈_` — all in `Universal.agda`.

There is still no example instance of either record, so the definitions have
never been exercised on a concrete bicategory; `Universal→UniversalHA` and
`UniversalHA→Universal` are the only things that build one, and they play the
role `Id` plays in `Bifunctor.agda`.

Pseudonatural transformations between bifunctors are defined
(`adjunction/PseudonaturalTransformation.agda`) but have no instance either:
neither the identity nor vertical composition is built, the identity being
blocked on Kelly's lemma (`unitˡ⇒ id₁ ≈ unitʳ⇒ id₁`), which `Bicategory.agda`
does not prove.

Biadjunctions (`adjunction/Biadjunction.agda`) are defined in the hom-wise
formulation, again with no instance, and
`adjunction/UniversalBiadjunction.agda` defines the pointwise presentation
(a biuniversal arrow to every object). Nothing connects the two yet.

Not done yet: composition of bifunctors (`_∘F_` exists for ordinary functors,
but the pseudofunctor case requires building the compositor of a composite and
is a real proof), modifications, the unit-counit formulation of a biadjunction
(which needs both of those), the passage from a `UniversalBiadjunction` to a
`Biadjunction` (which needs `R` as a `Bifunctor`, hence its compositor), and
the special cases the notes are aiming at (terminal objects, adjunctions).

## Architecture

Dependency order: `Category → Functor → Bicategory → Bifunctor → Universal`,
and, in `adjunction/`, `NaturalTransformation → Adjunction` and
`Bifunctor → PseudonaturalTransformation`, with `Biadjunction` on top of
`Bifunctor`, `NaturalTransformation` and `Adjunction`.

- **`Category.agda`** — setoid-enriched categories. `record Category o ℓ e`
  with `Obj`, `_⇒_`, `_≈_`, `id`, `_∘_` and the laws (`≈-equiv`, `∘-cong`,
  `assoc`, `identityˡ`, `identityʳ`); the laws take their morphism arguments
  *implicitly*, which is what makes equational-reasoning chains readable.
  Derived: `≈-refl`/`≈-sym`/`≈-trans`, `∘-congˡ`/`∘-congʳ`, `assoc'` (the
  reversed associativity), and `hom-setoid : (A B : Obj) → Setoid ℓ e`, which is
  what feeds `Relation.Binary.Reasoning.Setoid`.

  Also `record Invertible f` (`inv`, `invˡ`, `invʳ`), the *primitive* notion:
  it is what to reach for when the morphism is already at hand. Its algebra —
  `mkInv`, `id-invertible`, `inv-invertible`, `∘-invertible`, and
  `∘-cancelˡ`/`∘-cancelʳ` (an invertible morphism can be cancelled from either
  side of an equation) — is where the actual proofs live. Isomorphisms are then *derived*, as the Σ-type
  `A ≅ B = Σ (A ⇒ B) Invertible`, with `to`/`invertible-≅` the two projections
  and `from`/`isoˡ`/`isoʳ`/`mk≅`/`≅-invertible` on top of them, so that
  `≅-refl`/`≅-sym`/`≅-trans` are one-liners over the `Invertible` algebra.
  Adding an isomorphism lemma therefore means adding the `Invertible` lemma
  first and pairing it. Finally `≅-natural`: if a square commutes with the `to`
  directions of two isos, it commutes with the `from` directions. `_≅_` lives
  here rather than in `Bicategory` because the associator and unitors are
  exactly isomorphisms *in a hom-category*, and `≅-natural` is what gives their
  reverse-direction naturality for free.

- **`Functor.agda`** — `record Functor (C : Category …) (D : Category …)` with
  `F₀`, `F₁`, `F-cong`, `F-id`, `F-∘`. In the setoid approach `F-cong`
  (compatibility with `_≈_`) is a genuine extra condition, not a consequence.
  The record body opens its two arguments as `private module C = Category C`
  and `module D = Category D`, so laws read `F₁ (f C.∘ g) D.≈ F₁ f D.∘ F₁ g` —
  this is the idiom to follow whenever two (bi)categories are in scope at once.
  Derived: `F-≅` (functors preserve isomorphisms). Then, after
  `open Functor public`, the identity functor `Id` and composition `_∘F_`.

- **`Bicategory.agda`** — `record Bicategory o ℓ₁ ℓ₂ e` (objects, 1-cells,
  2-cells, equality of 2-cells). Structure of the record, in order:

  1. `Obj` and `hom : Obj → Obj → Category ℓ₁ ℓ₂ e`, then
     `module Hom {A B : Obj} = Category (hom A B)` which lifts the whole
     hom-category API in one go. Everything vertical (`_⇒₂_`, `_≈_`, `id₂`,
     `_•_`, `_≅₂_`, `•-assoc`, `•-identityˡ/ʳ`, `⇒₂-setoid`, `⇒₂-Reasoning`) is
     a one-line re-export of `Hom.…`, *not* a new field. Adding a law about
     vertical composition means adding it to `Category`, not here.
  2. Horizontal composition: `id₁`, `_∘₁_`, `_∗_` on 2-cells, with `∗-cong`,
     `∗-id` and the interchange law `∗-•`. Those last two are exactly
     "`_∘₁_` is a functor `hom B C × hom A B → hom A C`", spelled out so that
     no product category or `Functor` record is needed.
  3. Whiskering `_◁_` / `_▷_`, defined *between* two `field` blocks (this is
     legal in Agda and is the reason the field blocks are split) so that the
     coherence axioms below can be stated with them.
  4. `associator`, `unitorˡ`, `unitorʳ` as `_≅₂_`, with directed aliases
     `assoc⇒`/`assoc⇐`, `unitˡ⇒`/`unitˡ⇐`, `unitʳ⇒`/`unitʳ⇐`.
  5. Naturality (`assoc-natural`, `unitˡ-natural`, `unitʳ-natural`) and
     coherence (`triangle`, `pentagon`).
  6. Derived: `◁-cong`/`▷-cong`, `◁-id`/`▷-id`, `◁-•`/`▷-•`,
     `∗-decomposeˡ`/`∗-decomposeʳ` (horizontal composition as two whiskerings,
     in both orders), `exchange`, `postcomp`/`precomp` (composing with a fixed
     1-cell, as a `Functor` between hom-categories — this is why the file
     imports `Functor.agda`), the 2-iso algebra `_∗≅_`/`_◁≅_`/`_▷≅_`, and
     the reverse naturalities `assoc-natural⇐`, `unitˡ-natural⇐`,
     `unitʳ-natural⇐` (each a one-liner via `Hom.≅-natural`).

  There is deliberately **no example instance**: the derived lemmas play that
  role. `∗-decomposeˡ`, `exchange` and the `⇐`-naturalities do not type-check
  unless the interchange direction and the associator/unitor orientations are
  mutually consistent. If one of them stops working after an edit, the axiom
  orientation is what to revisit, not the lemma.

- **`Bifunctor.agda`** — `record Bifunctor (C : Bicategory …) (D : Bicategory …)`:
  a morphism of bicategories, i.e. what is elsewhere called a homomorphism of
  bicategories or a pseudofunctor. Structure of the record:

  1. `F₀` on objects, and `Fhom : (A B : C.Obj) → Functor (C.hom A B) (D.hom …)`.
     Taking a `Functor` between hom-categories as the primitive datum gives, in
     one field, the action on 1-cells (`F₁ = Functor.F₀ …`), on 2-cells
     (`F₂ = Functor.F₁ …`), and the fact that `_≈_`, `id₂` and vertical
     composition are preserved *strictly* (`F₂-cong`, `F₂-id₂`, `F₂-•`), plus
     `F₂-≅` for free. Only horizontal composition is weakened.
  2. The comparison 2-cells `F-∘` and `F-id`, as `_≅₂_`, with directed aliases
     `F-∘⇒`/`F-∘⇐` and `F-id⇒`/`F-id⇐`.
  3. `F-∘-natural`, then the three coherence axioms `F-assoc` (the two ways of
     going from `(F f ∘ F g) ∘ F h` to `F (f ∘ (g ∘ h))`), `F-unitˡ` and
     `F-unitʳ`.
  4. `F-∘-natural⇐`, a one-liner via `D.Hom.≅-natural`.

  The identity bifunctor `Id` is defined at the end of the file. It is the
  sanity check that the axioms are consistent: it is the one place where all
  four coherence axioms are actually *discharged* rather than assumed, so if an
  orientation is wrong, `Id` is where it shows up.

- **`Universal.agda`** — biuniversal arrows, in the two formulations whose
  equivalence is the point of the directory. Neither record depends on the
  other; each is parametrized by a `Bifunctor C D` and an object `y : D.Obj`,
  and the names are deliberately kept in step so that the two can be read side
  by side: `U₀` (the object ȳ), `U₁` (the 1-cell `u : F ȳ ⇒ y`),
  `⇑₁`/`ε`/`ε-invertible` for the factorization of 1-cells (with `ε⁻¹`/`ε-iso`
  derived from it), `η`/`η-invertible` for the unit (with `η⁻¹`/`η-iso`), and
  `⇑₂` for the factorization of 2-cells. Only `⇑₂` means something different on
  each side — see below; everything else has the same type in both.

  1. `Universal` (`universal1.tex`) — the *universal-property* form. `⇑₂ α`
     factors a 2-cell `α : u ∘₁ F g ⇒₂ f` as a `g ⇒₂ ⇑₁ f`, and is pinned down
     by `⇑₂-β` together with `⇑₂-unique`. `η g = ⇑₂ id₂` is therefore a
     *definition*, only its invertibility being a field. Derived: `⇑₂-β'`,
     `⇑₂-cong` and `⇑₂-cancel`, all consequences of `⇑₂-unique`.
  2. `UniversalHA` (`universal2.tex`) — the *algebraic*, half-adjoint form.
     `⇑₂` (here of type `f ⇒₂ g → ⇑₁ f ⇒₂ ⇑₁ g`) and `η` are data, with no
     uniqueness clause; they are tied together by `η-triangle`
     (`ε (u ∘₁ F f) • (u ◁ F₂ (η f)) ≈ id₂`) and by the two naturality axioms
     `ε-natural` and `η-natural`. Since uniqueness is gone, `⇑₂-cong` is a
     *field* here rather than a lemma, and it is genuinely not derivable:
     cancelling `ε` in `ε-natural` only yields
     `u ◁ F₂ (⇑₂ α) ≈ u ◁ F₂ (⇑₂ β)`, and coming back from there through
     `η-natural` needs `⇑₂-cong` itself. Derived: `η-triangle'` (the triangle
     read as `u ◁ F₂ (η f) ≈ ε⁻¹ …`), `ε-natural⇐` and `η-natural⇐`.

  **Composition order.** The `.tex` notes compose diagrammatically, the Agda
  does not: `F f̄ ⨟ u` is `U₁ ∘₁ F₁ (⇑₁ f)` and `α ⨟ β` is `β • α`. Every axiom
  here is the note's equation read backwards in that sense — check this first
  when a transcription looks wrong.

  As in `Bifunctor.agda`, the `⇐`-lemmas are the sanity check: `ε-natural⇐` and
  `η-natural⇐` are one-liners via `Hom.≅-natural`, and they type-check only if
  the orientations of `ε`, `η` and the two naturality axioms are mutually
  consistent.

  3. The **equivalence**, in a single anonymous module fixing `C`, `D`, `F`
     and `y`. Both translations copy `U₀`, `U₁`, `⇑₁` and `ε` unchanged and only
     rebuild `⇑₂` and `η`, which is why the round trips are definitional on the
     first four components and only need a lemma on the last two.

     - `Universal→UniversalHA` — `⇑₂ α` becomes `U.⇑₂ (α • ε f)` (composing with
       `ε` puts `α` in the shape `U.⇑₂` expects) and `η-triangle` is literally
       `⇑₂-β` at `id₂`. Only `η-natural` needs work: apply `⇑₂-cancel`, then
       both sides collapse to `u ◁ F₂ α`.
     - `UniversalHA→Universal` — `⇑₂ α` becomes `H.⇑₂ α • H.η g`. Everything
       here rests on `◁-faithful`, the lemma that `u ◁ F₂ (−)` is faithful on
       2-cells between 1-cells `x ⇒₁ ȳ`; it is what replaces the missing
       uniqueness clause, and it is the only consumer of `⇑₂-cong` together
       with the invertibility of `η`. `⇑₂-id` (`H.⇑₂ id₂ ≈ id₂`) follows from
       it and is what makes the derived `η` invertible.
     - `Universal-roundtrip-⇑₂`/`-η` and `UniversalHA-roundtrip-⇑₂`/`-η` — four
       one-liners, each reusing the `⇑₂-β`/`⇑₂-unique` of the *translated*
       structure rather than reproving anything.

  Do **not** `open Universal public`: the two records deliberately share field
  names, so access stays qualified (`U.ε`, `Universal.⇑₂-β R α`).

- **`adjunction/PseudonaturalTransformation.agda`** — pseudonatural
  transformations `τ : F ⇒ G` between two `Bifunctor C D`. Data: the component
  `τ₁ A : F₀ A ⇒₁ G₀ A` at an object (the subscript marks the dimension of the
  cell, as everywhere else), and the *naturator*, an invertible 2-cell
  `naturator f : τ₁ B ∘₁ F₁ f ≅₂ G₁ f ∘₁ τ₁ A`, with the directed aliases
  `τ₂⇒`/`τ₂⇐`. The orientation is the **oplax** one, from `τ ∘ F f` towards
  `G f ∘ τ`; flipping it means flipping all three axioms. Those are
  `τ₂-natural` (naturality in 2-cells, stated in the `g • to i ≈ to j • f`
  shape of `Bifunctor.F-∘-natural`, precisely so that the `⇐` version is a
  one-liner), `τ₂-∘` (coherence with `F-∘⇒`/`G-∘⇒` and the associators) and
  `τ₂-id` (coherence with `F-id⇒`/`G-id⇒` and the unitors). Derived:
  `τ₂-natural⇐`, via `D.Hom.≅-natural` — as in `Bicategory.agda`, that
  one-liner is the consistency check standing in for the missing example
  instance, and it type-checks only if the naturator's orientation and
  `τ₂-natural` agree.

  `η` is deliberately *not* reused for the components, unlike in
  `adjunction/NaturalTransformation.agda`, since `η` already names the unit of
  a biuniversal arrow.

- **`adjunction/Biadjunction.agda`** — biadjunctions, hom-wise: bifunctors
  `L : C → D` and `R : D → C` with a family of adjoint equivalences of
  hom-categories `Φ A B : D (L A , B) ≃ C (A , R B)` (fields `Φ`, `Ψ`,
  `equivalence`, the last one an `Equivalence` from
  `adjunction/Adjunction.agda`), pseudonatural in both variables. Derived from
  the family: `Φ₁`/`Ψ₁` on 1-cells, `Φ₂`/`Ψ₂` on 2-cells, and `η`/`ε` with
  their invertibility.

  Pseudonaturality is split by variable, as `Φ-naturalˡ f B` and
  `Φ-naturalʳ A g`, each a `_≅N_` between composites of pre-/postcomposition
  functors — which is why `Bicategory.agda` gained `precomp`/`postcomp`.
  Stating them in a functor category means naturality in the 2-cells of the
  hom-categories is part of the datum (`Φ-natˡ-natural` and friends are then
  read off with `≅N⇒-natural`), rather than a further axiom. Directed aliases
  `Φ-natˡ⇒`/`Φ-natˡ⇐`/`Φ-natʳ⇒`/`Φ-natʳ⇐` are the components.

  Four coherence axioms then say the family is genuinely pseudonatural:
  `Φ-exchange` (the two squares paste in either order), `Φ-naturalˡ-∘` and
  `Φ-naturalʳ-∘` (compatibility with composition, through `L-∘⇒`/`R-∘⇒` and
  the associators), `Φ-naturalˡ-id` and `Φ-naturalʳ-id` (compatibility with
  identities, through `L-id⇒`/`R-id⇒` and the unitors). The two families are
  *not* symmetric — `Φ-naturalˡ` has `L` on the source side of the square and
  `Φ-naturalʳ` has `R` on its target side — so their axioms are not mirror
  images of each other; that asymmetry is expected, not a transcription slip.

  Notation: `L ⊣₂ R`, mirroring `_⊣_` in `adjunction/Adjunction.agda`.

- **`adjunction/UniversalBiadjunction.agda`** — `record
  UniversalBiadjunction (F : Bifunctor C D)` with the single field
  `universal : (y : D.Obj) → Universal F y`: the pointwise way of saying that
  `F` has a right biadjoint. `universalHA` re-reads the same data in the
  algebraic formulation, through `Universal→UniversalHA`.

  The rest of the record is the family opened at a variable object:
  `private module U (y : D.Obj) = Universal (universal y)`, and then `R₀`, `u`
  (the universal 1-cell), `⇑₁`, `ε`, `⇑₂`, `η` and their laws re-exported with
  `y` turned *implicit*, since it is determined by the 1-cell being
  transposed. That is the only real design decision in the file: `U.ε y f` is
  unusable in practice, `ε f` reads like the `Universal` it comes from.

  Then the beginnings of the right biadjoint: `R₁ g = ⇑₁ (g ∘₁ u y)` and
  `R₂ β = ⇑₂ ((β ▷ u y) • ε (g ∘₁ u y))`, with `R₂-cong`. These are data only
  — no functoriality is proved, and none is needed to state the record. Making
  `R` a `Bifunctor`, and hence relating this record to `Biadjunction`, is the
  next step and a real proof.

## Conventions

- **Explicit arguments on the associator and unitors.** `assoc⇒ f g h`, not
  `assoc⇒ {f} {g} {h}`. `_∘₁_` is a record field, hence not injective for
  unification, so a constraint like `?x ∘₁ (?y ∘₁ ?z) =?= f ∘₁ (g ∘₁ h)` is
  unsolvable: with implicit arguments the pentagon would elaborate to unsolved
  metas that `--allow-unsolved-metas` swallows in silence. Keep them explicit.
  2-cell arguments stay implicit where they are determined by an explicit
  argument's type.
- **Import idiom.** Each file's module has the same name as the record it
  defines, which makes the bare name ambiguous as a *module* name. Importers
  must write

  ```agda
  import Bicategory as Bicat
  open Bicat using (Bicategory)
  ```

  after which `open Bicategory B` unambiguously means the record module. Same
  for `Category`, `Functor`, `Bifunctor` and `Universal` (whose module holds
  both `Universal` and `UniversalHA`). This is noted in a comment at the top of
  each of those files except `Universal.agda`, which has no importer yet.
- **Direction of the comparison 2-cells.** `F-∘⇒ f g : F f ∘₁ F g ⇒₂ F (f ∘₁ g)`
  and `F-id⇒ : id₁ ⇒₂ F id₁` — from the composite of the images towards the
  image of the composite (the lax direction, here made invertible). All the
  coherence axioms are stated in that direction; flipping it means flipping all
  of them.
- **Naming.** Subscript `₁`/`₂` marks the dimension (`_⇒₁_`, `_⇒₂_`, `id₁`,
  `id₂`, `_∘₁_`, `F₁`/`F₂`); `_•_` is vertical composition, `_∗_` horizontal
  composition of 2-cells, `_◁_`/`_▷_` left/right whiskering; `⇒`/`⇐` suffixes
  name the two directions of a structural iso. `⇑₁`/`⇑₂` are the liftings along
  a universal arrow, `ε`/`η` its counit and unit, `ε⁻¹`/`η⁻¹` their inverses
  and `ε-iso`/`η-iso` the corresponding `_≅₂_`. A primed name (`assoc'`,
  `⇑₂-β'`, `η-triangle'`) is a variant of the unprimed one — the symmetric
  equation, or the same equation solved for a different subterm. Match this
  rather than introducing ASCII variants.
- Reuse stdlib (`IsEquivalence`, `Setoid`, `Rel`,
  `Relation.Binary.Reasoning.Setoid`) rather than redefining; there is no
  `Prelude.agda` here.
- Keep the development hole-free. Prefer a named lemma with an explicit `TODO`
  comment over a bare `{!!}` that `--allow-unsolved-metas` will silently
  swallow.
