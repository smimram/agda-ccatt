------------------------------------------------------------------------
-- Biadjunctions between bicategories, in the hom-wise formulation: a
-- pair of bifunctors L : C → D and R : D → C together with a family of
-- equivalences of categories
--
--     Φ : D (L A , B) ≃ C (A , R B)
--
-- pseudonatural in A and B. Pseudonaturality is the whole content here:
-- the squares expressing that Φ commutes with pre- and postcomposition
-- do not commute on the nose, only up to specified natural isomorphisms
-- (Φ-naturalˡ and Φ-naturalʳ), which are in turn required to be coherent
-- with respect to composition, identities, and each other.
--
-- The unit-counit formulation is not available yet: it needs composition
-- of bifunctors and modifications, neither of which exists here. This is
-- the bicategorical analogue of the natural-bijection formulation of an
-- adjunction, of which adjunction.Adjunction proves the 1-dimensional
-- case (⌊_⌋/⌈_⌉ and ⌊⌋-naturalˡ/ʳ there are Φ, Φ-naturalˡ/ʳ here).
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import adjunction.Biadjunction as Biadj
--   open Biadj using (Biadjunction)
--
-- so that "open Biadjunction B" unambiguously refers to the record
-- module.

module adjunction.Biadjunction where

open import Level using (Level; _⊔_)

import Category as Cat
open Cat using (Category)
import Functor as Fun
open Fun using (Functor; _∘F_)
import Bicategory as Bicat
open Bicat using (Bicategory)
import Bifunctor as Bifun
open Bifun using (Bifunctor)
import adjunction.NaturalTransformation as NatTrans
open NatTrans using (_≅N_; ≅N⇒; ≅N⇐; ≅N⇒-natural; ≅N⇐-natural; ≅N-pointwise)
import adjunction.Adjunction as Adj
open Adj using (Equivalence)

private
  variable
    o ℓ₁ ℓ₂ e o' ℓ₁' ℓ₂' e' : Level

record Biadjunction {C : Bicategory o ℓ₁ ℓ₂ e} {D : Bicategory o' ℓ₁' ℓ₂' e'}
       (L : Bifunctor C D) (R : Bifunctor D C) :
       Set (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e ⊔ o' ⊔ ℓ₁' ⊔ ℓ₂' ⊔ e') where

  private module C = Bicategory C
  private module D = Bicategory D
  private module L = Bifunctor L
  private module R = Bifunctor R

  ----------------------------------------------------------------------
  -- The family of equivalences
  ----------------------------------------------------------------------

  field
    -- the transposition, and its pseudoinverse
    Φ : (A : C.Obj) (B : D.Obj) → Functor (D.hom (L.F₀ A) B) (C.hom A (R.F₀ B))
    Ψ : (A : C.Obj) (B : D.Obj) → Functor (C.hom A (R.F₀ B)) (D.hom (L.F₀ A) B)
    -- they form an adjoint equivalence of hom-categories
    equivalence : (A : C.Obj) (B : D.Obj) → Equivalence (Φ A B) (Ψ A B)

  private module Eq {A : C.Obj} {B : D.Obj} = Equivalence (equivalence A B)

  -- the transpositions on 1-cells…
  Φ₁ : {A : C.Obj} {B : D.Obj} → L.F₀ A D.⇒₁ B → A C.⇒₁ R.F₀ B
  Φ₁ {A} {B} = Functor.F₀ (Φ A B)

  Ψ₁ : {A : C.Obj} {B : D.Obj} → A C.⇒₁ R.F₀ B → L.F₀ A D.⇒₁ B
  Ψ₁ {A} {B} = Functor.F₀ (Ψ A B)

  -- …and on 2-cells
  Φ₂ : {A : C.Obj} {B : D.Obj} {h h' : L.F₀ A D.⇒₁ B} →
       h D.⇒₂ h' → Φ₁ h C.⇒₂ Φ₁ h'
  Φ₂ {A} {B} = Functor.F₁ (Φ A B)

  Ψ₂ : {A : C.Obj} {B : D.Obj} {k k' : A C.⇒₁ R.F₀ B} →
       k C.⇒₂ k' → Ψ₁ k D.⇒₂ Ψ₁ k'
  Ψ₂ {A} {B} = Functor.F₁ (Ψ A B)

  -- the unit and the counit of the equivalence, at the level of 2-cells
  η : {A : C.Obj} {B : D.Obj} (h : L.F₀ A D.⇒₁ B) → h D.⇒₂ Ψ₁ (Φ₁ h)
  η = Eq.η

  ε : {A : C.Obj} {B : D.Obj} (k : A C.⇒₁ R.F₀ B) → Φ₁ (Ψ₁ k) C.⇒₂ k
  ε = Eq.ε

  η-invertible : {A : C.Obj} {B : D.Obj} (h : L.F₀ A D.⇒₁ B) → D.Invertible₂ (η h)
  η-invertible = Eq.η-invertible

  ε-invertible : {A : C.Obj} {B : D.Obj} (k : A C.⇒₁ R.F₀ B) → C.Invertible₂ (ε k)
  ε-invertible = Eq.ε-invertible

  ----------------------------------------------------------------------
  -- Pseudonaturality
  ----------------------------------------------------------------------

  -- Both squares are stated as isomorphisms in a functor category, the
  -- functors being the pre- and postcomposition functors of Bicategory:
  -- naturality in the 2-cells of the hom-categories is then part of the
  -- datum instead of being a separate axiom.
  field
    -- Φ (h ∘ L f) ≅ Φ h ∘ f, naturally in h
    Φ-naturalˡ : {A A' : C.Obj} (f : A' C.⇒₁ A) (B : D.Obj) →
                 (Φ A' B ∘F D.precomp (L.F₁ f)) ≅N (C.precomp f ∘F Φ A B)
    -- Φ (g ∘ h) ≅ R g ∘ Φ h, naturally in h
    Φ-naturalʳ : (A : C.Obj) {B B' : D.Obj} (g : B D.⇒₁ B') →
                 (Φ A B' ∘F D.postcomp g) ≅N (C.postcomp (R.F₁ g) ∘F Φ A B)

  Φ-natˡ⇒ : {A A' : C.Obj} (f : A' C.⇒₁ A) {B : D.Obj} (h : L.F₀ A D.⇒₁ B) →
            Φ₁ (h D.∘₁ L.F₁ f) C.⇒₂ (Φ₁ h C.∘₁ f)
  Φ-natˡ⇒ f {B} h = ≅N⇒ (Φ-naturalˡ f B) h

  Φ-natˡ⇐ : {A A' : C.Obj} (f : A' C.⇒₁ A) {B : D.Obj} (h : L.F₀ A D.⇒₁ B) →
            (Φ₁ h C.∘₁ f) C.⇒₂ Φ₁ (h D.∘₁ L.F₁ f)
  Φ-natˡ⇐ f {B} h = ≅N⇐ (Φ-naturalˡ f B) h

  Φ-natʳ⇒ : {A : C.Obj} {B B' : D.Obj} (g : B D.⇒₁ B') (h : L.F₀ A D.⇒₁ B) →
            Φ₁ (g D.∘₁ h) C.⇒₂ (R.F₁ g C.∘₁ Φ₁ h)
  Φ-natʳ⇒ {A} g h = ≅N⇒ (Φ-naturalʳ A g) h

  Φ-natʳ⇐ : {A : C.Obj} {B B' : D.Obj} (g : B D.⇒₁ B') (h : L.F₀ A D.⇒₁ B) →
            (R.F₁ g C.∘₁ Φ₁ h) C.⇒₂ Φ₁ (g D.∘₁ h)
  Φ-natʳ⇐ {A} g h = ≅N⇐ (Φ-naturalʳ A g) h

  ----------------------------------------------------------------------
  -- Coherence
  ----------------------------------------------------------------------

  field
    -- the two squares can be pasted in either order: both ways of going
    -- from Φ (g ∘ (h ∘ L f)) to R g ∘ (Φ h ∘ f) agree
    Φ-exchange : {A A' : C.Obj} (f : A' C.⇒₁ A) {B B' : D.Obj} (g : B D.⇒₁ B')
                 (h : L.F₀ A D.⇒₁ B) →
                 ((R.F₁ g C.◁ Φ-natˡ⇒ f h) C.• Φ-natʳ⇒ g (h D.∘₁ L.F₁ f))
                 C.≈
                 (C.assoc⇒ (R.F₁ g) (Φ₁ h) f C.•
                   ((Φ-natʳ⇒ g h C.▷ f) C.•
                     (Φ-natˡ⇒ f (g D.∘₁ h) C.• Φ₂ (D.assoc⇐ g h (L.F₁ f)))))

    -- Φ ((h ∘ L f) ∘ L f') ⇒ Φ h ∘ (f ∘ f')   computed in the two possible ways
    Φ-naturalˡ-∘ : {A A' A'' : C.Obj} (f : A' C.⇒₁ A) (f' : A'' C.⇒₁ A')
                   {B : D.Obj} (h : L.F₀ A D.⇒₁ B) →
                   (Φ-natˡ⇒ (f C.∘₁ f') h C.•
                     (Φ₂ (h D.◁ L.F-∘⇒ f f') C.• Φ₂ (D.assoc⇒ h (L.F₁ f) (L.F₁ f'))))
                   C.≈
                   (C.assoc⇒ (Φ₁ h) f f' C.•
                     ((Φ-natˡ⇒ f h C.▷ f') C.• Φ-natˡ⇒ f' (h D.∘₁ L.F₁ f)))

    -- Φ (h ∘ id) ⇒ Φ h ∘ id   computed in the two possible ways
    Φ-naturalˡ-id : {A : C.Obj} {B : D.Obj} (h : L.F₀ A D.⇒₁ B) →
                    (Φ-natˡ⇒ (C.id₁ {A}) h C.• Φ₂ (h D.◁ L.F-id⇒))
                    C.≈
                    (C.unitʳ⇐ (Φ₁ h) C.• Φ₂ (D.unitʳ⇒ h))

    -- Φ (g' ∘ (g ∘ h)) ⇒ R (g' ∘ g) ∘ Φ h   computed in the two possible ways
    Φ-naturalʳ-∘ : {A : C.Obj} {B B' B'' : D.Obj} (g' : B' D.⇒₁ B'') (g : B D.⇒₁ B')
                   (h : L.F₀ A D.⇒₁ B) →
                   (Φ-natʳ⇒ (g' D.∘₁ g) h C.• Φ₂ (D.assoc⇐ g' g h))
                   C.≈
                   ((R.F-∘⇒ g' g C.▷ Φ₁ h) C.•
                     (C.assoc⇐ (R.F₁ g') (R.F₁ g) (Φ₁ h) C.•
                       ((R.F₁ g' C.◁ Φ-natʳ⇒ g h) C.• Φ-natʳ⇒ g' (g D.∘₁ h))))

    -- Φ (id ∘ h) ⇒ R id ∘ Φ h   computed in the two possible ways
    Φ-naturalʳ-id : {A : C.Obj} {B : D.Obj} (h : L.F₀ A D.⇒₁ B) →
                    Φ-natʳ⇒ (D.id₁ {B}) h
                    C.≈
                    ((R.F-id⇒ C.▷ Φ₁ h) C.•
                      (C.unitˡ⇐ (Φ₁ h) C.• Φ₂ (D.unitˡ⇒ h)))

  ----------------------------------------------------------------------
  -- Consequences
  ----------------------------------------------------------------------

  -- the two comparison 2-cells are invertible, being the components of
  -- natural isomorphisms
  Φ-natˡ-invertible : {A A' : C.Obj} (f : A' C.⇒₁ A) {B : D.Obj}
                      (h : L.F₀ A D.⇒₁ B) → C.Invertible₂ (Φ-natˡ⇒ f h)
  Φ-natˡ-invertible f {B} h = ≅N-pointwise (Φ-naturalˡ f B) h

  Φ-natʳ-invertible : {A : C.Obj} {B B' : D.Obj} (g : B D.⇒₁ B')
                      (h : L.F₀ A D.⇒₁ B) → C.Invertible₂ (Φ-natʳ⇒ g h)
  Φ-natʳ-invertible {A} g h = ≅N-pointwise (Φ-naturalʳ A g) h

  Φ-natˡ-iso : {A A' : C.Obj} (f : A' C.⇒₁ A) {B : D.Obj} (h : L.F₀ A D.⇒₁ B) →
               Φ₁ (h D.∘₁ L.F₁ f) C.≅₂ (Φ₁ h C.∘₁ f)
  Φ-natˡ-iso f h = C.≅₂-invertible (Φ-natˡ-invertible f h)

  Φ-natʳ-iso : {A : C.Obj} {B B' : D.Obj} (g : B D.⇒₁ B') (h : L.F₀ A D.⇒₁ B) →
               Φ₁ (g D.∘₁ h) C.≅₂ (R.F₁ g C.∘₁ Φ₁ h)
  Φ-natʳ-iso g h = C.≅₂-invertible (Φ-natʳ-invertible g h)

  -- naturality in the 2-cells of the hom-categories, which is what
  -- taking the squares in a functor category buys, in both directions
  Φ-natˡ-natural : {A A' : C.Obj} (f : A' C.⇒₁ A) {B : D.Obj}
                   {h h' : L.F₀ A D.⇒₁ B} (β : h D.⇒₂ h') →
                   (Φ-natˡ⇒ f h' C.• Φ₂ (β D.▷ L.F₁ f))
                   C.≈ ((Φ₂ β C.▷ f) C.• Φ-natˡ⇒ f h)
  Φ-natˡ-natural f {B} β = ≅N⇒-natural (Φ-naturalˡ f B) β

  Φ-natˡ-natural⇐ : {A A' : C.Obj} (f : A' C.⇒₁ A) {B : D.Obj}
                    {h h' : L.F₀ A D.⇒₁ B} (β : h D.⇒₂ h') →
                    (Φ-natˡ⇐ f h' C.• (Φ₂ β C.▷ f))
                    C.≈ (Φ₂ (β D.▷ L.F₁ f) C.• Φ-natˡ⇐ f h)
  Φ-natˡ-natural⇐ f {B} β = ≅N⇐-natural (Φ-naturalˡ f B) β

  Φ-natʳ-natural : {A : C.Obj} {B B' : D.Obj} (g : B D.⇒₁ B')
                   {h h' : L.F₀ A D.⇒₁ B} (β : h D.⇒₂ h') →
                   (Φ-natʳ⇒ g h' C.• Φ₂ (g D.◁ β))
                   C.≈ ((R.F₁ g C.◁ Φ₂ β) C.• Φ-natʳ⇒ g h)
  Φ-natʳ-natural {A} g β = ≅N⇒-natural (Φ-naturalʳ A g) β

  Φ-natʳ-natural⇐ : {A : C.Obj} {B B' : D.Obj} (g : B D.⇒₁ B')
                    {h h' : L.F₀ A D.⇒₁ B} (β : h D.⇒₂ h') →
                    (Φ-natʳ⇐ g h' C.• (R.F₁ g C.◁ Φ₂ β))
                    C.≈ (Φ₂ (g D.◁ β) C.• Φ-natʳ⇐ g h)
  Φ-natʳ-natural⇐ {A} g β = ≅N⇐-natural (Φ-naturalʳ A g) β

------------------------------------------------------------------------
-- Notation
------------------------------------------------------------------------

infix 4 _⊣₂_

_⊣₂_ : {C : Bicategory o ℓ₁ ℓ₂ e} {D : Bicategory o' ℓ₁' ℓ₂' e'} →
       Bifunctor C D → Bifunctor D C →
       Set (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e ⊔ o' ⊔ ℓ₁' ⊔ ℓ₂' ⊔ e')
L ⊣₂ R = Biadjunction L R
