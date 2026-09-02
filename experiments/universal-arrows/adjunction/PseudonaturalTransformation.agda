------------------------------------------------------------------------
-- Pseudonatural transformations between bifunctors, i.e. the
-- bicategorical analogue of natural transformations. The naturality
-- squares do not commute on the nose: they commute up to a specified
-- invertible 2-cell (the naturator), which is natural in 2-cells and
-- coherent with respect to the comparison 2-cells of the two bifunctors.
--
-- The naturator is taken in the oplax direction, from τ ∘ F f towards
-- G f ∘ τ; flipping it means flipping the three axioms below.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import adjunction.PseudonaturalTransformation as PsNat
--   open PsNat using (PseudonaturalTransformation)
--
-- so that "open PseudonaturalTransformation τ" unambiguously refers to
-- the record module.

module adjunction.PseudonaturalTransformation where

open import Level using (Level; _⊔_)

import Category as Cat
open Cat using (Category)
import Bicategory as Bicat
open Bicat using (Bicategory)
import Bifunctor as Bifun
open Bifun using (Bifunctor)

private
  variable
    o ℓ₁ ℓ₂ e o' ℓ₁' ℓ₂' e' : Level

record PseudonaturalTransformation
       {C : Bicategory o ℓ₁ ℓ₂ e} {D : Bicategory o' ℓ₁' ℓ₂' e'}
       (F G : Bifunctor C D) : Set (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₁' ⊔ ℓ₂' ⊔ e') where

  private module C = Bicategory C
  private module D = Bicategory D
  private module F = Bifunctor F
  private module G = Bifunctor G

  ----------------------------------------------------------------------
  -- Components
  ----------------------------------------------------------------------

  -- as elsewhere, the subscript marks the dimension of the cell: τ₁ is
  -- the component at an object (a 1-cell), τ₂ the component at a 1-cell
  -- (a 2-cell)
  field
    -- the component at an object
    τ₁ : (A : C.Obj) → F.F₀ A D.⇒₁ G.F₀ A

    -- the naturator, invertible: the 1-cell is taken explicitly, since
    -- F₁ is a field and hence not injective for unification
    naturator : {A B : C.Obj} (f : A C.⇒₁ B) →
                (τ₁ B D.∘₁ F.F₁ f) D.≅₂ (G.F₁ f D.∘₁ τ₁ A)

  τ₂⇒ : {A B : C.Obj} (f : A C.⇒₁ B) →
        (τ₁ B D.∘₁ F.F₁ f) D.⇒₂ (G.F₁ f D.∘₁ τ₁ A)
  τ₂⇒ f = D.≅₂to (naturator f)

  τ₂⇐ : {A B : C.Obj} (f : A C.⇒₁ B) →
        (G.F₁ f D.∘₁ τ₁ A) D.⇒₂ (τ₁ B D.∘₁ F.F₁ f)
  τ₂⇐ f = D.≅₂from (naturator f)

  ----------------------------------------------------------------------
  -- Naturality and coherence
  ----------------------------------------------------------------------

  field
    -- the naturator is natural in 2-cells
    τ₂-natural : {A B : C.Obj} {f f' : A C.⇒₁ B} (α : f C.⇒₂ f') →
                 ((G.F₂ α D.▷ τ₁ A) D.• τ₂⇒ f)
                 D.≈ (τ₂⇒ f' D.• (τ₁ B D.◁ F.F₂ α))

    -- τ E ∘ (F f ∘ F g) ⇒ G (f ∘ g) ∘ τ A   computed in the two possible ways
    τ₂-∘ : {A B E : C.Obj} (f : B C.⇒₁ E) (g : A C.⇒₁ B) →
           (τ₂⇒ (f C.∘₁ g) D.• (τ₁ E D.◁ F.F-∘⇒ f g))
           D.≈
           ((G.F-∘⇒ f g D.▷ τ₁ A) D.•
             (D.assoc⇐ (G.F₁ f) (G.F₁ g) (τ₁ A) D.•
               ((G.F₁ f D.◁ τ₂⇒ g) D.•
                 (D.assoc⇒ (G.F₁ f) (τ₁ B) (F.F₁ g) D.•
                   ((τ₂⇒ f D.▷ F.F₁ g) D.• D.assoc⇐ (τ₁ E) (F.F₁ f) (F.F₁ g))))))

    -- τ A ∘ id ⇒ G id ∘ τ A   computed in the two possible ways
    τ₂-id : (A : C.Obj) →
            (τ₂⇒ (C.id₁ {A}) D.• (τ₁ A D.◁ F.F-id⇒))
            D.≈
            ((G.F-id⇒ D.▷ τ₁ A) D.• (D.unitˡ⇐ (τ₁ A) D.• D.unitʳ⇒ (τ₁ A)))

  ----------------------------------------------------------------------
  -- Naturality in the reverse direction
  ----------------------------------------------------------------------

  τ₂-natural⇐ : {A B : C.Obj} {f f' : A C.⇒₁ B} (α : f C.⇒₂ f') →
                (τ₂⇐ f' D.• (G.F₂ α D.▷ τ₁ A))
                D.≈ ((τ₁ B D.◁ F.F₂ α) D.• τ₂⇐ f)
  τ₂-natural⇐ {A} {B} {f} {f'} α =
    D.Hom.≅-natural (naturator f) (naturator f')
                    (τ₁ B D.◁ F.F₂ α) (G.F₂ α D.▷ τ₁ A) (τ₂-natural α)

open PseudonaturalTransformation public
