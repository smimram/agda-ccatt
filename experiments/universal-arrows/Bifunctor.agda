------------------------------------------------------------------------
-- Bifunctors, i.e. functors between bicategories (also known as
-- homomorphisms of bicategories, or pseudofunctors). Composition and
-- identities are preserved only up to a specified invertible 2-cell,
-- natural and subject to coherence axioms.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import Bifunctor as Bifun
--   open Bifun using (Bifunctor)
--
-- so that "open Bifunctor F" unambiguously refers to the record module.

module Bifunctor where

open import Level using (Level; _⊔_)

import Category as Cat
open Cat using (Category)
import Functor as Fun
open Fun using (Functor)
import Bicategory as Bicat
open Bicat using (Bicategory)

private
  variable
    o ℓ₁ ℓ₂ e o' ℓ₁' ℓ₂' e' : Level

record Bifunctor (C : Bicategory o ℓ₁ ℓ₂ e) (D : Bicategory o' ℓ₁' ℓ₂' e') :
       Set (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e ⊔ o' ⊔ ℓ₁' ⊔ ℓ₂' ⊔ e') where

  private module C = Bicategory C
  private module D = Bicategory D

  ----------------------------------------------------------------------
  -- Action on objects, 1-cells and 2-cells
  ----------------------------------------------------------------------

  field
    -- action on objects
    F₀ : C.Obj → D.Obj
    -- action on the hom-categories: this provides the action on 1-cells
    -- and on 2-cells, together with the fact that vertical composition
    -- is preserved (strictly)
    Fhom : (A B : C.Obj) → Functor (C.hom A B) (D.hom (F₀ A) (F₀ B))

  -- action on 1-cells
  F₁ : {A B : C.Obj} → A C.⇒₁ B → F₀ A D.⇒₁ F₀ B
  F₁ {A} {B} = Functor.F₀ (Fhom A B)

  -- action on 2-cells
  F₂ : {A B : C.Obj} {f g : A C.⇒₁ B} → f C.⇒₂ g → F₁ f D.⇒₂ F₁ g
  F₂ {A} {B} = Functor.F₁ (Fhom A B)

  F₂-cong : {A B : C.Obj} {f g : A C.⇒₁ B} {α β : f C.⇒₂ g} →
            α C.≈ β → F₂ α D.≈ F₂ β
  F₂-cong {A} {B} = Functor.F-cong (Fhom A B)

  -- the identity 2-cell is preserved
  F₂-id₂ : {A B : C.Obj} {f : A C.⇒₁ B} → F₂ (C.id₂ {f = f}) D.≈ D.id₂
  F₂-id₂ {A} {B} = Functor.F-id (Fhom A B)

  -- vertical composition is preserved
  F₂-• : {A B : C.Obj} {f g h : A C.⇒₁ B} (α : g C.⇒₂ h) (β : f C.⇒₂ g) →
         F₂ (α C.• β) D.≈ F₂ α D.• F₂ β
  F₂-• {A} {B} = Functor.F-∘ (Fhom A B)

  -- invertible 2-cells are preserved
  F₂-≅ : {A B : C.Obj} {f g : A C.⇒₁ B} → f C.≅₂ g → F₁ f D.≅₂ F₁ g
  F₂-≅ {A} {B} = Functor.F-≅ (Fhom A B)

  ----------------------------------------------------------------------
  -- Comparison 2-cells
  ----------------------------------------------------------------------

  field
    -- horizontal composition is preserved up to an invertible 2-cell
    F-∘ : {A B E : C.Obj} (f : B C.⇒₁ E) (g : A C.⇒₁ B) →
          (F₁ f D.∘₁ F₁ g) D.≅₂ F₁ (f C.∘₁ g)
    -- and so is the identity 1-cell
    F-id : {A : C.Obj} → (D.id₁ {F₀ A}) D.≅₂ F₁ (C.id₁ {A})

  F-∘⇒ : {A B E : C.Obj} (f : B C.⇒₁ E) (g : A C.⇒₁ B) →
         (F₁ f D.∘₁ F₁ g) D.⇒₂ F₁ (f C.∘₁ g)
  F-∘⇒ f g = D.≅₂to (F-∘ f g)

  F-∘⇐ : {A B E : C.Obj} (f : B C.⇒₁ E) (g : A C.⇒₁ B) →
         F₁ (f C.∘₁ g) D.⇒₂ (F₁ f D.∘₁ F₁ g)
  F-∘⇐ f g = D.≅₂from (F-∘ f g)

  F-id⇒ : {A : C.Obj} → (D.id₁ {F₀ A}) D.⇒₂ F₁ (C.id₁ {A})
  F-id⇒ = D.≅₂to F-id

  F-id⇐ : {A : C.Obj} → F₁ (C.id₁ {A}) D.⇒₂ (D.id₁ {F₀ A})
  F-id⇐ = D.≅₂from F-id

  ----------------------------------------------------------------------
  -- Naturality and coherence
  ----------------------------------------------------------------------

  field
    -- the comparison for composition is natural in both arguments
    F-∘-natural : {A B E : C.Obj} {f f' : B C.⇒₁ E} {g g' : A C.⇒₁ B}
                  (α : f C.⇒₂ f') (β : g C.⇒₂ g') →
                  (F₂ (α C.∗ β) D.• F-∘⇒ f g) D.≈ (F-∘⇒ f' g' D.• (F₂ α D.∗ F₂ β))

    -- (F f ∘ F g) ∘ F h ⇒ F (f ∘ (g ∘ h))   computed in the two possible ways
    F-assoc : {A B E G : C.Obj} (f : E C.⇒₁ G) (g : B C.⇒₁ E) (h : A C.⇒₁ B) →
              (F₂ (C.assoc⇒ f g h) D.• (F-∘⇒ (f C.∘₁ g) h D.• (F-∘⇒ f g D.▷ F₁ h)))
              D.≈
              (F-∘⇒ f (g C.∘₁ h) D.•
                ((F₁ f D.◁ F-∘⇒ g h) D.• D.assoc⇒ (F₁ f) (F₁ g) (F₁ h)))

    -- id ∘ F f ⇒ F f   computed in the two possible ways
    F-unitˡ : {A B : C.Obj} (f : A C.⇒₁ B) →
              (F₂ (C.unitˡ⇒ f) D.• (F-∘⇒ C.id₁ f D.• (F-id⇒ D.▷ F₁ f)))
              D.≈ D.unitˡ⇒ (F₁ f)

    -- F f ∘ id ⇒ F f   computed in the two possible ways
    F-unitʳ : {A B : C.Obj} (f : A C.⇒₁ B) →
              (F₂ (C.unitʳ⇒ f) D.• (F-∘⇒ f C.id₁ D.• (F₁ f D.◁ F-id⇒)))
              D.≈ D.unitʳ⇒ (F₁ f)

  ----------------------------------------------------------------------
  -- Naturality in the reverse direction
  ----------------------------------------------------------------------

  F-∘-natural⇐ : {A B E : C.Obj} {f f' : B C.⇒₁ E} {g g' : A C.⇒₁ B}
                 (α : f C.⇒₂ f') (β : g C.⇒₂ g') →
                 (F-∘⇐ f' g' D.• F₂ (α C.∗ β)) D.≈ ((F₂ α D.∗ F₂ β) D.• F-∘⇐ f g)
  F-∘-natural⇐ {f = f} {f' = f'} {g = g} {g' = g'} α β =
    D.Hom.≅-natural (F-∘ f g) (F-∘ f' g')
                    (F₂ α D.∗ F₂ β) (F₂ (α C.∗ β)) (F-∘-natural α β)

open Bifunctor public

------------------------------------------------------------------------
-- The identity bifunctor
------------------------------------------------------------------------

Id : {C : Bicategory o ℓ₁ ℓ₂ e} → Bifunctor C C
Id {C = C} = record
  { F₀          = λ A → A
  ; Fhom        = λ A B → Fun.Id
  ; F-∘         = λ f g → ≅₂-refl
  ; F-id        = ≅₂-refl
  ; F-∘-natural = λ α β → ≈-trans •-identityʳ (≈-sym •-identityˡ)
  ; F-assoc     = λ f g h →
      ≈-trans (≈-trans (•-congʳ (≈-trans (•-congʳ (▷-id (f ∘₁ g) h)) •-identityˡ))
                       •-identityʳ)
      (≈-sym (≈-trans •-identityˡ
             (≈-trans (•-congˡ (◁-id f (g ∘₁ h))) •-identityˡ)))
  ; F-unitˡ     = λ f →
      ≈-trans (•-congʳ (≈-trans (•-congʳ (▷-id id₁ f)) •-identityˡ)) •-identityʳ
  ; F-unitʳ     = λ f →
      ≈-trans (•-congʳ (≈-trans (•-congʳ (◁-id f id₁)) •-identityˡ)) •-identityʳ
  }
  where open Bicategory C
