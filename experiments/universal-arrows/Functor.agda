------------------------------------------------------------------------
-- Functors between categories (in the setoid approach): a functor has
-- to preserve the equality of morphisms, which is an extra condition
-- (F-cong) with respect to the usual definition.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import Functor as Fun
--   open Fun using (Functor)
--
-- so that "open Functor F" unambiguously refers to the record module.

module Functor where

open import Level using (Level; _⊔_)

import Category as Cat
open Cat using (Category)

private
  variable
    o ℓ e o' ℓ' e' o'' ℓ'' e'' : Level

record Functor (C : Category o ℓ e) (D : Category o' ℓ' e') :
       Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') where

  private module C = Category C
  private module D = Category D

  field
    -- action on objects
    F₀ : C.Obj → D.Obj
    -- action on morphisms
    F₁ : {A B : C.Obj} → A C.⇒ B → F₀ A D.⇒ F₀ B
    -- the action on morphisms is compatible with their equality
    F-cong : {A B : C.Obj} {f g : A C.⇒ B} → f C.≈ g → F₁ f D.≈ F₁ g
    -- functoriality
    F-id : {A : C.Obj} → F₁ (C.id {A}) D.≈ D.id
    F-∘  : {A B E : C.Obj} (f : B C.⇒ E) (g : A C.⇒ B) →
           F₁ (f C.∘ g) D.≈ F₁ f D.∘ F₁ g

  -- functors preserve isomorphisms
  F-≅ : {A B : C.Obj} → A C.≅ B → F₀ A D.≅ F₀ B
  F-≅ i = D.mk≅ (F₁ (C.to i)) (F₁ (C.from i))
    (D.≈-trans (D.≈-sym (F-∘ (C.from i) (C.to i)))
    (D.≈-trans (F-cong (C.isoˡ i)) F-id))
    (D.≈-trans (D.≈-sym (F-∘ (C.to i) (C.from i)))
    (D.≈-trans (F-cong (C.isoʳ i)) F-id))

open Functor public

------------------------------------------------------------------------
-- Identity and composition
------------------------------------------------------------------------

Id : {C : Category o ℓ e} → Functor C C
Id {C = C} = record
  { F₀     = λ A → A
  ; F₁     = λ f → f
  ; F-cong = λ p → p
  ; F-id   = Category.≈-refl C
  ; F-∘    = λ f g → Category.≈-refl C
  }

infixr 9 _∘F_

_∘F_ : {C : Category o ℓ e} {D : Category o' ℓ' e'} {E : Category o'' ℓ'' e''} →
       Functor D E → Functor C D → Functor C E
_∘F_ {D = D} {E = E} G F = record
  { F₀     = λ A → F₀ G (F₀ F A)
  ; F₁     = λ f → F₁ G (F₁ F f)
  ; F-cong = λ p → F-cong G (F-cong F p)
  ; F-id   = Category.≈-trans E (F-cong G (F-id F)) (F-id G)
  ; F-∘    = λ f g → Category.≈-trans E (F-cong G (F-∘ F f g)) (F-∘ G (F₁ F f) (F₁ F g))
  }
