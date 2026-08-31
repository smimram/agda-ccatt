------------------------------------------------------------------------
-- Bicategories, in the setoid approach: the 2-cells between two given
-- 1-cells form a setoid, i.e. they are equipped with an equivalence
-- relation _≈_ which plays the role of equality between 2-cells. The
-- 2-cells between two given objects are thus organized into a category
-- (the hom-category), which is what the definition below takes as
-- primitive.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import Bicategory as Bicat
--   open Bicat using (Bicategory)
--
-- so that "open Bicategory B" unambiguously refers to the record module.

module Bicategory where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

import Category as Cat
open Cat using (Category)

-- o  : level of objects
-- ℓ₁ : level of 1-cells
-- ℓ₂ : level of 2-cells
-- e  : level of equality between 2-cells
record Bicategory (o ℓ₁ ℓ₂ e : Level) : Set (suc (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e)) where

  infix  4 _⇒₁_
  infix  4 _⇒₂_
  infix  4 _≈_
  infix  4 _≅₂_
  infixr 9 _∘₁_
  infixr 9 _•_
  infixr 10 _∗_
  infixr 11 _◁_
  infixl 11 _▷_

  ----------------------------------------------------------------------
  -- Objects and hom-categories
  ----------------------------------------------------------------------

  field
    Obj : Set o
    hom : Obj → Obj → Category ℓ₁ ℓ₂ e

  -- 1-cells
  _⇒₁_ : Obj → Obj → Set ℓ₁
  A ⇒₁ B = Category.Obj (hom A B)

  -- all the structure of the hom-categories at once
  module Hom {A B : Obj} = Category (hom A B)

  -- 2-cells
  _⇒₂_ : {A B : Obj} → A ⇒₁ B → A ⇒₁ B → Set ℓ₂
  _⇒₂_ = Hom._⇒_

  -- equality between 2-cells
  _≈_ : {A B : Obj} {f g : A ⇒₁ B} → Rel (f ⇒₂ g) e
  _≈_ = Hom._≈_

  -- identity 2-cell
  id₂ : {A B : Obj} {f : A ⇒₁ B} → f ⇒₂ f
  id₂ = Hom.id

  -- vertical composition of 2-cells
  _•_ : {A B : Obj} {f g h : A ⇒₁ B} → g ⇒₂ h → f ⇒₂ g → f ⇒₂ h
  _•_ = Hom._∘_

  -- invertible 2-cells
  _≅₂_ : {A B : Obj} → A ⇒₁ B → A ⇒₁ B → Set (ℓ₂ ⊔ e)
  _≅₂_ = Hom._≅_

  ----------------------------------------------------------------------
  -- Recalling the laws of the hom-categories
  ----------------------------------------------------------------------

  ≈-refl : {A B : Obj} {f g : A ⇒₁ B} {α : f ⇒₂ g} → α ≈ α
  ≈-refl = Hom.≈-refl

  ≈-sym : {A B : Obj} {f g : A ⇒₁ B} {α β : f ⇒₂ g} → α ≈ β → β ≈ α
  ≈-sym = Hom.≈-sym

  ≈-trans : {A B : Obj} {f g : A ⇒₁ B} {α β γ : f ⇒₂ g} → α ≈ β → β ≈ γ → α ≈ γ
  ≈-trans = Hom.≈-trans

  •-cong : {A B : Obj} {f g h : A ⇒₁ B} {α α' : g ⇒₂ h} {β β' : f ⇒₂ g} →
           α ≈ α' → β ≈ β' → α • β ≈ α' • β'
  •-cong = Hom.∘-cong

  •-congˡ : {A B : Obj} {f g h : A ⇒₁ B} {α α' : g ⇒₂ h} {β : f ⇒₂ g} →
            α ≈ α' → α • β ≈ α' • β
  •-congˡ = Hom.∘-congˡ

  •-congʳ : {A B : Obj} {f g h : A ⇒₁ B} {α : g ⇒₂ h} {β β' : f ⇒₂ g} →
            β ≈ β' → α • β ≈ α • β'
  •-congʳ = Hom.∘-congʳ

  •-assoc : {A B : Obj} {f g h k : A ⇒₁ B} {α : h ⇒₂ k} {β : g ⇒₂ h} {γ : f ⇒₂ g} →
            (α • β) • γ ≈ α • (β • γ)
  •-assoc = Hom.assoc

  •-identityˡ : {A B : Obj} {f g : A ⇒₁ B} {α : f ⇒₂ g} → id₂ • α ≈ α
  •-identityˡ = Hom.identityˡ

  •-identityʳ : {A B : Obj} {f g : A ⇒₁ B} {α : f ⇒₂ g} → α • id₂ ≈ α
  •-identityʳ = Hom.identityʳ

  -- the two directions of an invertible 2-cell, and its inverse laws
  ≅₂to : {A B : Obj} {f g : A ⇒₁ B} → f ≅₂ g → f ⇒₂ g
  ≅₂to = Hom.to

  ≅₂from : {A B : Obj} {f g : A ⇒₁ B} → f ≅₂ g → g ⇒₂ f
  ≅₂from = Hom.from

  ≅₂isoˡ : {A B : Obj} {f g : A ⇒₁ B} (i : f ≅₂ g) → ≅₂from i • ≅₂to i ≈ id₂
  ≅₂isoˡ = Hom.isoˡ

  ≅₂isoʳ : {A B : Obj} {f g : A ⇒₁ B} (i : f ≅₂ g) → ≅₂to i • ≅₂from i ≈ id₂
  ≅₂isoʳ = Hom.isoʳ

  ≅₂-refl : {A B : Obj} {f : A ⇒₁ B} → f ≅₂ f
  ≅₂-refl = Hom.≅-refl

  ≅₂-sym : {A B : Obj} {f g : A ⇒₁ B} → f ≅₂ g → g ≅₂ f
  ≅₂-sym = Hom.≅-sym

  ≅₂-trans : {A B : Obj} {f g h : A ⇒₁ B} → f ≅₂ g → g ≅₂ h → f ≅₂ h
  ≅₂-trans = Hom.≅-trans

  -- the setoid of 2-cells from f to g, and equational reasoning on 2-cells
  ⇒₂-setoid : {A B : Obj} (f g : A ⇒₁ B) → Setoid ℓ₂ e
  ⇒₂-setoid = Hom.hom-setoid

  module ⇒₂-Reasoning {A B : Obj} {f g : A ⇒₁ B} = SetoidReasoning (⇒₂-setoid f g)

  ----------------------------------------------------------------------
  -- Horizontal composition
  ----------------------------------------------------------------------

  field
    -- identity 1-cell
    id₁ : {A : Obj} → A ⇒₁ A

    -- horizontal composition of 1-cells
    _∘₁_ : {A B C : Obj} → B ⇒₁ C → A ⇒₁ B → A ⇒₁ C

    -- horizontal composition of 2-cells
    _∗_ : {A B C : Obj} {f f' : B ⇒₁ C} {g g' : A ⇒₁ B} →
          f ⇒₂ f' → g ⇒₂ g' → (f ∘₁ g) ⇒₂ (f' ∘₁ g')

    ∗-cong : {A B C : Obj} {f f' : B ⇒₁ C} {g g' : A ⇒₁ B}
             {α α' : f ⇒₂ f'} {β β' : g ⇒₂ g'} →
             α ≈ α' → β ≈ β' → α ∗ β ≈ α' ∗ β'

    -- horizontal composition preserves identities…
    ∗-id : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
           id₂ {f = f} ∗ id₂ {f = g} ≈ id₂ {f = f ∘₁ g}

    -- …and vertical composition (interchange law)
    ∗-• : {A B C : Obj} {f f' f'' : B ⇒₁ C} {g g' g'' : A ⇒₁ B}
          (α' : f' ⇒₂ f'') (α : f ⇒₂ f') (β' : g' ⇒₂ g'') (β : g ⇒₂ g') →
          (α' • α) ∗ (β' • β) ≈ (α' ∗ β') • (α ∗ β)

  ----------------------------------------------------------------------
  -- Whiskering
  ----------------------------------------------------------------------

  -- left whiskering: a 1-cell acting on a 2-cell on the left
  _◁_ : {A B C : Obj} (f : B ⇒₁ C) {g g' : A ⇒₁ B} → g ⇒₂ g' → (f ∘₁ g) ⇒₂ (f ∘₁ g')
  f ◁ β = id₂ {f = f} ∗ β

  -- right whiskering
  _▷_ : {A B C : Obj} {f f' : B ⇒₁ C} → f ⇒₂ f' → (g : A ⇒₁ B) → (f ∘₁ g) ⇒₂ (f' ∘₁ g)
  α ▷ g = α ∗ id₂ {f = g}

  ----------------------------------------------------------------------
  -- Associator and unitors
  ----------------------------------------------------------------------

  field
    associator : {A B C D : Obj} (f : C ⇒₁ D) (g : B ⇒₁ C) (h : A ⇒₁ B) →
                 ((f ∘₁ g) ∘₁ h) ≅₂ (f ∘₁ (g ∘₁ h))
    unitorˡ : {A B : Obj} (f : A ⇒₁ B) → (id₁ ∘₁ f) ≅₂ f
    unitorʳ : {A B : Obj} (f : A ⇒₁ B) → (f ∘₁ id₁) ≅₂ f

  assoc⇒ : {A B C D : Obj} (f : C ⇒₁ D) (g : B ⇒₁ C) (h : A ⇒₁ B) →
           ((f ∘₁ g) ∘₁ h) ⇒₂ (f ∘₁ (g ∘₁ h))
  assoc⇒ f g h = ≅₂to (associator f g h)

  assoc⇐ : {A B C D : Obj} (f : C ⇒₁ D) (g : B ⇒₁ C) (h : A ⇒₁ B) →
           (f ∘₁ (g ∘₁ h)) ⇒₂ ((f ∘₁ g) ∘₁ h)
  assoc⇐ f g h = ≅₂from (associator f g h)

  unitˡ⇒ : {A B : Obj} (f : A ⇒₁ B) → (id₁ ∘₁ f) ⇒₂ f
  unitˡ⇒ f = ≅₂to (unitorˡ f)

  unitˡ⇐ : {A B : Obj} (f : A ⇒₁ B) → f ⇒₂ (id₁ ∘₁ f)
  unitˡ⇐ f = ≅₂from (unitorˡ f)

  unitʳ⇒ : {A B : Obj} (f : A ⇒₁ B) → (f ∘₁ id₁) ⇒₂ f
  unitʳ⇒ f = ≅₂to (unitorʳ f)

  unitʳ⇐ : {A B : Obj} (f : A ⇒₁ B) → f ⇒₂ (f ∘₁ id₁)
  unitʳ⇐ f = ≅₂from (unitorʳ f)

  ----------------------------------------------------------------------
  -- Naturality and coherence
  ----------------------------------------------------------------------

  field
    assoc-natural : {A B C D : Obj} {f f' : C ⇒₁ D} {g g' : B ⇒₁ C} {h h' : A ⇒₁ B}
                    (α : f ⇒₂ f') (β : g ⇒₂ g') (γ : h ⇒₂ h') →
                    (α ∗ (β ∗ γ)) • assoc⇒ f g h ≈ assoc⇒ f' g' h' • ((α ∗ β) ∗ γ)

    unitˡ-natural : {A B : Obj} {f f' : A ⇒₁ B} (α : f ⇒₂ f') →
                    α • unitˡ⇒ f ≈ unitˡ⇒ f' • (id₁ {B} ◁ α)

    unitʳ-natural : {A B : Obj} {f f' : A ⇒₁ B} (α : f ⇒₂ f') →
                    α • unitʳ⇒ f ≈ unitʳ⇒ f' • (α ▷ id₁ {A})

    -- (f ∘ id) ∘ g ⇒ f ∘ g   computed in the two possible ways
    triangle : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
               unitʳ⇒ f ▷ g ≈ (f ◁ unitˡ⇒ g) • assoc⇒ f id₁ g

    -- ((f ∘ g) ∘ h) ∘ k ⇒ f ∘ (g ∘ (h ∘ k))   computed in the two possible ways
    pentagon : {A B C D E : Obj} (f : D ⇒₁ E) (g : C ⇒₁ D) (h : B ⇒₁ C) (k : A ⇒₁ B) →
               assoc⇒ f g (h ∘₁ k) • assoc⇒ (f ∘₁ g) h k ≈
               (f ◁ assoc⇒ g h k) • (assoc⇒ f (g ∘₁ h) k • (assoc⇒ f g h ▷ k))

  ----------------------------------------------------------------------
  -- Properties of whiskering
  ----------------------------------------------------------------------

  ◁-cong : {A B C : Obj} (f : B ⇒₁ C) {g g' : A ⇒₁ B} {β β' : g ⇒₂ g'} →
           β ≈ β' → f ◁ β ≈ f ◁ β'
  ◁-cong f p = ∗-cong ≈-refl p

  ▷-cong : {A B C : Obj} {f f' : B ⇒₁ C} {α α' : f ⇒₂ f'} (g : A ⇒₁ B) →
           α ≈ α' → α ▷ g ≈ α' ▷ g
  ▷-cong g p = ∗-cong p ≈-refl

  ◁-id : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) → f ◁ id₂ {f = g} ≈ id₂
  ◁-id f g = ∗-id f g

  ▷-id : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) → id₂ {f = f} ▷ g ≈ id₂
  ▷-id f g = ∗-id f g

  ◁-• : {A B C : Obj} (f : B ⇒₁ C) {g g' g'' : A ⇒₁ B}
        (β' : g' ⇒₂ g'') (β : g ⇒₂ g') →
        f ◁ (β' • β) ≈ (f ◁ β') • (f ◁ β)
  ◁-• f β' β = ≈-trans (∗-cong (≈-sym •-identityˡ) ≈-refl) (∗-• id₂ id₂ β' β)

  ▷-• : {A B C : Obj} {f f' f'' : B ⇒₁ C}
        (α' : f' ⇒₂ f'') (α : f ⇒₂ f') (g : A ⇒₁ B) →
        (α' • α) ▷ g ≈ (α' ▷ g) • (α ▷ g)
  ▷-• α' α g = ≈-trans (∗-cong ≈-refl (≈-sym •-identityˡ)) (∗-• α' α id₂ id₂)

  -- horizontal composition decomposes into two whiskerings, in two ways
  ∗-decomposeˡ : {A B C : Obj} {f f' : B ⇒₁ C} {g g' : A ⇒₁ B}
                 (α : f ⇒₂ f') (β : g ⇒₂ g') → α ∗ β ≈ (α ▷ g') • (f ◁ β)
  ∗-decomposeˡ α β =
    ≈-trans (∗-cong (≈-sym •-identityʳ) (≈-sym •-identityˡ)) (∗-• α id₂ id₂ β)

  ∗-decomposeʳ : {A B C : Obj} {f f' : B ⇒₁ C} {g g' : A ⇒₁ B}
                 (α : f ⇒₂ f') (β : g ⇒₂ g') → α ∗ β ≈ (f' ◁ β) • (α ▷ g)
  ∗-decomposeʳ α β =
    ≈-trans (∗-cong (≈-sym •-identityˡ) (≈-sym •-identityʳ)) (∗-• id₂ α β id₂)

  -- whiskering on the left and on the right can be exchanged
  exchange : {A B C : Obj} {f f' : B ⇒₁ C} {g g' : A ⇒₁ B}
             (α : f ⇒₂ f') (β : g ⇒₂ g') → (α ▷ g') • (f ◁ β) ≈ (f' ◁ β) • (α ▷ g)
  exchange α β = ≈-trans (≈-sym (∗-decomposeˡ α β)) (∗-decomposeʳ α β)

  ----------------------------------------------------------------------
  -- Horizontal composition of invertible 2-cells
  ----------------------------------------------------------------------

  infixr 10 _∗≅_
  infixr 11 _◁≅_
  infixl 11 _▷≅_

  _∗≅_ : {A B C : Obj} {f f' : B ⇒₁ C} {g g' : A ⇒₁ B} →
         f ≅₂ f' → g ≅₂ g' → (f ∘₁ g) ≅₂ (f' ∘₁ g')
  _∗≅_ {f = f} {f' = f'} {g = g} {g' = g'} i j =
    Hom.mk≅ (≅₂to i ∗ ≅₂to j) (≅₂from i ∗ ≅₂from j)
      (≈-trans (≈-sym (∗-• (≅₂from i) (≅₂to i) (≅₂from j) (≅₂to j)))
      (≈-trans (∗-cong (≅₂isoˡ i) (≅₂isoˡ j)) (∗-id f g)))
      (≈-trans (≈-sym (∗-• (≅₂to i) (≅₂from i) (≅₂to j) (≅₂from j)))
      (≈-trans (∗-cong (≅₂isoʳ i) (≅₂isoʳ j)) (∗-id f' g')))

  _◁≅_ : {A B C : Obj} (f : B ⇒₁ C) {g g' : A ⇒₁ B} → g ≅₂ g' → (f ∘₁ g) ≅₂ (f ∘₁ g')
  f ◁≅ j = ≅₂-refl {f = f} ∗≅ j

  _▷≅_ : {A B C : Obj} {f f' : B ⇒₁ C} → f ≅₂ f' → (g : A ⇒₁ B) → (f ∘₁ g) ≅₂ (f' ∘₁ g)
  i ▷≅ g = i ∗≅ ≅₂-refl {f = g}

  ----------------------------------------------------------------------
  -- Naturality in the reverse direction
  ----------------------------------------------------------------------

  assoc-natural⇐ : {A B C D : Obj} {f f' : C ⇒₁ D} {g g' : B ⇒₁ C} {h h' : A ⇒₁ B}
                   (α : f ⇒₂ f') (β : g ⇒₂ g') (γ : h ⇒₂ h') →
                   assoc⇐ f' g' h' • (α ∗ (β ∗ γ)) ≈ ((α ∗ β) ∗ γ) • assoc⇐ f g h
  assoc-natural⇐ {f = f} {f' = f'} {g = g} {g' = g'} {h = h} {h' = h'} α β γ =
    Hom.≅-natural (associator f g h) (associator f' g' h')
                  ((α ∗ β) ∗ γ) (α ∗ (β ∗ γ)) (assoc-natural α β γ)

  unitˡ-natural⇐ : {A B : Obj} {f f' : A ⇒₁ B} (α : f ⇒₂ f') →
                   unitˡ⇐ f' • α ≈ (id₁ {B} ◁ α) • unitˡ⇐ f
  unitˡ-natural⇐ {f = f} {f' = f'} α =
    Hom.≅-natural (unitorˡ f) (unitorˡ f') (id₁ ◁ α) α (unitˡ-natural α)

  unitʳ-natural⇐ : {A B : Obj} {f f' : A ⇒₁ B} (α : f ⇒₂ f') →
                   unitʳ⇐ f' • α ≈ (α ▷ id₁ {A}) • unitʳ⇐ f
  unitʳ-natural⇐ {f = f} {f' = f'} α =
    Hom.≅-natural (unitorʳ f) (unitorʳ f') (α ▷ id₁) α (unitʳ-natural α)
