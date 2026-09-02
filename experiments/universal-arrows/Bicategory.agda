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
import Functor as Fun
open Fun using (Functor)

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

  -- invertibility, as a property of a given 2-cell
  Invertible₂ : {A B : Obj} {f g : A ⇒₁ B} → f ⇒₂ g → Set (ℓ₂ ⊔ e)
  Invertible₂ = Hom.Invertible

  ≅₂-invertible : {A B : Obj} {f g : A ⇒₁ B} {α : f ⇒₂ g} → Invertible₂ α → f ≅₂ g
  ≅₂-invertible = Hom.≅-invertible

  invertible-≅₂ : {A B : Obj} {f g : A ⇒₁ B} (i : f ≅₂ g) → Invertible₂ (≅₂to i)
  invertible-≅₂ = Hom.invertible-≅

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
  -- Composition as a functor in each variable
  ----------------------------------------------------------------------

  -- composing with a fixed 1-cell on the left is a functor between
  -- hom-categories, acting on 2-cells by whiskering
  postcomp : {A B C : Obj} (f : B ⇒₁ C) → Functor (hom A B) (hom A C)
  postcomp f = record
    { F₀     = λ g → f ∘₁ g
    ; F₁     = λ β → f ◁ β
    ; F-cong = ◁-cong f
    ; F-id   = ◁-id f _
    ; F-∘    = λ β' β → ◁-• f β' β
    }

  -- and so is composing with a fixed 1-cell on the right
  precomp : {A B C : Obj} (g : A ⇒₁ B) → Functor (hom B C) (hom A C)
  precomp g = record
    { F₀     = λ f → f ∘₁ g
    ; F₁     = λ α → α ▷ g
    ; F-cong = ▷-cong g
    ; F-id   = ▷-id _ g
    ; F-∘    = λ α' α → ▷-• α' α g
    }

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
  -- Unit coherence (Kelly)
  ----------------------------------------------------------------------

  -- whiskering by the identity 1-cell is faithful: the unitors are
  -- natural isomorphisms, so id₁ ◁ (−) is isomorphic to the identity
  ◁-id₁-faithful : {A B : Obj} {f g : A ⇒₁ B} {α β : f ⇒₂ g} →
                   (id₁ {B} ◁ α) ≈ (id₁ ◁ β) → α ≈ β
  ◁-id₁-faithful {f = f} {α = α} {β = β} p =
    Hom.∘-cancelʳ (invertible-≅₂ (unitorˡ f))
      (≈-trans (unitˡ-natural α) (≈-trans (•-congʳ p) (≈-sym (unitˡ-natural β))))

  ▷-id₁-faithful : {A B : Obj} {f g : A ⇒₁ B} {α β : f ⇒₂ g} →
                   (α ▷ id₁ {A}) ≈ (β ▷ id₁) → α ≈ β
  ▷-id₁-faithful {f = f} {α = α} {β = β} p =
    Hom.∘-cancelʳ (invertible-≅₂ (unitorʳ f))
      (≈-trans (unitʳ-natural α) (≈-trans (•-congʳ p) (≈-sym (unitʳ-natural β))))

  -- the left unitor of a composite, which is not an axiom but a
  -- consequence of the triangle and the pentagon (Kelly's argument: the
  -- two sides agree after whiskering by id₁, which is faithful)
  unitˡ-∘ : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
            unitˡ⇒ (f ∘₁ g) • assoc⇒ id₁ f g ≈ unitˡ⇒ f ▷ g
  unitˡ-∘ f g = ◁-id₁-faithful
    (Hom.∘-cancelʳ (invertible-≅₂ (associator id₁ (id₁ ∘₁ f) g))
      (≈-trans main (≈-sym (assoc-natural (id₂ {f = id₁}) (unitˡ⇒ f) (id₂ {f = g})))))
    where
      open ⇒₂-Reasoning

      main : (id₁ ◁ (unitˡ⇒ (f ∘₁ g) • assoc⇒ id₁ f g)) • assoc⇒ id₁ (id₁ ∘₁ f) g
             ≈ assoc⇒ id₁ f g • ((id₁ ◁ unitˡ⇒ f) ▷ g)
      main = Hom.∘-cancelʳ (invertible-≅₂ (associator id₁ id₁ f ▷≅ g)) (begin
        ((id₁ ◁ (unitˡ⇒ (f ∘₁ g) • assoc⇒ id₁ f g)) • assoc⇒ id₁ (id₁ ∘₁ f) g)
          • (assoc⇒ id₁ id₁ f ▷ g)
            ≈⟨ •-congˡ (•-congˡ (◁-• id₁ (unitˡ⇒ (f ∘₁ g)) (assoc⇒ id₁ f g))) ⟩
        (((id₁ ◁ unitˡ⇒ (f ∘₁ g)) • (id₁ ◁ assoc⇒ id₁ f g)) • assoc⇒ id₁ (id₁ ∘₁ f) g)
          • (assoc⇒ id₁ id₁ f ▷ g)
            ≈⟨ •-congˡ •-assoc ⟩
        ((id₁ ◁ unitˡ⇒ (f ∘₁ g)) •
          ((id₁ ◁ assoc⇒ id₁ f g) • assoc⇒ id₁ (id₁ ∘₁ f) g))
          • (assoc⇒ id₁ id₁ f ▷ g)
            ≈⟨ •-assoc ⟩
        (id₁ ◁ unitˡ⇒ (f ∘₁ g)) •
          (((id₁ ◁ assoc⇒ id₁ f g) • assoc⇒ id₁ (id₁ ∘₁ f) g)
            • (assoc⇒ id₁ id₁ f ▷ g))
            ≈⟨ •-congʳ •-assoc ⟩
        (id₁ ◁ unitˡ⇒ (f ∘₁ g)) •
          ((id₁ ◁ assoc⇒ id₁ f g) •
            (assoc⇒ id₁ (id₁ ∘₁ f) g • (assoc⇒ id₁ id₁ f ▷ g)))
            ≈⟨ •-congʳ (≈-sym (pentagon id₁ id₁ f g)) ⟩
        (id₁ ◁ unitˡ⇒ (f ∘₁ g)) • (assoc⇒ id₁ id₁ (f ∘₁ g) • assoc⇒ (id₁ ∘₁ id₁) f g)
            ≈⟨ ≈-sym •-assoc ⟩
        ((id₁ ◁ unitˡ⇒ (f ∘₁ g)) • assoc⇒ id₁ id₁ (f ∘₁ g)) • assoc⇒ (id₁ ∘₁ id₁) f g
            ≈⟨ •-congˡ (≈-sym (triangle id₁ (f ∘₁ g))) ⟩
        (unitʳ⇒ id₁ ▷ (f ∘₁ g)) • assoc⇒ (id₁ ∘₁ id₁) f g
            ≈⟨ •-congˡ (∗-cong ≈-refl (≈-sym (∗-id f g))) ⟩
        (unitʳ⇒ id₁ ∗ (id₂ {f = f} ∗ id₂ {f = g})) • assoc⇒ (id₁ ∘₁ id₁) f g
            ≈⟨ assoc-natural (unitʳ⇒ id₁) (id₂ {f = f}) (id₂ {f = g}) ⟩
        assoc⇒ id₁ f g • ((unitʳ⇒ id₁ ▷ f) ▷ g)
            ≈⟨ •-congʳ (▷-cong g (triangle id₁ f)) ⟩
        assoc⇒ id₁ f g • (((id₁ ◁ unitˡ⇒ f) • assoc⇒ id₁ id₁ f) ▷ g)
            ≈⟨ •-congʳ (▷-• (id₁ ◁ unitˡ⇒ f) (assoc⇒ id₁ id₁ f) g) ⟩
        assoc⇒ id₁ f g • (((id₁ ◁ unitˡ⇒ f) ▷ g) • (assoc⇒ id₁ id₁ f ▷ g))
            ≈⟨ ≈-sym •-assoc ⟩
        (assoc⇒ id₁ f g • ((id₁ ◁ unitˡ⇒ f) ▷ g)) • (assoc⇒ id₁ id₁ f ▷ g) ∎)

  -- the same for the right unitor, mirrored
  unitʳ-∘ : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
            unitʳ⇒ (f ∘₁ g) ≈ (f ◁ unitʳ⇒ g) • assoc⇒ f g id₁
  unitʳ-∘ f g = ▷-id₁-faithful
    (Hom.∘-cancelˡ (invertible-≅₂ (associator f g id₁)) (begin
      assoc⇒ f g id₁ • (unitʳ⇒ (f ∘₁ g) ▷ id₁)
        ≈⟨ •-congʳ (triangle (f ∘₁ g) id₁) ⟩
      assoc⇒ f g id₁ • (((f ∘₁ g) ◁ unitˡ⇒ id₁) • assoc⇒ (f ∘₁ g) id₁ id₁)
        ≈⟨ ≈-sym •-assoc ⟩
      (assoc⇒ f g id₁ • ((f ∘₁ g) ◁ unitˡ⇒ id₁)) • assoc⇒ (f ∘₁ g) id₁ id₁
        ≈⟨ •-congˡ (•-congʳ (∗-cong (≈-sym (∗-id f g)) ≈-refl)) ⟩
      (assoc⇒ f g id₁ • ((id₂ {f = f} ∗ id₂ {f = g}) ∗ unitˡ⇒ id₁))
        • assoc⇒ (f ∘₁ g) id₁ id₁
        ≈⟨ •-congˡ (≈-sym (assoc-natural (id₂ {f = f}) (id₂ {f = g}) (unitˡ⇒ id₁))) ⟩
      ((f ◁ (g ◁ unitˡ⇒ id₁)) • assoc⇒ f g (id₁ ∘₁ id₁)) • assoc⇒ (f ∘₁ g) id₁ id₁
        ≈⟨ •-assoc ⟩
      (f ◁ (g ◁ unitˡ⇒ id₁)) • (assoc⇒ f g (id₁ ∘₁ id₁) • assoc⇒ (f ∘₁ g) id₁ id₁)
        ≈⟨ •-congʳ (pentagon f g id₁ id₁) ⟩
      (f ◁ (g ◁ unitˡ⇒ id₁)) •
        ((f ◁ assoc⇒ g id₁ id₁) • (assoc⇒ f (g ∘₁ id₁) id₁ • (assoc⇒ f g id₁ ▷ id₁)))
        ≈⟨ ≈-sym •-assoc ⟩
      ((f ◁ (g ◁ unitˡ⇒ id₁)) • (f ◁ assoc⇒ g id₁ id₁)) •
        (assoc⇒ f (g ∘₁ id₁) id₁ • (assoc⇒ f g id₁ ▷ id₁))
        ≈⟨ •-congˡ (≈-sym (◁-• f (g ◁ unitˡ⇒ id₁) (assoc⇒ g id₁ id₁))) ⟩
      (f ◁ ((g ◁ unitˡ⇒ id₁) • assoc⇒ g id₁ id₁)) •
        (assoc⇒ f (g ∘₁ id₁) id₁ • (assoc⇒ f g id₁ ▷ id₁))
        ≈⟨ •-congˡ (◁-cong f (≈-sym (triangle g id₁))) ⟩
      (f ◁ (unitʳ⇒ g ▷ id₁)) • (assoc⇒ f (g ∘₁ id₁) id₁ • (assoc⇒ f g id₁ ▷ id₁))
        ≈⟨ ≈-sym •-assoc ⟩
      ((f ◁ (unitʳ⇒ g ▷ id₁)) • assoc⇒ f (g ∘₁ id₁) id₁) • (assoc⇒ f g id₁ ▷ id₁)
        ≈⟨ •-congˡ (assoc-natural (id₂ {f = f}) (unitʳ⇒ g) (id₂ {f = id₁})) ⟩
      (assoc⇒ f g id₁ • ((f ◁ unitʳ⇒ g) ▷ id₁)) • (assoc⇒ f g id₁ ▷ id₁)
        ≈⟨ •-assoc ⟩
      assoc⇒ f g id₁ • (((f ◁ unitʳ⇒ g) ▷ id₁) • (assoc⇒ f g id₁ ▷ id₁))
        ≈⟨ •-congʳ (≈-sym (▷-• (f ◁ unitʳ⇒ g) (assoc⇒ f g id₁) id₁)) ⟩
      assoc⇒ f g id₁ • (((f ◁ unitʳ⇒ g) • assoc⇒ f g id₁) ▷ id₁) ∎))
    where open ⇒₂-Reasoning

  -- the same laws with the unitors read in the other direction
  unitˡ-∘' : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
             (unitˡ⇒ f ▷ g) • assoc⇐ id₁ f g ≈ unitˡ⇒ (f ∘₁ g)
  unitˡ-∘' f g =
    ≈-trans (•-congˡ (≈-sym (unitˡ-∘ f g)))
    (≈-trans •-assoc
    (≈-trans (•-congʳ (≅₂isoʳ (associator id₁ f g))) •-identityʳ))

  unitˡ⇐-∘ : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
             assoc⇒ id₁ f g • (unitˡ⇐ f ▷ g) ≈ unitˡ⇐ (f ∘₁ g)
  unitˡ⇐-∘ f g = Hom.∘-cancelˡ (invertible-≅₂ (unitorˡ (f ∘₁ g)))
    (≈-trans (≈-sym •-assoc)
    (≈-trans (•-congˡ (unitˡ-∘ f g))
    (≈-trans (≈-sym (▷-• (unitˡ⇒ f) (unitˡ⇐ f) g))
    (≈-trans (▷-cong g (≅₂isoʳ (unitorˡ f)))
    (≈-trans (▷-id f g) (≈-sym (≅₂isoʳ (unitorˡ (f ∘₁ g)))))))))

  unitʳ⇐-∘ : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
             assoc⇐ f g id₁ • (f ◁ unitʳ⇐ g) ≈ unitʳ⇐ (f ∘₁ g)
  unitʳ⇐-∘ f g = Hom.∘-cancelˡ (invertible-≅₂ (unitorʳ (f ∘₁ g))) (begin
    unitʳ⇒ (f ∘₁ g) • (assoc⇐ f g id₁ • (f ◁ unitʳ⇐ g))
      ≈⟨ •-congˡ (unitʳ-∘ f g) ⟩
    ((f ◁ unitʳ⇒ g) • assoc⇒ f g id₁) • (assoc⇐ f g id₁ • (f ◁ unitʳ⇐ g))
      ≈⟨ •-assoc ⟩
    (f ◁ unitʳ⇒ g) • (assoc⇒ f g id₁ • (assoc⇐ f g id₁ • (f ◁ unitʳ⇐ g)))
      ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
    (f ◁ unitʳ⇒ g) • ((assoc⇒ f g id₁ • assoc⇐ f g id₁) • (f ◁ unitʳ⇐ g))
      ≈⟨ •-congʳ (•-congˡ (≅₂isoʳ (associator f g id₁))) ⟩
    (f ◁ unitʳ⇒ g) • (id₂ • (f ◁ unitʳ⇐ g))
      ≈⟨ •-congʳ •-identityˡ ⟩
    (f ◁ unitʳ⇒ g) • (f ◁ unitʳ⇐ g)
      ≈⟨ ≈-sym (◁-• f (unitʳ⇒ g) (unitʳ⇐ g)) ⟩
    f ◁ (unitʳ⇒ g • unitʳ⇐ g)
      ≈⟨ ◁-cong f (≅₂isoʳ (unitorʳ g)) ⟩
    f ◁ id₂
      ≈⟨ ◁-id f g ⟩
    id₂
      ≈⟨ ≈-sym (≅₂isoʳ (unitorʳ (f ∘₁ g))) ⟩
    unitʳ⇒ (f ∘₁ g) • unitʳ⇐ (f ∘₁ g) ∎)
    where open ⇒₂-Reasoning

  -- the triangle, with both unitors read in the other direction
  triangle⇐ : {A B C : Obj} (f : B ⇒₁ C) (g : A ⇒₁ B) →
              assoc⇐ f id₁ g • (f ◁ unitˡ⇐ g) ≈ unitʳ⇐ f ▷ g
  triangle⇐ f g = Hom.∘-cancelˡ (invertible-≅₂ (unitorʳ f ▷≅ g))
    (≈-trans (≈-sym •-assoc)
    (≈-trans (•-congˡ (≈-trans (•-congˡ (triangle f g))
                      (≈-trans •-assoc
                      (≈-trans (•-congʳ (≅₂isoʳ (associator f id₁ g)))
                               •-identityʳ))))
    (≈-trans (≈-sym (◁-• f (unitˡ⇒ g) (unitˡ⇐ g)))
    (≈-trans (◁-cong f (≅₂isoʳ (unitorˡ g)))
    (≈-trans (◁-id f g)
    (≈-trans (≈-sym (▷-id f g))
    (≈-trans (▷-cong g (≈-sym (≅₂isoʳ (unitorʳ f))))
             (▷-• (unitʳ⇒ f) (unitʳ⇐ f) g))))))))

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

  ----------------------------------------------------------------------
  -- Pasting of squares
  ----------------------------------------------------------------------

  -- A "square" is a 2-cell u₂ ∘ p ⇒ q ∘ u₁, thought of as filling
  --
  --          p
  --     ∙ -------> ∙
  --     |          |
  --  u₁ |    σ     | u₂        (read as u₂ ∘ p ⇒ q ∘ u₁)
  --     v          v
  --     ∙ -------> ∙
  --          q
  --
  -- Two such squares paste side by side. The pasting is associative up
  -- to the associators of the two rows, which is paste-assoc.
  -- the pentagon, with every associator inverted
  pentagon⇐ : {A B C D E : Obj} (f : D ⇒₁ E) (g : C ⇒₁ D) (h : B ⇒₁ C) (k : A ⇒₁ B) →
              assoc⇐ (f ∘₁ g) h k • assoc⇐ f g (h ∘₁ k)
              ≈ ((assoc⇐ f g h ▷ k) • assoc⇐ f (g ∘₁ h) k) • (f ◁ assoc⇐ g h k)
  pentagon⇐ f g h k = Hom.inv-resp
    (Hom.∘-invertible (invertible-≅₂ (associator f g (h ∘₁ k)))
                      (invertible-≅₂ (associator (f ∘₁ g) h k)))
    (Hom.∘-invertible (invertible-≅₂ (f ◁≅ associator g h k))
      (Hom.∘-invertible (invertible-≅₂ (associator f (g ∘₁ h) k))
                        (invertible-≅₂ (associator f g h ▷≅ k))))
    (pentagon f g h k)

  paste : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
          (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
          (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) →
          (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁) → (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀) →
          (u₂ ∘₁ (p₂ ∘₁ p₁)) ⇒₂ ((q₂ ∘₁ q₁) ∘₁ u₀)
  paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ =
    assoc⇐ q₂ q₁ u₀ •
      ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)))

  paste-cong : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
               (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
               (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
               {σ' σ'' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)}
               {σ σ''' : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀)} →
               σ' ≈ σ'' → σ ≈ σ''' →
               paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ
               ≈ paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ'' σ'''
  paste-cong u₀ u₁ u₂ p₁ p₂ q₁ q₂ p p' =
    •-congʳ (•-cong (◁-cong q₂ p') (•-congʳ (•-congˡ (▷-cong p₁ p))))

  paste-assoc :
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Obj}
    (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂) (u₃ : a₃ ⇒₁ b₃)
    (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (p₃ : a₂ ⇒₁ a₃)
    (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) (q₃ : b₂ ⇒₁ b₃)
    (σ₃ : (u₃ ∘₁ p₃) ⇒₂ (q₃ ∘₁ u₂)) (σ₂ : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁))
    (σ₁ : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀)) →
    (assoc⇒ q₃ q₂ q₁ ▷ u₀) •
      paste u₀ u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) σ₁
    ≈ paste u₀ u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
        (paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁)
        • (u₃ ◁ assoc⇒ p₃ p₂ p₁)
  paste-assoc u₀ u₁ u₂ u₃ p₁ p₂ p₃ q₁ q₂ q₃ σ₃ σ₂ σ₁ = begin
    (assoc⇒ q₃ q₂ q₁ ▷ u₀) •
      paste u₀ u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) σ₁
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ expandL))) ⟩
    L10 • (L9 • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))) 
      ≈⟨ ≈-sym •-assoc ⟩
    (L10 • L9) • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congˡ step1 ⟩
    (R10 • (R9 • A₁)) • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-assoc ⟩
    R10 • ((R9 • A₁) • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ •-assoc ⟩
    R10 • (R9 • (A₁ • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    R10 • (R9 • ((A₁ • L8) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ step2)) ⟩
    R10 • (R9 • ((R8 • A₂) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    R10 • (R9 • (R8 • (A₂ • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))) 
      ≈⟨ •-congʳ (•-congʳ (•-congʳ
           (≈-trans (•-congʳ (≈-sym •-assoc)) (≈-sym •-assoc)))) ⟩
    R10 • (R9 • (R8 • ((A₂ • (L7 • L6)) • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ step3))) ⟩
    R10 • (R9 • (R8 • ((R7 • A₃) • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    R10 • (R9 • (R8 • (R7 • (A₃ • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc)))) ⟩
    R10 • (R9 • (R8 • (R7 • ((A₃ • L5) • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congˡ step4)))) ⟩
    R10 • (R9 • (R8 • (R7 • ((R6 • A₄) • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ •-assoc))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (A₄ • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • ((A₄ • L4) • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congˡ step5))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • ((R5 • (R4 • A₅)) • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (≈-trans •-assoc (•-congʳ •-assoc)))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (A₅ • (L3 • (L2 • L1)))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (≈-sym •-assoc))))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • ((A₅ • L3) • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (•-congˡ step6))))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • ((R3 • A₆) • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           •-assoc)))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (A₆ • (L2 • L1)))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (•-congʳ step7))))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))))
      ≈⟨ ≈-sym expandR ⟩
    paste u₀ u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
      (paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁)
      • (u₃ ◁ assoc⇒ p₃ p₂ p₁) ∎
    where
      open ⇒₂-Reasoning

      L1  = assoc⇐ u₃ (p₃ ∘₁ p₂) p₁
      L2  = assoc⇐ u₃ p₃ p₂ ▷ p₁
      L3  = (σ₃ ▷ p₂) ▷ p₁
      L4  = assoc⇒ q₃ u₂ p₂ ▷ p₁
      L5  = (q₃ ◁ σ₂) ▷ p₁
      L6  = assoc⇐ q₃ q₂ u₁ ▷ p₁
      L7  = assoc⇒ (q₃ ∘₁ q₂) u₁ p₁
      L8  = (q₃ ∘₁ q₂) ◁ σ₁
      L9  = assoc⇐ (q₃ ∘₁ q₂) q₁ u₀
      L10 = assoc⇒ q₃ q₂ q₁ ▷ u₀

      R1  = u₃ ◁ assoc⇒ p₃ p₂ p₁
      R2  = assoc⇐ u₃ p₃ (p₂ ∘₁ p₁)
      R3  = σ₃ ▷ (p₂ ∘₁ p₁)
      R4  = assoc⇒ q₃ u₂ (p₂ ∘₁ p₁)
      R5  = q₃ ◁ assoc⇐ u₂ p₂ p₁
      R6  = q₃ ◁ (σ₂ ▷ p₁)
      R7  = q₃ ◁ assoc⇒ q₂ u₁ p₁
      R8  = q₃ ◁ (q₂ ◁ σ₁)
      R9  = q₃ ◁ assoc⇐ q₂ q₁ u₀
      R10 = assoc⇐ q₃ (q₂ ∘₁ q₁) u₀

      A₁ = assoc⇒ q₃ q₂ (q₁ ∘₁ u₀)
      A₂ = assoc⇒ q₃ q₂ (u₁ ∘₁ p₁)
      A₃ = assoc⇒ q₃ (q₂ ∘₁ u₁) p₁
      A₄ = assoc⇒ q₃ (u₂ ∘₁ p₂) p₁
      A₅ = assoc⇒ (q₃ ∘₁ u₂) p₂ p₁
      A₆ = assoc⇒ (u₃ ∘₁ p₃) p₂ p₁

      -- the two pastings, flattened
      expandL : (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁) • L1
                ≈ L6 • (L5 • (L4 • (L3 • (L2 • L1))))
      expandL = ≈-trans (•-congˡ expand▷)
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc))))))
        where
          expand▷ : paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁
                    ≈ L6 • (L5 • (L4 • (L3 • L2)))
          expand▷ =
            ≈-trans (▷-• (assoc⇐ q₃ q₂ u₁)
                         ((q₃ ◁ σ₂) • (assoc⇒ q₃ u₂ p₂
                           • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂))) p₁)
            (•-congʳ (≈-trans (▷-• (q₃ ◁ σ₂)
                         (assoc⇒ q₃ u₂ p₂ • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂)) p₁)
            (•-congʳ (≈-trans (▷-• (assoc⇒ q₃ u₂ p₂)
                         ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂) p₁)
            (•-congʳ (▷-• (σ₃ ▷ p₂) (assoc⇐ u₃ p₃ p₂) p₁))))))

      expandR : paste u₀ u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
                  (paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁)
                  • (u₃ ◁ assoc⇒ p₃ p₂ p₁)
                ≈ R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))))
      expandR = ≈-trans (•-congˡ (•-congʳ (•-congˡ expand◁)))
                (≈-trans (•-congˡ (•-congʳ
                  (≈-trans •-assoc (•-congʳ
                  (≈-trans •-assoc (•-congʳ
                  (≈-trans •-assoc (•-congʳ •-assoc))))))))
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc)))))))))))))))
        where
          expand◁ : q₃ ◁ paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁
                    ≈ R9 • (R8 • (R7 • (R6 • R5)))
          expand◁ =
            ≈-trans (◁-• q₃ (assoc⇐ q₂ q₁ u₀)
                         ((q₂ ◁ σ₁) • (assoc⇒ q₂ u₁ p₁
                           • ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁))))
            (•-congʳ (≈-trans (◁-• q₃ (q₂ ◁ σ₁)
                         (assoc⇒ q₂ u₁ p₁ • ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁)))
            (•-congʳ (≈-trans (◁-• q₃ (assoc⇒ q₂ u₁ p₁)
                         ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁))
            (•-congʳ (◁-• q₃ (σ₂ ▷ p₁) (assoc⇐ u₂ p₂ p₁)))))))

      -- the pentagon at (q₃,q₂,q₁,u₀), with two associators inverted
      step1 : L10 • L9 ≈ R10 • (R9 • A₁)
      step1 = Hom.∘-cancelˡ
        (Hom.∘-invertible (invertible-≅₂ (q₃ ◁≅ associator q₂ q₁ u₀))
                          (invertible-≅₂ (associator q₃ (q₂ ∘₁ q₁) u₀)))
        (begin
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • assoc⇒ q₃ (q₂ ∘₁ q₁) u₀) • (L10 • L9)
            ≈⟨ •-assoc ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • (assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • (L10 • L9))
            ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • ((assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • L10) • L9)
            ≈⟨ ≈-sym •-assoc ⟩
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • (assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • L10)) • L9
            ≈⟨ •-congˡ (≈-sym (pentagon q₃ q₂ q₁ u₀)) ⟩
          (A₁ • assoc⇒ (q₃ ∘₁ q₂) q₁ u₀) • L9
            ≈⟨ •-assoc ⟩
          A₁ • (assoc⇒ (q₃ ∘₁ q₂) q₁ u₀ • L9)
            ≈⟨ •-congʳ (≅₂isoʳ (associator (q₃ ∘₁ q₂) q₁ u₀)) ⟩
          A₁ • id₂
            ≈⟨ •-identityʳ ⟩
          A₁
            ≈⟨ ≈-sym •-identityˡ ⟩
          id₂ • A₁
            ≈⟨ •-congˡ (≈-sym (≈-trans (≈-sym (◁-• q₃ (assoc⇒ q₂ q₁ u₀)
                                                     (assoc⇐ q₂ q₁ u₀)))
                              (≈-trans (◁-cong q₃ (≅₂isoʳ (associator q₂ q₁ u₀)))
                                       (◁-id q₃ (q₂ ∘₁ (q₁ ∘₁ u₀)))))) ⟩
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • R9) • A₁
            ≈⟨ •-assoc ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • (R9 • A₁)
            ≈⟨ •-congʳ (≈-sym (≈-trans (•-congˡ (≅₂isoʳ (associator q₃ (q₂ ∘₁ q₁) u₀)))
                                       •-identityˡ)) ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • ((assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • R10) • (R9 • A₁))
            ≈⟨ •-congʳ •-assoc ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • (assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • (R10 • (R9 • A₁)))
            ≈⟨ ≈-sym •-assoc ⟩
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • assoc⇒ q₃ (q₂ ∘₁ q₁) u₀) • (R10 • (R9 • A₁)) ∎)

      -- naturality of the associator in the last variable
      step2 : A₁ • L8 ≈ R8 • A₂
      step2 = ≈-sym (≈-trans (assoc-natural (id₂ {f = q₃}) (id₂ {f = q₂}) σ₁)
                             (•-congʳ (∗-cong (∗-id q₃ q₂) ≈-refl)))

      -- the pentagon at (q₃,q₂,u₁,p₁)
      step3 : A₂ • (L7 • L6) ≈ R7 • A₃
      step3 = begin
        A₂ • (L7 • L6)
          ≈⟨ ≈-sym •-assoc ⟩
        (A₂ • L7) • L6
          ≈⟨ •-congˡ (pentagon q₃ q₂ u₁ p₁) ⟩
        (R7 • (A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁))) • L6
          ≈⟨ •-assoc ⟩
        R7 • ((A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁)) • L6)
          ≈⟨ •-congʳ •-assoc ⟩
        R7 • (A₃ • ((assoc⇒ q₃ q₂ u₁ ▷ p₁) • L6))
          ≈⟨ •-congʳ (•-congʳ (≈-trans (≈-sym (▷-• (assoc⇒ q₃ q₂ u₁)
                                                   (assoc⇐ q₃ q₂ u₁) p₁))
                              (≈-trans (▷-cong p₁ (≅₂isoʳ (associator q₃ q₂ u₁)))
                                       (▷-id (q₃ ∘₁ (q₂ ∘₁ u₁)) p₁)))) ⟩
        R7 • (A₃ • id₂)
          ≈⟨ •-congʳ •-identityʳ ⟩
        R7 • A₃ ∎

      -- naturality of the associator in the middle variable
      step4 : A₃ • L5 ≈ R6 • A₄
      step4 = ≈-sym (assoc-natural (id₂ {f = q₃}) σ₂ (id₂ {f = p₁}))

      -- the pentagon at (q₃,u₂,p₂,p₁)
      step5 : A₄ • L4 ≈ R5 • (R4 • A₅)
      step5 = ≈-sym (begin
        R5 • (R4 • A₅)
          ≈⟨ •-congʳ (pentagon q₃ u₂ p₂ p₁) ⟩
        R5 • ((q₃ ◁ assoc⇒ u₂ p₂ p₁) • (A₄ • L4))
          ≈⟨ ≈-sym •-assoc ⟩
        (R5 • (q₃ ◁ assoc⇒ u₂ p₂ p₁)) • (A₄ • L4)
          ≈⟨ •-congˡ (≈-trans (≈-sym (◁-• q₃ (assoc⇐ u₂ p₂ p₁) (assoc⇒ u₂ p₂ p₁)))
                     (≈-trans (◁-cong q₃ (≅₂isoˡ (associator u₂ p₂ p₁)))
                              (◁-id q₃ ((u₂ ∘₁ p₂) ∘₁ p₁)))) ⟩
        id₂ • (A₄ • L4)
          ≈⟨ •-identityˡ ⟩
        A₄ • L4 ∎)

      -- naturality of the associator in the first variable
      step6 : A₅ • L3 ≈ R3 • A₆
      step6 = ≈-sym (≈-trans (•-congˡ (∗-cong ≈-refl (≈-sym (∗-id p₂ p₁))))
                             (assoc-natural σ₃ (id₂ {f = p₂}) (id₂ {f = p₁})))

      -- the pentagon at (u₃,p₃,p₂,p₁)
      step7 : A₆ • (L2 • L1) ≈ R2 • R1
      step7 = Hom.∘-cancelˡ (invertible-≅₂ (associator u₃ p₃ (p₂ ∘₁ p₁))) (begin
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (A₆ • (L2 • L1))
          ≈⟨ ≈-sym •-assoc ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • A₆) • (L2 • L1)
          ≈⟨ •-congˡ (pentagon u₃ p₃ p₂ p₁) ⟩
        (R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁))) • (L2 • L1)
          ≈⟨ •-assoc ⟩
        R1 • ((assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁)) • (L2 • L1))
          ≈⟨ •-congʳ •-assoc ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • ((assoc⇒ u₃ p₃ p₂ ▷ p₁) • (L2 • L1)))
          ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (((assoc⇒ u₃ p₃ p₂ ▷ p₁) • L2) • L1))
          ≈⟨ •-congʳ (•-congʳ (•-congˡ
               (≈-trans (≈-sym (▷-• (assoc⇒ u₃ p₃ p₂) (assoc⇐ u₃ p₃ p₂) p₁))
               (≈-trans (▷-cong p₁ (≅₂isoʳ (associator u₃ p₃ p₂)))
                        (▷-id (u₃ ∘₁ (p₃ ∘₁ p₂)) p₁))))) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (id₂ • L1))
          ≈⟨ •-congʳ (•-congʳ •-identityˡ) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • L1)
          ≈⟨ •-congʳ (≅₂isoʳ (associator u₃ (p₃ ∘₁ p₂) p₁)) ⟩
        R1 • id₂
          ≈⟨ •-identityʳ ⟩
        R1
          ≈⟨ ≈-sym •-identityˡ ⟩
        id₂ • R1
          ≈⟨ •-congˡ (≈-sym (≅₂isoʳ (associator u₃ p₃ (p₂ ∘₁ p₁)))) ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • R2) • R1
          ≈⟨ •-assoc ⟩
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (R2 • R1) ∎)

  -- the pasting is natural in its two squares: a 2-cell of the top row
  -- can be absorbed into the right-hand square…
  paste-▷ : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
            (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
            (p₁ : a₀ ⇒₁ a₁) (p₂ p₂' : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
            (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (σ : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀))
            (τ : p₂' ⇒₂ p₂) →
            paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (τ ▷ p₁))
            ≈ paste u₀ u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ τ)) σ
  paste-▷ u₀ u₁ u₂ p₁ p₂ p₂' q₁ q₂ σ' σ τ = begin
    paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (τ ▷ p₁))
      ≈⟨ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • (((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))) • (u₂ ◁ (τ ▷ p₁)))
      ≈⟨ •-congʳ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)) • (u₂ ◁ (τ ▷ p₁))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁) • (u₂ ◁ (τ ▷ p₁)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (τ ▷ p₁))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ
           (assoc-natural⇐ (id₂ {f = u₂}) τ (id₂ {f = p₁}))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (((u₂ ◁ τ) ▷ p₁) • assoc⇐ u₂ p₂' p₁))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • ((u₂ ◁ τ) ▷ p₁)) • assoc⇐ u₂ p₂' p₁)))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ
           (≈-sym (▷-• σ' (u₂ ◁ τ) p₁))))) ⟩
    paste u₀ u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ τ)) σ ∎
    where open ⇒₂-Reasoning

  -- …and one of the bottom row into the left-hand square
  paste-◁ : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
            (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
            (p₁ p₁' : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
            (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (σ : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀))
            (τ : p₁' ⇒₂ p₁) →
            paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (p₂ ◁ τ))
            ≈ paste u₀ u₁ u₂ p₁' p₂ q₁ q₂ σ' (σ • (u₁ ◁ τ))
  paste-◁ u₀ u₁ u₂ p₁ p₁' p₂ q₁ q₂ σ' σ τ = begin
    paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (p₂ ◁ τ))
      ≈⟨ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • (((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))) • (u₂ ◁ (p₂ ◁ τ)))
      ≈⟨ •-congʳ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)) • (u₂ ◁ (p₂ ◁ τ))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁) • (u₂ ◁ (p₂ ◁ τ)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (p₂ ◁ τ))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ
           (≈-trans (assoc-natural⇐ (id₂ {f = u₂}) (id₂ {f = p₂}) τ)
                    (•-congˡ (∗-cong (∗-id u₂ p₂) ≈-refl)))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (((u₂ ∘₁ p₂) ◁ τ) • assoc⇐ u₂ p₂ p₁'))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • ((u₂ ∘₁ p₂) ◁ τ)) • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ
           (≈-trans (≈-sym (∗-• σ' (id₂ {f = u₂ ∘₁ p₂}) (id₂ {f = p₁}) τ))
           (≈-trans (∗-cong •-identityʳ •-identityˡ)
                    (∗-decomposeʳ σ' τ)))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((((q₂ ∘₁ u₁) ◁ τ) • (σ' ▷ p₁')) • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((q₂ ∘₁ u₁) ◁ τ) • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((assoc⇒ q₂ u₁ p₁ • ((q₂ ∘₁ u₁) ◁ τ))
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ
           (≈-trans (•-congʳ (∗-cong (≈-sym (∗-id q₂ u₁)) ≈-refl))
                    (≈-sym (assoc-natural (id₂ {f = q₂}) (id₂ {f = u₁}) τ))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (((q₂ ◁ (u₁ ◁ τ)) • assoc⇒ q₂ u₁ p₁')
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((q₂ ◁ (u₁ ◁ τ)) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))))
      ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • (((q₂ ◁ σ) • (q₂ ◁ (u₁ ◁ τ))) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congˡ (≈-sym (◁-• q₂ σ (u₁ ◁ τ)))) ⟩
    paste u₀ u₁ u₂ p₁' p₂ q₁ q₂ σ' (σ • (u₁ ◁ τ)) ∎
    where open ⇒₂-Reasoning

  -- The same pasting where the last square has no bottom-left leg: its
  -- 2-cell is u₁ ∘ p₁ ⇒ q₁ instead of u₁ ∘ p₁ ⇒ q₁ ∘ u₀. This is the
  -- shape a universal arrow produces, ε being a square of that kind.
  fpaste : {a₀ a₁ a₂ b₁ b₂ : Obj}
           (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
           (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) →
           (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁) → (u₁ ∘₁ p₁) ⇒₂ q₁ →
           (u₂ ∘₁ (p₂ ∘₁ p₁)) ⇒₂ (q₂ ∘₁ q₁)
  fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ =
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))

  fpaste-cong : {a₀ a₁ a₂ b₁ b₂ : Obj}
                (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
                (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
                {σ' σ'' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)}
                {τ τ' : (u₁ ∘₁ p₁) ⇒₂ q₁} →
                σ' ≈ σ'' → τ ≈ τ' →
                fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ ≈ fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ'' τ'
  fpaste-cong u₁ u₂ p₁ p₂ q₁ q₂ p p' =
    •-cong (◁-cong q₂ p') (•-congʳ (•-congˡ (▷-cong p₁ p)))

  fpaste-▷ : {a₀ a₁ a₂ b₁ b₂ : Obj}
             (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
             (p₁ : a₀ ⇒₁ a₁) (p₂ p₂' : a₁ ⇒₁ a₂)
             (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
             (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (τ : (u₁ ∘₁ p₁) ⇒₂ q₁)
             (κ : p₂' ⇒₂ p₂) →
             fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (κ ▷ p₁))
             ≈ fpaste u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ κ)) τ
  fpaste-▷ u₁ u₂ p₁ p₂ p₂' q₁ q₂ σ' τ κ = begin
    fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (κ ▷ p₁))
      ≈⟨ •-assoc ⟩
    (q₂ ◁ τ) • ((assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))
      • (u₂ ◁ (κ ▷ p₁)))
      ≈⟨ •-congʳ •-assoc ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)
      • (u₂ ◁ (κ ▷ p₁))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (κ ▷ p₁)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ
           (assoc-natural⇐ (id₂ {f = u₂}) κ (id₂ {f = p₁})))) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (((u₂ ◁ κ) ▷ p₁) • assoc⇐ u₂ p₂' p₁)))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • ((u₂ ◁ κ) ▷ p₁))
      • assoc⇐ u₂ p₂' p₁))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ (≈-sym (▷-• σ' (u₂ ◁ κ) p₁)))) ⟩
    fpaste u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ κ)) τ ∎
    where open ⇒₂-Reasoning

  fpaste-◁ : {a₀ a₁ a₂ b₁ b₂ : Obj}
             (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
             (p₁ p₁' : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂)
             (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
             (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (τ : (u₁ ∘₁ p₁) ⇒₂ q₁)
             (κ : p₁' ⇒₂ p₁) →
             fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (p₂ ◁ κ))
             ≈ fpaste u₁ u₂ p₁' p₂ q₁ q₂ σ' (τ • (u₁ ◁ κ))
  fpaste-◁ u₁ u₂ p₁ p₁' p₂ q₁ q₂ σ' τ κ = begin
    fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (p₂ ◁ κ))
      ≈⟨ •-assoc ⟩
    (q₂ ◁ τ) • ((assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))
      • (u₂ ◁ (p₂ ◁ κ)))
      ≈⟨ •-congʳ •-assoc ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)
      • (u₂ ◁ (p₂ ◁ κ))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (p₂ ◁ κ)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ
           (≈-trans (assoc-natural⇐ (id₂ {f = u₂}) (id₂ {f = p₂}) κ)
                    (•-congˡ (∗-cong (∗-id u₂ p₂) ≈-refl))))) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (((u₂ ∘₁ p₂) ◁ κ) • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • ((u₂ ∘₁ p₂) ◁ κ))
      • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ
           (≈-trans (≈-sym (∗-• σ' (id₂ {f = u₂ ∘₁ p₂}) (id₂ {f = p₁}) κ))
           (≈-trans (∗-cong •-identityʳ •-identityˡ)
                    (∗-decomposeʳ σ' κ))))) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((((q₂ ∘₁ u₁) ◁ κ) • (σ' ▷ p₁'))
      • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((q₂ ∘₁ u₁) ◁ κ)
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
    (q₂ ◁ τ) • ((assoc⇒ q₂ u₁ p₁ • ((q₂ ∘₁ u₁) ◁ κ))
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ (•-congˡ
           (≈-trans (•-congʳ (∗-cong (≈-sym (∗-id q₂ u₁)) ≈-refl))
                    (≈-sym (assoc-natural (id₂ {f = q₂}) (id₂ {f = u₁}) κ)))) ⟩
    (q₂ ◁ τ) • (((q₂ ◁ (u₁ ◁ κ)) • assoc⇒ q₂ u₁ p₁')
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ •-assoc ⟩
    (q₂ ◁ τ) • ((q₂ ◁ (u₁ ◁ κ)) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ ≈-sym •-assoc ⟩
    ((q₂ ◁ τ) • (q₂ ◁ (u₁ ◁ κ))) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congˡ (≈-sym (◁-• q₂ τ (u₁ ◁ κ))) ⟩
    fpaste u₁ u₂ p₁' p₂ q₁ q₂ σ' (τ • (u₁ ◁ κ)) ∎
    where open ⇒₂-Reasoning

  fpaste-assoc :
    {a₀ a₁ a₂ a₃ b₁ b₂ b₃ : Obj}
    (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂) (u₃ : a₃ ⇒₁ b₃)
    (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (p₃ : a₂ ⇒₁ a₃)
    (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) (q₃ : b₂ ⇒₁ b₃)
    (σ₃ : (u₃ ∘₁ p₃) ⇒₂ (q₃ ∘₁ u₂)) (σ₂ : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁))
    (τ : (u₁ ∘₁ p₁) ⇒₂ q₁) →
    assoc⇒ q₃ q₂ q₁ •
      fpaste u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) τ
    ≈ fpaste u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
        (fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ)
        • (u₃ ◁ assoc⇒ p₃ p₂ p₁)
  fpaste-assoc u₁ u₂ u₃ p₁ p₂ p₃ q₁ q₂ q₃ σ₃ σ₂ τ = begin
    assoc⇒ q₃ q₂ q₁ •
      fpaste u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) τ
      ≈⟨ •-congʳ (•-congʳ (•-congʳ expandL)) ⟩
    L9 • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ ≈-sym •-assoc ⟩
    (L9 • L8) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-congˡ step2 ⟩
    (R8 • A₂) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-assoc ⟩
    R8 • (A₂ • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (≈-trans (•-congʳ (≈-sym •-assoc)) (≈-sym •-assoc)) ⟩
    R8 • ((A₂ • (L7 • L6)) • (L5 • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congˡ step3) ⟩
    R8 • ((R7 • A₃) • (L5 • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ •-assoc ⟩
    R8 • (R7 • (A₃ • (L5 • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    R8 • (R7 • ((A₃ • L5) • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ step4)) ⟩
    R8 • (R7 • ((R6 • A₄) • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    R8 • (R7 • (R6 • (A₄ • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))) ⟩
    R8 • (R7 • (R6 • ((A₄ • L4) • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ step5))) ⟩
    R8 • (R7 • (R6 • ((R5 • (R4 • A₅)) • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-trans •-assoc (•-congʳ •-assoc)))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • (A₅ • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • ((A₅ • L3) • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congˡ step6))))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • ((R3 • A₆) • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ •-assoc)))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (A₆ • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ step7))))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))
      ≈⟨ ≈-sym expandR ⟩
    fpaste u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
      (fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ)
      • (u₃ ◁ assoc⇒ p₃ p₂ p₁) ∎
    where
      open ⇒₂-Reasoning

      L1 = assoc⇐ u₃ (p₃ ∘₁ p₂) p₁
      L2 = assoc⇐ u₃ p₃ p₂ ▷ p₁
      L3 = (σ₃ ▷ p₂) ▷ p₁
      L4 = assoc⇒ q₃ u₂ p₂ ▷ p₁
      L5 = (q₃ ◁ σ₂) ▷ p₁
      L6 = assoc⇐ q₃ q₂ u₁ ▷ p₁
      L7 = assoc⇒ (q₃ ∘₁ q₂) u₁ p₁
      L8 = (q₃ ∘₁ q₂) ◁ τ
      L9 = assoc⇒ q₃ q₂ q₁

      R1 = u₃ ◁ assoc⇒ p₃ p₂ p₁
      R2 = assoc⇐ u₃ p₃ (p₂ ∘₁ p₁)
      R3 = σ₃ ▷ (p₂ ∘₁ p₁)
      R4 = assoc⇒ q₃ u₂ (p₂ ∘₁ p₁)
      R5 = q₃ ◁ assoc⇐ u₂ p₂ p₁
      R6 = q₃ ◁ (σ₂ ▷ p₁)
      R7 = q₃ ◁ assoc⇒ q₂ u₁ p₁
      R8 = q₃ ◁ (q₂ ◁ τ)

      A₂ = assoc⇒ q₃ q₂ (u₁ ∘₁ p₁)
      A₃ = assoc⇒ q₃ (q₂ ∘₁ u₁) p₁
      A₄ = assoc⇒ q₃ (u₂ ∘₁ p₂) p₁
      A₅ = assoc⇒ (q₃ ∘₁ u₂) p₂ p₁
      A₆ = assoc⇒ (u₃ ∘₁ p₃) p₂ p₁

      expandL : (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁) • L1
                ≈ L6 • (L5 • (L4 • (L3 • (L2 • L1))))
      expandL = ≈-trans (•-congˡ expand▷)
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc))))))
        where
          expand▷ : paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁
                    ≈ L6 • (L5 • (L4 • (L3 • L2)))
          expand▷ =
            ≈-trans (▷-• (assoc⇐ q₃ q₂ u₁)
                         ((q₃ ◁ σ₂) • (assoc⇒ q₃ u₂ p₂
                           • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂))) p₁)
            (•-congʳ (≈-trans (▷-• (q₃ ◁ σ₂)
                         (assoc⇒ q₃ u₂ p₂ • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂)) p₁)
            (•-congʳ (≈-trans (▷-• (assoc⇒ q₃ u₂ p₂)
                         ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂) p₁)
            (•-congʳ (▷-• (σ₃ ▷ p₂) (assoc⇐ u₃ p₃ p₂) p₁))))))

      expandR : fpaste u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
                  (fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ) • R1
                ≈ R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))
      expandR = ≈-trans (•-congˡ (•-congˡ expand◁))
                (≈-trans (•-congˡ
                  (≈-trans •-assoc (•-congʳ
                  (≈-trans •-assoc (•-congʳ •-assoc)))))
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc)))))))))))
        where
          expand◁ : q₃ ◁ fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ
                    ≈ R8 • (R7 • (R6 • R5))
          expand◁ =
            ≈-trans (◁-• q₃ (q₂ ◁ τ)
                         (assoc⇒ q₂ u₁ p₁ • ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁)))
            (•-congʳ (≈-trans (◁-• q₃ (assoc⇒ q₂ u₁ p₁)
                         ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁))
            (•-congʳ (◁-• q₃ (σ₂ ▷ p₁) (assoc⇐ u₂ p₂ p₁)))))

      step2 : L9 • L8 ≈ R8 • A₂
      step2 = ≈-sym (≈-trans (assoc-natural (id₂ {f = q₃}) (id₂ {f = q₂}) τ)
                             (•-congʳ (∗-cong (∗-id q₃ q₂) ≈-refl)))

      step3 : A₂ • (L7 • L6) ≈ R7 • A₃
      step3 = begin
        A₂ • (L7 • L6)
          ≈⟨ ≈-sym •-assoc ⟩
        (A₂ • L7) • L6
          ≈⟨ •-congˡ (pentagon q₃ q₂ u₁ p₁) ⟩
        (R7 • (A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁))) • L6
          ≈⟨ •-assoc ⟩
        R7 • ((A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁)) • L6)
          ≈⟨ •-congʳ •-assoc ⟩
        R7 • (A₃ • ((assoc⇒ q₃ q₂ u₁ ▷ p₁) • L6))
          ≈⟨ •-congʳ (•-congʳ (≈-trans (≈-sym (▷-• (assoc⇒ q₃ q₂ u₁)
                                                   (assoc⇐ q₃ q₂ u₁) p₁))
                              (≈-trans (▷-cong p₁ (≅₂isoʳ (associator q₃ q₂ u₁)))
                                       (▷-id (q₃ ∘₁ (q₂ ∘₁ u₁)) p₁)))) ⟩
        R7 • (A₃ • id₂)
          ≈⟨ •-congʳ •-identityʳ ⟩
        R7 • A₃ ∎

      step4 : A₃ • L5 ≈ R6 • A₄
      step4 = ≈-sym (assoc-natural (id₂ {f = q₃}) σ₂ (id₂ {f = p₁}))

      step5 : A₄ • L4 ≈ R5 • (R4 • A₅)
      step5 = ≈-sym (begin
        R5 • (R4 • A₅)
          ≈⟨ •-congʳ (pentagon q₃ u₂ p₂ p₁) ⟩
        R5 • ((q₃ ◁ assoc⇒ u₂ p₂ p₁) • (A₄ • L4))
          ≈⟨ ≈-sym •-assoc ⟩
        (R5 • (q₃ ◁ assoc⇒ u₂ p₂ p₁)) • (A₄ • L4)
          ≈⟨ •-congˡ (≈-trans (≈-sym (◁-• q₃ (assoc⇐ u₂ p₂ p₁)
                                              (assoc⇒ u₂ p₂ p₁)))
                     (≈-trans (◁-cong q₃ (≅₂isoˡ (associator u₂ p₂ p₁)))
                              (◁-id q₃ ((u₂ ∘₁ p₂) ∘₁ p₁)))) ⟩
        id₂ • (A₄ • L4)
          ≈⟨ •-identityˡ ⟩
        A₄ • L4 ∎)

      step6 : A₅ • L3 ≈ R3 • A₆
      step6 = ≈-sym (≈-trans (•-congˡ (∗-cong ≈-refl (≈-sym (∗-id p₂ p₁))))
                             (assoc-natural σ₃ (id₂ {f = p₂}) (id₂ {f = p₁})))

      step7 : A₆ • (L2 • L1) ≈ R2 • R1
      step7 = Hom.∘-cancelˡ (invertible-≅₂ (associator u₃ p₃ (p₂ ∘₁ p₁))) (begin
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (A₆ • (L2 • L1))
          ≈⟨ ≈-sym •-assoc ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • A₆) • (L2 • L1)
          ≈⟨ •-congˡ (pentagon u₃ p₃ p₂ p₁) ⟩
        (R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁))) • (L2 • L1)
          ≈⟨ •-assoc ⟩
        R1 • ((assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁)) • (L2 • L1))
          ≈⟨ •-congʳ •-assoc ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • ((assoc⇒ u₃ p₃ p₂ ▷ p₁) • (L2 • L1)))
          ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (((assoc⇒ u₃ p₃ p₂ ▷ p₁) • L2) • L1))
          ≈⟨ •-congʳ (•-congʳ (•-congˡ
               (≈-trans (≈-sym (▷-• (assoc⇒ u₃ p₃ p₂) (assoc⇐ u₃ p₃ p₂) p₁))
               (≈-trans (▷-cong p₁ (≅₂isoʳ (associator u₃ p₃ p₂)))
                        (▷-id (u₃ ∘₁ (p₃ ∘₁ p₂)) p₁))))) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (id₂ • L1))
          ≈⟨ •-congʳ (•-congʳ •-identityˡ) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • L1)
          ≈⟨ •-congʳ (≅₂isoʳ (associator u₃ (p₃ ∘₁ p₂) p₁)) ⟩
        R1 • id₂
          ≈⟨ •-identityʳ ⟩
        R1
          ≈⟨ ≈-sym •-identityˡ ⟩
        id₂ • R1
          ≈⟨ •-congˡ (≈-sym (≅₂isoʳ (associator u₃ p₃ (p₂ ∘₁ p₁)))) ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • R2) • R1
          ≈⟨ •-assoc ⟩
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (R2 • R1) ∎)
