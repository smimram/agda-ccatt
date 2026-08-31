------------------------------------------------------------------------
-- Categories, in the setoid approach: the morphisms between two given
-- objects form a setoid, i.e. they are equipped with an equivalence
-- relation _≈_ which plays the role of equality between morphisms.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import Category as Cat
--   open Cat using (Category)
--
-- so that "open Category C" unambiguously refers to the record module.

module Category where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)

record Category (o ℓ e : Level) : Set (suc (o ⊔ ℓ ⊔ e)) where
  eta-equality

  infix  4 _⇒_
  infix  4 _≈_
  infixr 9 _∘_

  field
    -- objects
    Obj : Set o
    -- morphisms
    _⇒_ : Obj → Obj → Set ℓ
    -- equality between morphisms
    _≈_ : {A B : Obj} → Rel (A ⇒ B) e

    id  : {A : Obj} → A ⇒ A
    _∘_ : {A B C : Obj} → B ⇒ C → A ⇒ B → A ⇒ C

    ≈-equiv   : {A B : Obj} → IsEquivalence (_≈_ {A} {B})
    ∘-cong    : {A B C : Obj} {f f' : B ⇒ C} {g g' : A ⇒ B} →
                f ≈ f' → g ≈ g' → f ∘ g ≈ f' ∘ g'
    assoc     : {A B C D : Obj} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
                (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
    identityˡ : {A B : Obj} {f : A ⇒ B} → id ∘ f ≈ f
    identityʳ : {A B : Obj} {f : A ⇒ B} → f ∘ id ≈ f

  ----------------------------------------------------------------------
  -- The equivalence relation on morphisms
  ----------------------------------------------------------------------

  module ≈ {A B : Obj} = IsEquivalence (≈-equiv {A} {B})

  ≈-refl : {A B : Obj} {f : A ⇒ B} → f ≈ f
  ≈-refl = ≈.refl

  ≈-sym : {A B : Obj} {f g : A ⇒ B} → f ≈ g → g ≈ f
  ≈-sym = ≈.sym

  ≈-trans : {A B : Obj} {f g h : A ⇒ B} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans = ≈.trans

  -- the setoid of morphisms from A to B
  hom-setoid : (A B : Obj) → Setoid ℓ e
  hom-setoid A B = record
    { Carrier       = A ⇒ B
    ; _≈_           = _≈_
    ; isEquivalence = ≈-equiv
    }

  ----------------------------------------------------------------------
  -- Derived laws
  ----------------------------------------------------------------------

  ∘-congˡ : {A B C : Obj} {f f' : B ⇒ C} {g : A ⇒ B} → f ≈ f' → f ∘ g ≈ f' ∘ g
  ∘-congˡ p = ∘-cong p ≈-refl

  ∘-congʳ : {A B C : Obj} {f : B ⇒ C} {g g' : A ⇒ B} → g ≈ g' → f ∘ g ≈ f ∘ g'
  ∘-congʳ p = ∘-cong ≈-refl p

  assoc' : {A B C D : Obj} {f : C ⇒ D} {g : B ⇒ C} {h : A ⇒ B} →
           f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
  assoc' = ≈-sym assoc

  ----------------------------------------------------------------------
  -- Invertible morphisms
  ----------------------------------------------------------------------

  -- being invertible, as a property of a given morphism: this is the
  -- primitive notion, isomorphisms below are derived from it
  record Invertible {A B : Obj} (f : A ⇒ B) : Set (ℓ ⊔ e) where
    eta-equality
    field
      inv  : B ⇒ A
      invˡ : inv ∘ f ≈ id
      invʳ : f ∘ inv ≈ id

  open Invertible public

  -- builder, usable where the field names are not in scope
  mkInv : {A B : Obj} {f : A ⇒ B} (g : B ⇒ A) →
          g ∘ f ≈ id → f ∘ g ≈ id → Invertible f
  mkInv g p q = record { inv = g ; invˡ = p ; invʳ = q }

  id-invertible : {A : Obj} → Invertible (id {A})
  id-invertible = record { inv = id ; invˡ = identityˡ ; invʳ = identityˡ }

  -- the inverse of an invertible morphism is invertible
  inv-invertible : {A B : Obj} {f : A ⇒ B} (i : Invertible f) → Invertible (inv i)
  inv-invertible {f = f} i = record { inv = f ; invˡ = invʳ i ; invʳ = invˡ i }

  ∘-invertible : {A B C : Obj} {f : B ⇒ C} {g : A ⇒ B} →
                 Invertible f → Invertible g → Invertible (f ∘ g)
  ∘-invertible i j = record
    { inv  = inv j ∘ inv i
    ; invˡ = ≈-trans assoc
             (≈-trans (∘-congʳ (≈-trans assoc' (≈-trans (∘-congˡ (invˡ i)) identityˡ)))
             (invˡ j))
    ; invʳ = ≈-trans assoc
             (≈-trans (∘-congʳ (≈-trans assoc' (≈-trans (∘-congˡ (invʳ j)) identityˡ)))
             (invʳ i))
    }

  ----------------------------------------------------------------------
  -- Isomorphisms
  ----------------------------------------------------------------------

  infix 4 _≅_

  -- an isomorphism is an invertible morphism together with its source:
  -- _≅_ is what to use when the morphism is part of the data, Invertible
  -- when it is already at hand
  _≅_ : Obj → Obj → Set (ℓ ⊔ e)
  A ≅ B = Σ (A ⇒ B) (Invertible {A} {B})

  to : {A B : Obj} → A ≅ B → A ⇒ B
  to = proj₁

  invertible-≅ : {A B : Obj} (i : A ≅ B) → Invertible (to i)
  invertible-≅ = proj₂

  from : {A B : Obj} → A ≅ B → B ⇒ A
  from i = inv (invertible-≅ i)

  isoˡ : {A B : Obj} (i : A ≅ B) → from i ∘ to i ≈ id
  isoˡ i = invˡ (invertible-≅ i)

  isoʳ : {A B : Obj} (i : A ≅ B) → to i ∘ from i ≈ id
  isoʳ i = invʳ (invertible-≅ i)

  -- an invertible morphism is the same thing as the "to" direction of
  -- an isomorphism
  ≅-invertible : {A B : Obj} {f : A ⇒ B} → Invertible f → A ≅ B
  ≅-invertible {f = f} i = f , i

  -- builder, usable where the field names are not in scope
  mk≅ : {A B : Obj} (f : A ⇒ B) (g : B ⇒ A) → g ∘ f ≈ id → f ∘ g ≈ id → A ≅ B
  mk≅ f g p q = f , mkInv g p q

  ≅-refl : {A : Obj} → A ≅ A
  ≅-refl = id , id-invertible

  ≅-sym : {A B : Obj} → A ≅ B → B ≅ A
  ≅-sym i = from i , inv-invertible (invertible-≅ i)

  ≅-trans : {A B C : Obj} → A ≅ B → B ≅ C → A ≅ C
  ≅-trans i j = to j ∘ to i , ∘-invertible (invertible-≅ j) (invertible-≅ i)

  -- naturality transfers to the inverses of isomorphisms
  ≅-natural : {A B A' B' : Obj} (i : A ≅ B) (j : A' ≅ B')
              (f : A ⇒ A') (g : B ⇒ B') →
              g ∘ to i ≈ to j ∘ f → from j ∘ g ≈ f ∘ from i
  ≅-natural i j f g p =
    ≈-trans (∘-congʳ (≈-sym identityʳ))
    (≈-trans (∘-congʳ (∘-congʳ (≈-sym (isoʳ i))))
    (≈-trans (∘-congʳ assoc')
    (≈-trans (∘-congʳ (∘-congˡ p))
    (≈-trans (∘-congʳ assoc)
    (≈-trans assoc'
    (≈-trans (∘-congˡ (isoˡ j))
             identityˡ))))))
