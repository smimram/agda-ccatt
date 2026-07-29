module Prelude where

open import Agda.Primitive public using (Level) renaming (Set to Type ; _⊔_ to ℓ-max)

open import Data.Empty public
open import Data.Unit using (⊤ ; tt) public
open import Data.Nat public
open import Data.Nat.Properties public
open import Data.List using (List ; [] ; _∷_ ; length ; lookup) public
open import Data.Fin using (Fin ; zero ; suc ; _↑ʳ_ ; fromℕ ; inject₁) public
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) using (_×_ ; Σ ; _,_ ; uncurry) public
open import Data.Vec using (Vec ; [] ; _∷_) public
open import Relation.Binary.PropositionalEquality public
open import Function using (_∘_) public

import Data.List as List

open ≡-Reasoning public

transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport p x = subst (λ X → X) p x

-- Uniqueness of identity proofs (we have K here)
uip : ∀ {ℓ} {A : Type ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl refl = refl

-- Equality in a Σ-type
Σ-≡ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {x y : A} (p : x ≡ y) {u : B x} {v : B y}
    → subst B p u ≡ v → (x , u) ≡ (y , v)
Σ-≡ refl refl = refl

-- Substituting in a pair
subst-× : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : A → Type ℓ''} {x y : A} (p : x ≡ y) (u : B x) (v : C x)
        → subst (λ z → B z × C z) p (u , v) ≡ (subst B p u , subst C p v)
subst-× refl u v = refl

-- Substituting twice
subst₂-subst : ∀ {ℓ ℓ'} {A B : Type ℓ} {C : A → B → Type ℓ'} {x x' : A} {y y' : B}
               (p : x ≡ x') (q : y ≡ y') (u : C x y)
             → subst₂ C p q u ≡ subst (uncurry C) (cong₂ _,_ p q) u
subst₂-subst refl refl u = refl

-- Looking up the image of an element in a mapped list: we produce the shifted
-- index together with the proof that its value is the mapped original.
map-lookup : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (h : A → B) (xs : List A) (v : Fin (length xs))
           → Σ (Fin (length (List.map h xs))) (λ v' → lookup (List.map h xs) v' ≡ h (lookup xs v))
map-lookup h (x ∷ xs) zero = zero , refl
map-lookup h (x ∷ xs) (suc v) = let (v' , e) = map-lookup h xs v in suc v' , e
