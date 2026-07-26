module Prelude where

open import Agda.Primitive public using (Level) renaming (Set to Type ; _⊔_ to ℓ-max)

open import Data.Empty public
open import Data.Unit using (⊤ ; tt) public
open import Data.Nat public
open import Data.Nat.Properties
open import Data.List using (List ; [] ; _∷_ ; length ; lookup) public
open import Data.Fin using (Fin) public
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) using (_×_ ; Σ ; _,_ ; uncurry) public
open import Data.Vec using (Vec ; [] ; _∷_) public
open import Relation.Binary.PropositionalEquality public
open import Function using (_∘_) public

open ≡-Reasoning public
