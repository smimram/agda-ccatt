{-# OPTIONS --cubical #-}

--- Type theoretical definition of unbiased categories
---
--- Version with pre-syntax

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Empty
open import Cubical.Data.Unit renaming (Unit to ⊤)

module UCategory2 where

-- pre-syntax
module Pre where
  obj = ℕ

  data type : Type where
    hom : obj → obj → type

  ctx0 = ℕ
  ctx1 = List type

  ctx : Type
  ctx = ctx0 × ctx1

  vars : ctx → ℕ
  vars (n , _) = n
  
  sub : Type

  data term : Type where
    coh : ctx → type → sub → term

  sub = List term

  data _⊢C : ctx → Type
  data _⊢T_ : ctx → type → Type
  data _⊢t_#_ : ctx → term → type → Type
  data _⊢S_>_ : ctx → sub → ctx → Type

  data _⊢C where
    ec : (n : ℕ) → (n , []) ⊢C
    cc : {Γ : ctx} {A : type} → Γ ⊢C → Γ ⊢T A → (Γ .fst , A ∷ Γ .snd) ⊢C

  data _⊢T_ where
    hom : {Γ : ctx} {A B : obj} → Γ ⊢C → A < vars Γ → B < vars Γ → Γ ⊢T hom A B

  data _⊢t_#_ where

  data _⊢S_>_ where
