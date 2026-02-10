open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Recursive as Fin

{-# BUILTIN REWRITE _≡_ #-}

infixr 5 _⇒_

data Ty (n : ℕ) : Type where
  X : (i : Fin n) → Ty n
  _⇒_ : (A B : Ty n) → Ty n

-- A substitution on types
SubTy : (n n' : ℕ) → Type
SubTy n n' = Fin n' → Ty n

-- Applying a type substitution
_[_]' : {n : ℕ} {n' : ℕ} → Ty n' → SubTy n n' → Ty n
X i [ τ ]' = τ i
(A ⇒ B) [ τ ]' = (A [ τ ]') ⇒ (B [ τ ]')

SubTyId : (n : ℕ) → SubTy n n
SubTyId n k = X k

SubTyIdEq : {n : ℕ} {A : Ty n} → (A [ SubTyId n ]') ≡ A
SubTyIdEq {A = X i} = refl
SubTyIdEq {A = A ⇒ B} = cong₂ _⇒_ SubTyIdEq SubTyIdEq

-- Composition of substitutions
_∘'_ : {n n' n'' : ℕ} → SubTy n' n'' → SubTy n n' → SubTy n n''
(τ' ∘' τ) i = τ' i [ τ ]'

-- Applying a substition is an action
[∘'] : {n n' n'' : ℕ} {A : Ty n''} {τ' : SubTy n' n''} {τ : SubTy n n'} → (A [ τ' ]' [ τ ]') ≡ (A [ τ' ∘' τ ]')
[∘'] {A = X i} = refl
[∘'] {A = A ⇒ B} = cong₂ _⇒_ ([∘'] {A = A}) ([∘'] {A = B})

{-# REWRITE SubTyIdEq #-}

-- Contexts
data Con (n : ℕ) : Type where
  ε : Con n
  _▹_ : (Γ : Con n) (A : Ty n) → Con n

infixl 5 _▹_

-- Presence in contexts
data _∈_ {n : ℕ} (A : Ty n) : Con n → Type where
  here : {Γ : Con n} → A ∈ (Γ ▹ A)
  drop : {Γ : Con n} {B : Ty n} → A ∈ Γ → A ∈ (Γ ▹ B)

postulate
  -- TODO
  PS : {n : ℕ} (Γ : Con n) (A : Ty n) → Type
