{-# OPTIONS --rewriting #-}

--- Unbiased type theory for cartesian categories

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Recursive
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (Sub)

open import Ty

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE [∘'] #-}

{-# NO_POSITIVITY_CHECK #-}
-- Terms
data Tm {n : ℕ} (Γ : Con n) : (A : Ty n) → Type

-- Substitutions for terms
SubTm : {n : ℕ} (Γ : Con n) {n' : ℕ} (Γ' : Con n') (τ : SubTy n n') → Type
SubTm Γ ε _ = Unit
SubTm Γ (Γ' ▹ A) τ = SubTm Γ Γ' τ × Tm Γ (A [ τ ]')

-- Substitutions
Sub : {n : ℕ} (Γ : Con n) {n' : ℕ} (Γ' : Con n') → Type
Sub {n} Γ {n'} Γ' = Σ (SubTy n n') (SubTm Γ Γ')

-- Extend a substitution with a term
SubExt : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A : Ty n'} (σ : Sub Γ Γ') → Tm Γ (A [ fst σ ]') → Sub Γ (Γ' ▹ A)
SubExt σ t = fst σ , snd σ , t

-- Identity substitution
SubTmId : {n : ℕ} (Γ : Con n) → SubTm Γ Γ (SubTyId n)
SubTmId ε = tt
SubTmId (Γ ▹ A) = {!!} , {!!}

SubId : {n : ℕ} (Γ : Con n) → Sub Γ Γ
SubId {n} Γ = SubTyId n , SubTmId Γ

SubWk : {n : ℕ} (Γ : Con n) (A : Ty n) → Sub (Γ ▹ A) Γ
SubWk Γ A = SubTyId _ , {!!}

SubTerm : {n : ℕ} (Γ : Con n) → Sub Γ ε
SubTerm Γ = SubTyId _ , tt


{-# TERMINATING #-}
_[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A : Ty n'} → Tm Γ' A → (σ : Sub Γ Γ') → Tm Γ (A [ fst σ ]')

SubTm∘ : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {n'' : ℕ} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} →
          SubTm Γ' Γ'' τ' → SubTm Γ Γ' τ → 
          SubTm Γ Γ'' (τ' ∘' τ)

_∘_ : {n1 n2 n3 : ℕ} {Γ1 : Con n1} {Γ2 : Con n2} {Γ3 : Con n3} → Sub Γ2 Γ3 → Sub Γ1 Γ2 → Sub Γ1 Γ3
(τ' , σ') ∘ (τ , σ) = (τ' ∘' τ) , (SubTm∘ σ' σ)

postulate
  [∘] : {n1 n2 n3 : ℕ} {Γ1 : Con n1} {Γ2 : Con n2} {Γ3 : Con n3} {A : Ty n3} {t : Tm Γ3 A} {σ' : Sub Γ2 Γ3} {σ : Sub Γ1 Γ2} →
        (t [ σ' ] [ σ ]) ≡ t [ σ' ∘ σ ]
  -- {-# REWRITE [∘] #-}

data Tm {n} Γ where
  coh : {n' : ℕ} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) (σ : Sub Γ Γ') → Tm Γ (A [ fst σ ]')
  eq  : {n' : ℕ} {Γ' : Con n'} {A : Ty n'} (ps : PS Γ' A) (t u : Tm Γ' A) (σ : Sub Γ Γ') → (t [ σ ]) ≡ (u [ σ ])
  tmSet : {A : Ty n} → isSet (Tm Γ A)

SubTm∘ {Γ'' = ε} σ' σ = tt
SubTm∘ {Γ'' = Γ'' ▹ A} (σ' , t) σ = SubTm∘ σ' σ , t [ _ , σ ]

_[_] {Γ = Γ} (coh {A = A} ps σ') σ = coh ps (σ' ∘ σ)
eq ps t u σ' i [ σ ] = p i
  where
  p : (t [ σ' ]) [ σ ] ≡ (u [ σ' ]) [ σ ]
  p = [∘] {t = t} ∙ eq ps t u (σ' ∘ σ) ∙ sym ([∘] {t = u})
tmSet t u p q i j [ σ ] = P i j
  where
  P : Square (cong (λ t → t [ σ ]) p) (cong (λ t → t [ σ ]) q) refl refl
  P = isSet→isSet' tmSet _ _ _ _

-- [∘] {t = coh ps σ} = {!!}
-- [∘] {t = eq ps t u σ i} = {!!}
-- [∘] {t = tmSet t u x y i j} = {!!}

∘UnitL : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} (σ : Sub Γ Γ') → SubId Γ' ∘ σ ≡ σ
∘UnitL = {!!}

-- this can be done by taking Γ to consist of distinct variables and then substitute with the actual types of Γ
Var : {n : ℕ} {Γ : Con n} {A : Ty n} → A ∈ Γ → Tm Γ A
Var p = {!!}

Id : {n : ℕ} {Γ : Con n} {A : Ty n} → Tm Γ (A ⇒ A)
Id {n} {Γ} {A} = coh {n' = 1} {Γ' = ε} {A = X zero ⇒ X zero} {!!} ((λ x → A) , tt)

K : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A)
K {n} {Γ} {A} {B} = coh {n' = 2} {Γ' = ε} {A = X zero ⇒ X (suc zero) ⇒ X zero} {!!} ((λ { zero → A ; (suc x) → B }) , tt)

S : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm Γ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
S {n} {Γ} {A} {B} {C} =  coh {n' = 3} {Γ' = ε} {A = (X zero ⇒ X (suc zero) ⇒ X (suc (suc zero))) ⇒ (X zero ⇒ X (suc zero)) ⇒ X zero ⇒ X (suc (suc zero))} {!!} ((λ { zero → A ; (suc zero) → B ; (suc (suc zero)) → C }) , tt)

ap : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
ap {n} {Γ} {A} {B} t u = coh {n' = 2} {Γ' = ε ▹ (X zero ⇒ X (suc zero)) ▹ X zero} {A = X (suc zero)} {!!} ((λ { zero → A ; (suc zero) → B }) , (tt , t) , u)
