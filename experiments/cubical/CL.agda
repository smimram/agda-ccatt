--- Combinatory logic for the implicational fragment

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Nat
open import Cubical.Data.Fin
open import Cubical.Data.Sigma hiding (Sub)

open import Ty

infixl 6 _$_

data Tm {n : ℕ} (Γ : Con n) : Ty n → Type where
  X : {A : Ty n} → A ∈ Γ → Tm Γ A
  K : {A B : Ty n} → Tm Γ (A ⇒ B ⇒ A)
  S : {A B C : Ty n} → Tm Γ ((A ⇒ B ⇒ C) ⇒ (A ⇒ B) ⇒ A ⇒ C)
  _$_ : {A B : Ty n} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  Kβ : {A B : Ty n} {t : Tm Γ A} {u : Tm Γ B} → K $ t $ u ≡ t
  Sβ : {A B C : Ty n} {t : Tm Γ (A ⇒ B ⇒ C)} {u : Tm Γ (A ⇒ B)} {v : Tm Γ A} → S $ t $ u $ v ≡ t $ v $ (u $ v)
  -- ax4
  lamKβ : {A B C : Ty n} →
          _≡_ {A = Tm Γ ((A ⇒ C) ⇒ (A ⇒ B) ⇒ (A ⇒ C))} 
          (S $ (K $ S) $ (S $ (K $ K {A = C} {B = B})))
          K
  -- ax5
  lamSβ : {A B C D : Ty n} →
          _≡_ {A = Tm Γ ((C ⇒ B ⇒ A ⇒ D) ⇒ (C ⇒ B ⇒ A) ⇒ (C ⇒ B) ⇒ C ⇒ D)}
          (S $ (K $ (S $ (K $ S))) $ (S $ (K $ S) $ (S $ (K $ S))))
          (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ (S $ (K $ (S $ (K $ S))) $ S)))) $ (K $ S))
  -- ax1
  lamwk$ : {A B C : Ty n} →
           _≡_ {A = Tm Γ ((C ⇒ B) ⇒ C ⇒ A ⇒ B)}
           (S $ (K $ K {A = B} {B = A}))
           (S $ (S $ (K $ S) $ (S $ (K $ K) $ (S $ (K $ S) $ K))) $ (K $ K))
  -- ax2
  η : {A B C : Ty n} →
      _≡_ {A = Tm Γ ((A ⇒ B) ⇒ A ⇒ B)}
      (S $ (S $ (K $ S) $ K) $ (K $ (S $ K $ K {A = A} {B = A})))
      (S $ K $ K {A = A ⇒ B} {B = A})

  TmSet : {A : Ty n} → isSet (Tm Γ A)

postulate
  -- TODO
  PSTm : {n : ℕ} {Γ : Con n} {A : Ty n} → PS Γ A → Tm Γ A
  PSEq : {n : ℕ} {Γ : Con n} {A : Ty n} (ps : PS Γ A) (t u : Tm Γ A) → t ≡ u

-- Substitutions for terms
SubTm : {n : ℕ} (Γ : Con n) {n' : ℕ} (Γ' : Con n') (τ : SubTy n n') → Type
SubTm Γ ε _ = Unit
SubTm Γ (Γ' ▹ A) τ = SubTm Γ Γ' τ × Tm Γ (A [ τ ]')

-- Substitutions
Sub : {n : ℕ} (Γ : Con n) {n' : ℕ} (Γ' : Con n') → Type
Sub {n} Γ {n'} Γ' = Σ (SubTy n n') (SubTm Γ Γ')

{-# TERMINATING #-}
_[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A : Ty n'} → Tm Γ' A → (σ : Sub Γ Γ') → Tm Γ (A [ fst σ ]')
X here [ τ , σ , t ] = t
X (drop x) [ τ , σ , t ] = X x [ τ , σ ]
K [ σ ] = K
S [ σ ] = S
(t $ u) [ σ ] = (t [ σ ]) $ (u [ σ ])
Kβ {t = t} {u = u} i [ σ ] = cong (λ t → t [ σ ]) (Kβ {t = t} {u = u}) i
Sβ {t = t} {u = u} {v = v} i [ σ ] = cong (λ t → t [ σ ]) (Sβ {t = t} {u = u} {v = v}) i
lamKβ {A = A} {B} {C} i [ σ ] = cong (λ t → t [ σ ]) (lamKβ {A = A} {B} {C}) i
lamSβ {A = A} {B} {C} {D} i [ σ ] = cong (λ t → t [ σ ]) (lamSβ {A = A} {B} {C} {D}) i
lamwk$ {A = A} {B} {C} i [ σ ] = cong (λ t → t [ σ ]) (lamwk$ {A = A} {B} {C}) i
η {A = A} {B} {C} i [ σ ] = cong (λ t → t [ σ ]) (η {A = A} {B} {C}) i
TmSet t u p q i j [ σ ] = isSet→isSet' TmSet (cong (λ t → t [ σ ]) p) (cong (λ t → t [ σ ]) q) refl refl i j
