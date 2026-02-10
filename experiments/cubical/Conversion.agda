{-# OPTIONS --rewriting #-}

open import Cubical.Foundations.Prelude hiding (Sub)
open import Cubical.Data.Nat
open import Cubical.Data.Fin.Recursive

open import Ty
import CC
import CL

{-# TERMINATING #-}
F : {n : ℕ} {Γ : Con n} {A : Ty n} → CC.Tm Γ A → CL.Tm Γ A
FSubTm : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} (τ : SubTy n n') → CC.SubTm Γ Γ' τ → CL.SubTm Γ Γ' τ
FSub : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} → CC.Sub Γ Γ' → CL.Sub Γ Γ'
FSubEq : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A : Ty n'} (t : CC.Tm Γ' A) (σ : CC.Sub Γ Γ') →
         F (t CC.[ σ ]) ≡ ((F t) CL.[ fst σ , (FSubTm {Γ = Γ} (fst σ) (snd σ)) ])

FSub (τ , σ) = τ , FSubTm τ σ

F (CC.coh ps σ) = CL.PSTm ps CL.[ FSub σ ]
F (CC.eq ps t u σ i) = lem i
  where
  lem : F (t CC.[ σ ]) ≡ F (u CC.[ σ ])
  lem =  FSubEq t σ ∙ cong (λ t → t CL.[ FSub σ ]) (CL.PSEq ps (F t) (F u)) ∙ sym (FSubEq u σ)
F (CC.tmSet t u p q i j) = isSet→isSet' {!!} {!!} {!!} {!!} {!!} i j

FSubTm {Γ' = ε} τ σ = tt
FSubTm {Γ' = Γ' ▹ A} τ (σ , t) = FSubTm τ σ , F t

FSubEq (CC.coh ps σ') σ = {!CL.[∘]!}
FSubEq (CC.eq ps t u σ' i) σ j = isSet→isSet' CL.TmSet _ _ _ _ i j
FSubEq (CC.tmSet t u p q i j) σ k = {!isSet→isGroupoid'!}

G : {n : ℕ} {Γ : Con n} {A : Ty n} → CL.Tm Γ A → CC.Tm Γ A

G {n} {Γ} (CL.X x) = CC.Var x
G {n} {Γ} (CL.K {A} {B}) = CC.K
G {n} {Γ} (CL.S {A} {B} {C}) = CC.S
G (t CL.$ u) = CC.ap (G t) (G u)
G {n} {Γ} (CL.Kβ {A} {B} {t} {u} i) = lem t u i
  where
  lem : (t : CL.Tm Γ A) (u : CL.Tm Γ B) → CC.ap (CC.ap CC.K (G t)) (G u) ≡ G t
  -- lem t u = {!!} ∙ CC.eq {Γ = Γ} {Γ' = Γ ▹ A ▹ B} {A = A} {!!} (CC.ap (CC.ap CC.K (CC.Var (drop here))) (CC.Var here)) (CC.Var (drop here)) (CC.SubExt {Γ' = Γ ▹ A} (CC.SubExt (CC.SubId Γ) (G t)) (G u)) ∙ {!!}
  lem t u = {!!} ∙ CC.eq {Γ = Γ} {n' = 2} {Γ' = ε ▹ X zero ▹ X (suc zero)} {A = X zero} {!!} (CC.ap (CC.ap CC.K (CC.Var (drop here))) (CC.Var here)) (CC.Var (drop here)) ((λ { zero → A ; (suc zero) → B }) , (tt , {!t!}) , {!u!}) ∙ {!!}
    where
    t' : CC.Tm Γ (X zero [ (λ { zero → A ; (suc zero) → B ; (suc (suc ())) }) ]')
    t' = {!t!}
G (CL.Sβ i) = {!!}
G (CL.lamKβ i) = {!!}
G (CL.lamSβ i) = {!!}
G (CL.lamwk$ i) = {!!}
G (CL.η i) = {!!}
G (CL.TmSet t u p q i j) = {!!}
