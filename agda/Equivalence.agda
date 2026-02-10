---
--- Our main theorem: CL and CC coincide
---

open import Prelude
open import Ty
import CC
import CL

--- From CC to CL

F     : {n : ℕ} {Γ : Con n} {A : Ty n} → CC.Tm Γ A → CL.Tm Γ A
F∼    : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : CC.Tm Γ A} → t CC.∼ u → F t CL.∼ F u
FSub  : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CC.Sub τ Γ Γ' → CL.Sub τ Γ Γ'
FSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : CC.Tm Γ' A) {τ : SubTy n n'} (σ : CC.Sub τ Γ Γ') →
        ((F t) CL.[ FSub {Γ = Γ} σ ]) ≡ F (t CC.[ σ ])
F∼Sub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : CC.Sub τ Γ Γ'} → σ CC.∼Sub σ' → FSub σ CL.∼Sub FSub σ'
FSub∘ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (σ' : CC.Sub τ' Γ' Γ'') (σ : CC.Sub τ Γ Γ') →
        FSub σ' CL.∘ FSub σ ≡ FSub {Γ = Γ} (CC._∘_ {Γ = Γ} σ' σ)

F (CC.var x) = CL.var x
F (CC.coh ps τ σ) = CL.PSTm ps CL.[ FSub σ ]

F∼ (CC.eqv x) = CL.∼refl
F∼ {Γ = Γ} (CC.eq ps t u τ {σ = σ} {σ'} p) = subst₂ CL._∼_ (FSub≡ t σ) (FSub≡ u σ') ((CL.PSEq ps (F t) (F u)) CL.[ F∼Sub {Γ = Γ} p ]∼)
F∼ (CC.∼trans p q) = CL.∼trans (F∼ p) (F∼ q)

FSub {Γ' = ε} σ = tt
FSub {Γ' = Γ' ▹ A} (σ , t) = FSub σ , F t

FSub≡ (CC.var here) σ = refl
FSub≡ (CC.var (drop x)) (σ , t) = FSub≡ (CC.var x) σ
FSub≡ (CC.coh ps τ' σ') σ = CL.[∘] (CL.PSTm ps) (FSub σ') (FSub σ) ∙ cong (λ σ → CL.PSTm ps CL.[ σ ]) (FSub∘ σ' σ)

F∼Sub {Γ' = ε} p = tt
F∼Sub {Γ' = Γ' ▹ A} (p , q) = F∼Sub p , F∼ q

FSub∘ {Γ'' = ε} σ' σ = refl
FSub∘ {Γ'' = Γ'' ▹ A} (σ' , t') σ = Σ-≡,≡→≡ (FSub∘ σ' σ , substConst _ _ ∙ FSub≡ t' σ)

--- From CL to CC

G : {n : ℕ} {Γ : Con n} {A : Ty n} → CL.Tm Γ A → CC.Tm Γ A
G {n} {Γ} (CL.var x) = CC.var x
G {n} {Γ} CL.I = CC.I
G {n} {Γ} CL.K = CC.K
G {n} {Γ} CL.S = CC.S
G (t CL.$ u) = CC.ap (G t) (G u)

G∼ : {n : ℕ} {Γ : Con n} {A : Ty n} {t u : CL.Tm Γ A} → t CL.∼ u → G t CC.∼ G u
G∼ (CL.Iβ t) = CC.apI (G t)
G∼ (CL.Kβ t u) = CC.apK (G t) (G u)
G∼ (CL.Sβ t u v) = CC.apS (G t) (G u) (G v)
G∼ CL.lamIβ = CC.lamIβ
G∼ CL.lamKβ = CC.lamKβ
G∼ CL.lamSβ = CC.lamSβ
G∼ CL.lamwk = CC.lamwk
G∼ CL.lamη = CC.lamη
G∼ (CL.∼$ p q) = CC.∼ap (G∼ p) (G∼ q)
G∼ CL.∼refl = CC.∼refl _
G∼ (CL.∼sym p) = CC.∼sym (G∼ p)
G∼ (CL.∼trans p q) = CC.∼trans (G∼ p) (G∼ q)

GSub : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} → CL.Sub τ Γ Γ' → CC.Sub τ Γ Γ'
GSub {Γ' = ε} σ = tt
GSub {Γ' = Γ' ▹ A} (σ , t) = GSub σ , G t

GSub≡ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Ty n'} (t : CL.Tm Γ' A) {τ : SubTy n n'} (σ : CL.Sub τ Γ Γ') →
        ((G t) CC.[ GSub {Γ = Γ} σ ]) ≡ G (t CL.[ σ ])
GSub≡ (CL.var here) σ = refl
GSub≡ (CL.var (drop x)) (σ , t) = GSub≡ (CL.var x) σ
GSub≡ CL.I σ = refl
GSub≡ CL.K σ = refl
GSub≡ CL.S σ = refl
GSub≡ (t CL.$ u) σ = cong₂ CC.ap (GSub≡ t σ) (GSub≡ u σ)

--- F and G are mutually inverse functions

GF : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CC.Tm Γ A) → G (F t) CC.∼ t
GFSub : {n n' : ℕ} {τ : SubTy n n'} {Γ : Con n} {Γ' : Con n'} (σ : CC.Sub τ Γ Γ') → GSub (FSub σ) CC.∼Sub σ

GF (CC.var x) = CC.∼refl _
GF (CC.coh ps τ σ) = CC.∼trans
  (CC.∼trans (CC.∼of≡ (sym (GSub≡ (CL.PSTm ps) (FSub σ)))) (G (CL.PSTm ps) CC.[ GFSub σ ]∼))
  (CC.∼trans (CC.eqs ps (G (CL.PSTm ps)) (CC.coh ps (SubTyId _) (CC.SubId _)) τ σ)
  (subst₂ CC._∼_ refl (cong (CC.coh ps τ) (CC.∘UnitL σ)) (CC.∼refl _)))

GFSub {Γ' = ε} tt = tt
GFSub {Γ' = Γ' ▹ A} (σ , t) = GFSub σ , GF t

FG : {n : ℕ} {Γ : Con n} {A : Ty n} (t : CL.Tm Γ A) → F (G t) CL.∼ t
FG (CL.var x) = CL.∼refl
FG {Γ = Γ} CL.I = CL.PSEq PS⊢X⇒X (CL.PSTm PS⊢X⇒X) CL.I CL.[ CL.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
FG {Γ = Γ} CL.K = CL.PSEq PS⊢X⇒Y⇒X (CL.PSTm PS⊢X⇒Y⇒X) CL.K CL.[ CL.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
FG {Γ = Γ} CL.S = CL.PSEq PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z (CL.PSTm PS⊢[X⇒Y⇒Z]⇒[X⇒Y]⇒X⇒Z) CL.S CL.[ CL.∼SubRefl {Γ = Γ} {τ = []} tt ]∼
FG (t CL.$ u) = CL.PSEq PSX⇒Y,X⊢Y (CL.PSTm PSX⇒Y,X⊢Y) (CL.var (drop here) CL.$ CL.var here) CL.[ (tt , FG t) , FG u ]∼
