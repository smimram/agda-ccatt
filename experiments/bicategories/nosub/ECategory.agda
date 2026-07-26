--- Equivalence between biased and unbiased version of categories

open import Prelude
open import Data.List as List

import Set as Set
import Category as Cat
import UProp as UProp
import USet as USet
import UCategory as UCat
import ESet as Pred

f1 : {Γ : Set.ctx} {A B : Set.obj Γ} → Set.1cell Γ A B → USet.1cell Γ A B
f1 = Pred.f

g1 : {Γ : USet.ctx} {A B : USet.obj Γ} → USet.1cell Γ A B → Set.1cell Γ A B
g1 = Pred.g

f1* : Cat.ctx → UCat.ctx
f1* (Γ' , Γ) = Γ' , List.map ty Γ
  where
  ty : Cat.type Γ' → UCat.type Γ'
  ty (A , a , b) = A , f1 a , f1 b

g1* : UCat.ctx → Cat.ctx
g1* (Γ' , Γ) = Γ' , List.map ty Γ
  where
  ty : UCat.type Γ' → Cat.type Γ'
  ty (A , a , b) = A , g1 a , g1 b

g1+ : {Δ Γ : USet.ctx} → USet.sub Δ Γ → Set.sub Δ Γ
g1+ {Δ} {Γ} (σ' , σ) = σ' , aux Γ σ' σ
  where
  aux : (Γ : USet.ctx) (σ' : UProp.sub (fst Δ) (fst Γ)) (σ : USet.sub1 Δ Γ σ') → Set.sub1 Δ Γ σ'
  aux (Γ' , []) σ' σ = tt
  aux (Γ' , (A , B) ∷ Γ) σ' (t , σ) = g1 t , aux (Γ' , Γ) σ' σ

-- TODO: lengthy recurrence...
g1-nat : {Δ Γ : USet.ctx} (σ : USet.sub Δ Γ) {A B : USet.obj Γ} (t : USet.1cell Γ A B) → g1 (USet.ap σ t) ≡ Set.ap (g1+ σ) (g1 t)
g1-nat σ (USet.var v) = {!!}
g1-nat σ (USet.coh S P) = {!!}

f2 : {Γ : Cat.ctx} {A B : Cat.obj Γ} {a b : Cat.1cell Γ A B} → Cat.2cell Γ a b → UCat.2cell (f1* Γ) (f1 a) (f1 b)
f2 (Cat.var v) = {!UCat.var ?!}
f2 (Cat.lunit _) = UCat.lunit _
f2 (Cat.runit _) = UCat.runit _
f2 (Cat.assoc _ _ _) = UCat.assoc _ _ _
f2 Cat.eqrefl = UCat.eqrefl
f2 (Cat.eqtrans α β) = UCat.eqtrans (f2 α) (f2 β)
f2 (Cat.eqsym α) = UCat.eqsym (f2 α)

g2 : {Γ : UCat.ctx} {A B : UCat.obj Γ} {a b : UCat.1cell Γ A B} → UCat.2cell Γ a b → Cat.2cell (g1* Γ) (g1 a) (g1 b)

-- we can compose pasting schemes
g2-ps : {Γ : UCat.ctx} {S : UCat.pshape} (P : UCat.ps Γ S) → Cat.2cell (g1* Γ) (g1 (USet.subst-tgt (UCat.ps-glob-tgt P) (USet.coh _ (UCat.ps-src P)))) (g1 (USet.coh _ (UCat.ps-tgt P)))

-- we can normalize 1-cells
-- TODO: this one is too general, we need the fact that a is a composite of P in a generic way...
--       I think that this comes from the coh in UCat which is too general
g2-n : {Γ : UCat.ctx} {S : USet.pshape} {P : USet.ps (fst Γ) S} (a : UCat.1cell Γ (UCat.Pred.ps-src P) (UCat.Pred.ps-tgt P)) → Cat.2cell (g1* Γ) (g1 a) (g1 (USet.coh S P))

-- g2-n {Γ = Γ} {S = zero} {P = A , tt} t = lem t -- we need to show that t has to be id
  -- where
  -- -- Γ* : USet.ctx
  -- -- Γ* = 1 , []
  -- -- t* : USet.1cell Γ* Fin.zero Fin.zero
  -- -- t* = USet.id
  -- -- lem* : (t : USet.1cell Γ* Fin.zero Fin.zero) → Cat.2cell (g1* (Γ* , [])) (g1 t) Set.id
  -- -- lem* t = USet.elim (λ t → {!Cat.2cell (g1* Γ*) (g1 t) Set.id!}) {!!} {!!} t
  -- -- σ* : {Γ : USet.ctx} {A : USet.obj Γ} (t : USet.1cell Γ A A) → USet.sub Γ Γ*
  -- -- σ* {Γ} {A} t = (A ∷ []) , tt
  -- -- nat : g1-ps (USet.ap-ps (σ* t*) 0 (Fin.zero , tt)) ≡ Set.id
  -- -- nat = g1-nat (σ* t*) (USet.id {A = Fin.zero})
  -- -- Γ0 : USet.ctx
  -- -- this is hard to believe, unless we have some naturality property wrt Γ, ie we can suppose that Γ is the context associated to the pasting scheme
  -- lem : {Γ : UCat.ctx} {A : UCat.obj Γ} (t : UCat.1cell Γ A A) → Cat.2cell (g1* Γ) (g1 t) Set.id
  -- lem {Γ} t = subst₂ (Cat.2cell (g1* Γ)) {!sym ?!} {!!} {!!}
-- g2-n {S = suc S} {P = A , B , a , P} t = {!!}

g2-ps = {!!}

g2 (UCat.var v) = {!Cat.var ?!}
g2 {Γ} (UCat.coh S P t u) =
  Cat.eqtrans3
    {!lem!}
    (g2-ps P)
    {!Cat.eqsym (g2-n u)!}
  -- where
  -- g2nt : Cat.2cell (g1* Γ) (g1 t) (g1 (USet.coh _ (UCat.ps-src P)))
  -- g2nt = g2-n t

  -- -- a naturality property
  -- nat : {A : Type} (F : A → Type) (G : A → Type) {a a' : A} (p : a ≡ a') (f : {x : A} → F x → G x) (x : F a) → subst G p (f x) ≡ f (subst F p x)
  -- nat F G refl f x = refl
  -- lem1' : subst (Set.1cell _ _) (UCat.ps-glob-tgt P) (g1 t) ≡ g1 (subst (USet.1cell _ _) (UCat.ps-glob-tgt P) t)
  -- lem1' = nat (USet.1cell (fst Γ) _) (Set.1cell (fst Γ) _) (UCat.ps-glob-tgt P) g1 t
  -- lem1 : Set.subst-tgt (UCat.ps-glob-tgt P) (g1 t) ≡ g1 (UCat.Pred.subst-tgt (UCat.ps-glob-tgt P) t)
  -- lem1 = lem1'
  -- lem2 : Set.subst-tgt (UCat.ps-glob-tgt P) (g1-ps (UCat.ps-src P)) ≡ g1 (USet.subst-tgt (UCat.ps-glob-tgt P) (USet.coh _ (UCat.ps-src P)))
  -- lem2 = nat (USet.1cell _ _) (Set.1cell _ _) (UCat.ps-glob-tgt P) g1 (UCat.Pred.coh _ (UCat.ps-src P))
  -- lem : Cat.2cell (g1* Γ) (g1 (UCat.Pred.subst-tgt (UCat.ps-glob-tgt P) t)) (g1 (UCat.Pred.subst-tgt (UCat.ps-glob-tgt P) (USet.coh _ (UCat.ps-src P))))
  -- lem = subst₂ (Cat.2cell (g1* Γ)) lem1 lem2 (Cat.subst-tgt0 (UCat.ps-glob-tgt P) g2nt)
