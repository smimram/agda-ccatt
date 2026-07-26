--- Equivalence between biased and unbiased version of categories

open import Prelude
open import Data.List as List

import Set as Set
import Category as Cat
import USet as USet
import UCategory as UCat

-- f0* : Set.ctx → USet.ctx
-- f0* (n , Γ) = n , Γ -- List.map (uncurry USet.hom) Γ

-- g0* : USet.ctx → Set.ctx
-- g0* (n , Γ) = n , {!!}

f1 : {Γ : Set.ctx} {A B : Set.obj Γ} → Set.1cell Γ A B → USet.1cell Γ A B
f1 {Γ} (Set.var v) = USet.var v
f1 {Γ} {A} Set.id = USet.id
f1 {Γ} {A} {B} (Set.co a b) = USet.co (f1 a) (f1 b)

{-# TERMINATING #-}
g1 : {Γ : USet.ctx} {A B : USet.obj Γ} → USet.1cell Γ A B → Set.1cell Γ A B

g1-ps : {Γ : USet.ctx} {S : USet.pshape} (P : USet.ps Γ S) → Set.term Γ (USet.ps-hom P)
g1-ps {Γ} {S} (A , P) = g1-ps-from A S P
  where
  g1-ps-from : (A : USet.obj Γ) (S : USet.pshape) (P : USet.ps-from Γ S A) → Set.term Γ (USet.ps-hom (A , P))
  g1-ps-from A zero P = Set.id
  g1-ps-from A (suc S) (B , a , P) = Set.co (g1 a) (g1-ps-from B S P)

g1 (USet.var v) = Set.var v
g1 (USet.coh S P) = g1-ps P

f1* : Cat.ctx → UCat.ctx
f1* (Γ' , Γ) = Γ' , List.map ty Γ
  where
  ty : Cat.type Γ' → UCat.type Γ'
  ty (A , a , b) = A , f1 a , f1 b

g1* : UCat.ctx → Cat.ctx
g1* (Γ' , Γ) = Γ' , (List.map ty Γ)
  where
  ty : UCat.type Γ' → Cat.type Γ'
  ty (A , a , b) = A , g1 a , g1 b

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
g2-n : {Γ : UCat.ctx} {S : USet.pshape} {P : USet.ps (fst Γ) S} (a : UCat.1cell Γ (UCat.Pred.ps-src P) (UCat.Pred.ps-tgt P)) → Cat.2cell (g1* Γ) (g1 a) (g1 (USet.coh S P))

g2-ps = {!!}
g2-n {Γ = Γ} {S = zero} {P = A , tt} t = lem t -- we need to show that t has to be id
  where
  -- this is hard to believe, unless we have some naturality property wrt Γ, ie we can suppose that Γ is the context associated to the pasting scheme
  lem : {Γ : UCat.ctx} {A : USet.obj (fst Γ)} (t : UCat.1cell Γ A A) → Cat.2cell (g1* Γ) (g1 t) Set.id
  lem tl = {!!}
g2-n {S = suc S} {P = A , B , a , P} t = {!!}

g2 (UCat.var v) = {!Cat.var ?!}
g2 {Γ} (UCat.coh S P t u) =
  Cat.eqtrans3
    lem
    (g2-ps P)
    (Cat.eqsym (g2-n u))
  where
  g2nt : Cat.2cell (g1* Γ) (g1 t) (g1 (USet.coh _ (UCat.ps-src P)))
  g2nt = g2-n t

  -- a naturality property
  nat : {A : Type} (F : A → Type) (G : A → Type) {a a' : A} (p : a ≡ a') (f : {x : A} → F x → G x) (x : F a) → subst G p (f x) ≡ f (subst F p x)
  nat F G refl f x = refl
  lem1' : subst (Set.1cell _ _) (UCat.ps-glob-tgt P) (g1 t) ≡ g1 (subst (USet.1cell _ _) (UCat.ps-glob-tgt P) t)
  lem1' = nat (USet.1cell (fst Γ) _) (Set.1cell (fst Γ) _) (UCat.ps-glob-tgt P) g1 t
  lem1 : Set.subst-tgt (UCat.ps-glob-tgt P) (g1 t) ≡ g1 (UCat.Pred.subst-tgt (UCat.ps-glob-tgt P) t)
  lem1 = lem1'
  lem2 : Set.subst-tgt (UCat.ps-glob-tgt P) (g1-ps (UCat.ps-src P)) ≡ g1 (USet.subst-tgt (UCat.ps-glob-tgt P) (USet.coh _ (UCat.ps-src P)))
  lem2 = nat (USet.1cell _ _) (Set.1cell _ _) (UCat.ps-glob-tgt P) g1 (UCat.Pred.coh _ (UCat.ps-src P))
  lem : Cat.2cell (g1* Γ) (g1 (UCat.Pred.subst-tgt (UCat.ps-glob-tgt P) t)) (g1 (UCat.Pred.subst-tgt (UCat.ps-glob-tgt P) (USet.coh _ (UCat.ps-src P))))
  lem = subst₂ (Cat.2cell (g1* Γ)) lem1 lem2 (Cat.subst-tgt0 (UCat.ps-glob-tgt P) g2nt)
