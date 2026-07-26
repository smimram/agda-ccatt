-- Equivalence between biaised and unbiased sets

open import Prelude

import Set as Set
import UProp as UProp
import USet as USet

-- From sets to unbiased sets

f : {Γ : Set.ctx} {A B : Set.obj Γ} → Set.1cell Γ A B → USet.1cell Γ A B
f {Γ} (Set.var v) = USet.var v
f {Γ} {A} Set.id = USet.id
f {Γ} {A} {B} (Set.co a b) = USet.co (f a) (f b)

-- From unbiased sets to sets

{-# TERMINATING #-}
g : {Γ : USet.ctx} {A B : USet.obj Γ} → USet.1cell Γ A B → Set.1cell Γ A B

-- Every ps is inhabited
g-ps : {Γ : USet.ctx} {S : USet.pshape} (P : USet.ps Γ S) → Set.term Γ (USet.ps-hom P)
g-ps {Γ} {S} (A , P) = g-ps-from A S P
  where
  g-ps-from : (A : USet.obj Γ) (S : USet.pshape) (P : USet.ps-from Γ S A) → Set.term Γ (USet.ps-hom (A , P))
  g-ps-from A zero P = Set.id
  g-ps-from A (suc S) (B , a , P) = Set.co (g a) (g-ps-from B S P)

g (USet.var v) = Set.var v
g (USet.coh S P) = g-ps P
