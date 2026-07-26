open import Prelude

import UProp as UProp
import Set as Set
import USet as USet

f : {Γ : Set.ctx} {A B : Set.obj Γ} → Set.1cell Γ A B → USet.1cell Γ A B
f (Set.var i) = USet.var i
f Set.id = USet.id
f (Set.co a b) = USet.co (f a) (f b)

-- {-# TERMINATING #-}
g : {Γ : USet.ctx} {A B : USet.obj Γ} → USet.1cell Γ A B → Set.1cell Γ A B

g-ps : (S : USet.pshape) → Set.term (USet.ps S) (USet.ps-hom S)
g-ps S = {!!} -- g-ps-from (USet.ps-src S) S
  where
  g-ps-from : (Γ : USet.ctx) (A : USet.obj Γ) (S : USet.pshape) → Set.term (USet.ps-from S Γ A) (USet.ps-src-from S Γ A A , USet.ps-tgt-from S Γ A)
  g-ps-from Γ A zero = Set.id
  g-ps-from Γ A (suc S) = Set.co (g-ps-from (USet.add1 (USet.add0 Γ) (UProp.wk0ap A , B)) B {!S!}) (g {!!}) -- (g {!USet.add1 (USet.add0 ?) (UProp.wk0ap A , ?)!}) (g-ps-from {!!} {!!})
    where
    B = USet.last0 Γ


  -- g-ps-from : (A : USet.obj Γ) (S : USet.pshape) (P : USet.ps-from Γ S A) → Set.term Γ (USet.ps-hom (A , P))
  -- g-ps-from A zero P = Set.id
  -- g-ps-from A (suc S) (B , a , P) = Set.co (g a) (g-ps-from B S P)


g (USet.var i) = Set.var i
g (USet.coh S σ) = {!!}

