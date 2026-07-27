open import Prelude
import Data.List as List
import Data.Product as Product

import UProp as UProp
import Set as Set
import USet as USet

f : {Γ : Set.ctx} {A B : Set.obj Γ} → Set.1cell Γ A B → USet.1cell Γ A B
f (Set.var i) = USet.var i
f Set.id = USet.id
f (Set.co a b) = USet.co (f a) (f b)

-- The substitution weakening by one 0-cell (add0) and one 1-cell (add1): a
-- variable is sent to the corresponding variable of the extended context.
wk01' : {Γ : USet.ctx} (A' : USet.type (USet.ctx-pred (USet.add0 Γ)))
      → Set.sub (USet.add1 (USet.add0 Γ) A') Γ
wk01' {Γ} A' = UProp.wk0 , Set.sub1-mk UProp.wk0 λ v →
  let (v' , e) = map-lookup (USet.wk0-type {USet.ctx-pred Γ}) (snd Γ) v in
  subst (Set.term (USet.add1 (USet.add0 Γ) A')) e (Set.var (suc v'))

-- Weaken a Set term by one 0-cell (add0) and one 1-cell (add1)
wk01 : {Γ : USet.ctx} {A' : USet.type (USet.ctx-pred (USet.add0 Γ))} {T : Set.type (fst Γ)}
     → Set.term Γ T → Set.term (USet.add1 (USet.add0 Γ) A') (Product.map UProp.wk0ap UProp.wk0ap T)
wk01 {A' = A'} a = Set.sub-ap (wk01' A') a

-- The canonical (biased) composite of the linear pasting scheme of shape S,
-- built inside the scheme context ps S. We thread the composite-so-far as an
-- accumulator, weakening it each time the context is extended by a new arrow.
g-ps-from : (Γ : USet.ctx) (X A : USet.obj Γ) (acc : Set.term Γ (X , A)) (S : USet.pshape)
          → Set.term (USet.ps-from S Γ A) (USet.ps-src-from S Γ A X , USet.ps-tgt-from S Γ A)
g-ps-from Γ X A acc zero = acc
g-ps-from Γ X A acc (suc S) =
  g-ps-from (USet.add1 (USet.add0 Γ) (UProp.wk0ap A , USet.last0 Γ)) (UProp.wk0ap X) (USet.last0 Γ)
            (Set.co (wk01 acc) (Set.var zero)) S

g-ps : (S : USet.pshape) → Set.term (USet.ps S) (USet.ps-hom S)
g-ps S = g-ps-from USet.ctx-pt z z Set.id S
  where z = USet.last0 USet.ctx-empty

g : {Γ : USet.ctx} {A B : USet.obj Γ} → USet.1cell Γ A B → Set.1cell Γ A B

-- Translation of a substitution
gsub1 : {Δ Γ : USet.ctx} {σ' : UProp.sub (USet.ctx-pred Δ) (USet.ctx-pred Γ)} → USet.sub1 Δ Γ σ' → Set.sub1 Δ Γ σ'
gsub1 {Γ = Γ' , []} σ = tt
gsub1 {Γ = Γ' , A ∷ Γ} (a , σ) = g a , gsub1 σ

gsub : {Δ Γ : USet.ctx} → USet.sub Δ Γ → Set.sub Δ Γ
gsub σ = fst σ , gsub1 (snd σ)

g (USet.var i) = Set.var i
g (USet.coh S σ) = Set.sub-ap (gsub σ) (g-ps S)
