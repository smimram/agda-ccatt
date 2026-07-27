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

-- Looking up the image of a variable in a mapped context list: we produce the
-- shifted index together with the proof that its type is the mapped original.
wk-lookup : {A B : Type} (h : A → B) (xs : List A) (v : Fin (length xs))
          → Σ (Fin (length (List.map h xs))) (λ v' → lookup (List.map h xs) v' ≡ h (lookup xs v))
wk-lookup h (x ∷ xs) zero = zero , refl
wk-lookup h (x ∷ xs) (suc v) = let (v' , e) = wk-lookup h xs v in suc v' , e

-- Weaken a Set term by one 0-cell (add0) and one 1-cell (add1). Set has no
-- built-in weakening, so we define the one we need directly by recursion.
wk01 : {Γ : USet.ctx} {A' : USet.type (USet.ctx-pred (USet.add0 Γ))} {T : Set.type (fst Γ)}
     → Set.term Γ T → Set.term (USet.add1 (USet.add0 Γ) A') (Product.map UProp.wk0ap UProp.wk0ap T)
wk01 {Γ} {A'} (Set.var v) =
  subst (Set.term (USet.add1 (USet.add0 Γ) A')) (snd r) (Set.var (suc (fst r)))
  where r = wk-lookup (USet.wk0-type {USet.ctx-pred Γ}) (snd Γ) v
wk01 Set.id = Set.id
wk01 (Set.co a b) = Set.co (wk01 a) (wk01 b)

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

{-# TERMINATING #-}
g : {Γ : USet.ctx} {A B : USet.obj Γ} → USet.1cell Γ A B → Set.1cell Γ A B

-- Apply a substitution σ : Γ → ps S to a Set term living in ps S, producing the
-- corresponding biased composite in Γ. This is the "Set substitution" that the
-- top-level Set module lacks; variables are interpreted via σ (translated by g).
applyσ : {Γ : USet.ctx} (S : USet.pshape) (σ : USet.sub Γ (USet.ps S))
         {(A , B) : Set.type (fst (USet.ps S))}
       → Set.term (USet.ps S) (A , B)
       → Set.1cell Γ (UProp.sub-ap (fst σ) A) (UProp.sub-ap (fst σ) B)
applyσ S σ (Set.var v) = g (USet.sub1-lookup (snd σ) v)
applyσ S σ Set.id = Set.id
applyσ S σ (Set.co a b) = Set.co (applyσ S σ a) (applyσ S σ b)

g (USet.var i) = Set.var i
g (USet.coh S σ) = applyσ S σ (g-ps S)
