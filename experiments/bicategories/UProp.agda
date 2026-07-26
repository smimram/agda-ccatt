{-# OPTIONS --allow-unsolved-metas #-}

--- incoherent sets / presentations of propositions

module UProp where

open import Prelude
open import Data.Vec as Vec hiding (last)

ctx : Type
ctx = ℕ

ctx-empty : ctx
ctx-empty = 0

add0 : ctx → ctx
add0 = suc

term : ctx → Type
term = Fin

-- the variable we just added
last0 : (Γ : ctx) → term (add0 Γ)
last0 Γ = zero

sub : ctx → ctx → Type
sub Δ Γ = Vec (term Δ) Γ

sub-ap : {Δ Γ : ctx} → sub Δ Γ → term Γ → term Δ
sub-ap σ t = Vec.lookup σ t

sub-comp : {Γ'' Γ' Γ : ctx} → sub Γ'' Γ' → sub Γ' Γ → sub Γ'' Γ
sub-comp σ [] = []
sub-comp σ (x ∷ τ) = sub-ap σ x ∷ sub-comp σ τ

sub-comp-ap : {Γ'' Γ' Γ : ctx} (σ : sub Γ'' Γ') (τ : sub Γ' Γ) (x : term Γ) → sub-ap σ (sub-ap τ x) ≡ sub-ap (sub-comp σ τ) x
sub-comp-ap σ (x ∷ τ) zero = refl
sub-comp-ap σ (x ∷ τ) (suc i) = sub-comp-ap σ τ i

wk0 : {Γ : ctx} → sub (add0 Γ) Γ
wk0 {zero} = []
wk0 {suc Γ} = suc zero ∷ Vec.map (_↑ʳ_ 1) (wk0 {Γ})

wk0ap : {Γ : ctx} → term Γ → term (add0 Γ)
wk0ap = sub-ap wk0

-- Identity substitution
sub-id : (Γ : ctx) → sub Γ Γ
sub-id zero = []
sub-id (suc Γ) = last0 Γ ∷ wk0
