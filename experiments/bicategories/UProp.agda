--- Incoherent sets / presentations of propositions

module UProp where

open import Prelude
open import Data.Vec as Vec hiding (last)
open import Data.Vec.Properties using (lookup-map)

ctx : Type
ctx = ℕ

ctx-empty : ctx
ctx-empty = 0

add0 : ctx → ctx
add0 = suc

term : ctx → Type
term = Fin

-- The variable we just added
last0 : (Γ : ctx) → term (add0 Γ)
last0 Γ = zero

-- A substitution
sub : ctx → ctx → Type
sub Δ Γ = Vec (term Δ) Γ

-- Application of a substitution
sub-ap : {Δ Γ : ctx} → sub Δ Γ → term Γ → term Δ
sub-ap σ t = Vec.lookup σ t

-- Composition of substitutions
sub-comp : {Γ'' Γ' Γ : ctx} → sub Γ'' Γ' → sub Γ' Γ → sub Γ'' Γ
sub-comp σ [] = []
sub-comp σ (x ∷ τ) = sub-ap σ x ∷ sub-comp σ τ

-- Application is an action
sub-comp-ap : {Γ'' Γ' Γ : ctx} (σ : sub Γ'' Γ') (τ : sub Γ' Γ) (x : term Γ) → sub-ap σ (sub-ap τ x) ≡ sub-ap (sub-comp σ τ) x
sub-comp-ap σ (x ∷ τ) zero = refl
sub-comp-ap σ (x ∷ τ) (suc i) = sub-comp-ap σ τ i

-- Weakening
wk0 : {Γ : ctx} → sub (add0 Γ) Γ
wk0 {zero} = []
wk0 {suc Γ} = suc zero ∷ Vec.map (_↑ʳ_ 1) (wk0 {Γ})

wk0ap : {Γ : ctx} → term Γ → term (add0 Γ)
wk0ap = sub-ap wk0

-- Weakening shifts the variables
wk0-ap : {Γ : ctx} (x : term Γ) → wk0ap x ≡ suc x
wk0-ap {suc Γ} zero = refl
wk0-ap {suc Γ} (suc x) = trans (lookup-map x (_↑ʳ_ 1) (wk0 {Γ})) (cong suc (wk0-ap x))

-- Identity substitution
sub-id : (Γ : ctx) → sub Γ Γ
sub-id zero = []
sub-id (suc Γ) = last0 Γ ∷ wk0

-- The identity substitution acts trivially
sub-id-ap : (Γ : ctx) (x : term Γ) → sub-ap (sub-id Γ) x ≡ x
sub-id-ap (suc Γ) zero = refl
sub-id-ap (suc Γ) (suc x) = wk0-ap x
