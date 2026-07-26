--- incoherent sets / presentations of propositions

module UProp where

open import Prelude
open import Data.Vec as Vec

ctx : Type
ctx = ℕ

term : ctx → Type
term = Fin

sub : ctx → ctx → Type
sub Δ Γ = Vec (term Δ) Γ

ap : {Δ Γ : ctx} → sub Δ Γ → term Γ → term Δ
ap σ t = Vec.lookup σ t
