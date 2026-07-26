-- Propositions
-- (incoherent ones, possibly with multiple witnesses)

module Prop where

open import Prelude
open import Data.Vec as Vec

-- A context is a list of variables (identified to their number)
ctx : Type
ctx = ℕ

-- A term is a variable
term : ctx → Type
term = Fin

sub : ctx → ctx → Type
sub Δ Γ = Vec (term Δ) Γ

ap : {Δ Γ : ctx} → sub Δ Γ → term Γ → term Δ
ap σ t = Vec.lookup σ t
