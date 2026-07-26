--- Type theoretical definition of sets / incoherent categories

module Set where

open import Prelude

-- A (-1)-context x₀:*,…,xₙ:* is characterized by its length (we could define this as a Prop context)
Vars = ℕ

-- The variables in a context of given length
Var = Fin

-- A type in a context is of the form xᵢ→yᵢ and thus corresponds to a pair of variables
type : (Γ : Vars) → Type
type Γ = Var Γ × Var Γ

-- A context is list of variables xᵢ:* (a (-1)-context) plus declarations of the form fᵢ:xᵢ→yᵢ
ctx : Type
ctx = Σ Vars (List ∘ type)

-- The 1-dimensional variables in a context
vars : ctx → Type
vars Γ = Fin (length (snd Γ))

-- The 0-dimensional variables in a context
obj : ctx → Type
obj Γ =  Var (fst Γ)

-- A term in a context is a formal composite of variables
data term (Γ : ctx) : (A : type (fst Γ)) → Type where
  var : (v : vars Γ) → term Γ (lookup (snd Γ) v)
  id : {A : obj Γ} → term Γ (A , A)
  co : {A B C : obj Γ} (f : term Γ (A , B)) (g : term Γ (B , C)) → term Γ (A , C)

-- A 1-cell is just a term
1cell : (Γ : ctx) (A B : Var (fst Γ)) → Type
1cell Γ A B = term Γ (A , B)

-- We can transport the target
subst-tgt : {Γ : ctx} {A B B' : obj Γ} → B ≡ B' → 1cell Γ A B → 1cell Γ A B'
subst-tgt {Γ = Γ} {A = A} p = subst (1cell Γ A) p
