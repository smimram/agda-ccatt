--- Type theoretical definition of sets / incoherent categories

module Set where

open import Prelude

import UProp as Pred

-- A (-1)-context x₀:*,…,xₙ:* is characterized by its length (we could define this as a Prop context)
Vars = Pred.ctx

-- The variables in a context of given length
Var = Pred.term

-- A type in a context is of the form xᵢ→yᵢ and thus corresponds to a pair of variables
type : (Γ : Vars) → Type
type Γ = Var Γ × Var Γ

-- A context is list of variables xᵢ:* (a (-1)-context) plus declarations of the form fᵢ:xᵢ→yᵢ
ctx : Type
ctx = Σ Vars (List ∘ type)

ctx-pred : ctx → Pred.ctx
ctx-pred = fst

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

-- A 1-substitution with given underlying 0-substitution
sub1 : (Δ Γ : ctx) → Pred.sub (fst Δ) (fst Γ) → Type
sub1 Δ (Γ' , []) σ' = ⊤
sub1 Δ (Γ' , (A , B) ∷ Γ) σ' = 1cell Δ (Pred.sub-ap σ' A) (Pred.sub-ap σ' B) × sub1 Δ (Γ' , Γ) σ'

-- Image of a variable under a substitution
sub1-lookup : {Δ Γ : ctx} {σ' : Pred.sub (ctx-pred Δ) (ctx-pred Γ)} (σ : sub1 Δ Γ σ') (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd))
sub1-lookup {Γ = Γ' , (A , B) ∷ Γ} σ zero = fst σ
sub1-lookup {Γ = Γ' , (A , B) ∷ Γ} σ (suc i) = sub1-lookup (snd σ) i

-- A substitution acts on terms: this is where the formal composites get transported
sub1-ap : {Δ Γ : ctx} {σ' : Pred.sub (fst Δ) (fst Γ)} (σ : sub1 Δ Γ σ') {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap σ' A) (Pred.sub-ap σ' B)
sub1-ap σ (var v) = sub1-lookup σ v
sub1-ap σ id = id
sub1-ap σ (co a b) = co (sub1-ap σ a) (sub1-ap σ b)

-- A 1-substitution is determined by the images of the variables
sub1-mk : {Δ Γ : ctx} (σ' : Pred.sub (fst Δ) (fst Γ))
          (f : (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd)))
        → sub1 Δ Γ σ'
sub1-mk {Γ = Γ' , []} σ' f = tt
sub1-mk {Γ = Γ' , A ∷ Γ} σ' f = f zero , sub1-mk {Γ = Γ' , Γ} σ' (f ∘ suc)

-- Composite substitution
sub1-comp : {Γ₁ Γ₂ Γ₃ : ctx}
            {σ' : Pred.sub (ctx-pred Γ₁) (ctx-pred Γ₂)}
            {τ' : Pred.sub (ctx-pred Γ₂) (ctx-pred Γ₃)} →
            sub1 Γ₁ Γ₂ σ' → sub1 Γ₂ Γ₃ τ' → sub1 Γ₁ Γ₃ (Pred.sub-comp σ' τ')
sub1-comp {Γ₃ = Γ₃' , []} σ tt = tt
sub1-comp {Γ₁ = Γ₁} {Γ₃ = Γ₃' , (A , B) ∷ Γ₃} {σ'} {τ'} σ (a , τ) = subst₂ (1cell Γ₁) (Pred.sub-comp-ap σ' τ' A) (Pred.sub-comp-ap σ' τ' B) (sub1-ap σ a) , sub1-comp σ τ

-- A substitution
sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (ctx-pred Δ) (ctx-pred Γ)) (sub1 Δ Γ)

-- Underlying substitution
sub-pred : {Δ Γ : ctx} → sub Δ Γ → Pred.sub (ctx-pred Δ) (ctx-pred Γ)
sub-pred = fst

-- Apply a substitution
sub-ap : {Δ Γ : ctx} (σ : sub Δ Γ) {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap (sub-pred σ) A) (Pred.sub-ap (sub-pred σ) B)
sub-ap σ a = sub1-ap (snd σ) a

-- Compose substitutions
sub-comp : {Γ'' Γ' Γ : ctx} (τ : sub Γ'' Γ') (σ : sub Γ' Γ) → sub Γ'' Γ
sub-comp τ σ = Pred.sub-comp (sub-pred τ) (sub-pred σ) , sub1-comp (snd τ) (snd σ)
