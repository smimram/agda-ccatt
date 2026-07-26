--- Type theoretical definition of sets / incoherent categories

module Set where

open import Prelude
import Prop as Pred

-- A type is a pair of type variables
type : (Γ : Pred.ctx) → Type
type Γ = Pred.term Γ × Pred.term Γ

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

vars : ctx → Type
vars Γ = Fin (length (snd Γ))

obj : ctx → Type
obj Γ =  Pred.term (fst Γ)

data term (Γ : ctx) : (A : type (fst Γ)) → Type where
  var : (v : vars Γ) → term Γ (lookup (snd Γ) v)
  id : {A : obj Γ} → term Γ (A , A)
  co : {A B C : obj Γ} (f : term Γ (A , B)) (g : term Γ (B , C)) → term Γ (A , C)

1cell : (Γ : ctx) (A B : obj Γ) → Type
1cell Γ A B = term Γ (A , B)

subst-tgt : {Γ : ctx} {A B B' : obj Γ} → B ≡ B' → 1cell Γ A B → 1cell Γ A B'
subst-tgt {Γ = Γ} {A = A} p = subst (1cell Γ A) p

sub1 : (Δ Γ : ctx) → Pred.sub (fst Δ) (fst Γ) → Type
sub1 Δ (Γ' , []) σ = ⊤
sub1 Δ (Γ' , (A , B) ∷ Γ) σ = term Δ (Pred.ap σ A , Pred.ap σ B) × sub1 Δ (Γ' , Γ) σ

sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (fst Δ) (fst Γ)) (sub1 Δ Γ)

ap : {Δ Γ : ctx} (σ : sub Δ Γ) {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.ap (fst σ) A) (Pred.ap (fst σ) B)
ap-var : {Δ Γ : ctx} (σ : sub Δ Γ) (v : vars Γ) → 1cell Δ (Pred.ap (fst σ) (lookup (snd Γ) v .fst)) (Pred.ap (fst σ) (lookup (snd Γ) v .snd))

ap σ (var v) = ap-var σ v
ap σ id = id
ap σ (co a b) = co (ap σ a) (ap σ b)

ap-var {Δ} {Γ} σ v = lem Γ (fst σ) (snd σ) v
  where
  lem : (Γ : ctx) (σ' : Pred.sub (fst Δ) (fst Γ)) (σ : sub1 Δ Γ σ') (v : vars Γ) → 1cell Δ (Pred.ap σ' (lookup (snd Γ) v .fst)) (Pred.ap σ' (lookup (snd Γ) v .snd))
  lem (Γ' , _ ∷ Γ) σ' σ Fin.zero = fst σ
  lem (Γ' , _ ∷ Γ) σ' σ (Fin.suc v) = lem (Γ' , Γ) σ' (snd σ) v
