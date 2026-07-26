--- Type theoretical definition of categories / incoherent bicategories

module Category where

open import Prelude
import Set as Pred

type : Pred.ctx → Type
type Γ = Σ (Pred.type (fst Γ)) λ A → Pred.term Γ A × Pred.term Γ A

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

obj : ctx → Type
obj = Pred.obj ∘ fst

1cell : (Γ : ctx) → obj Γ → obj Γ → Type
1cell (Γ , _) = Pred.1cell Γ

data term : (Γ : ctx) → type (fst Γ) → Type

2cell : (Γ : ctx) {A B : obj Γ} (a b : 1cell Γ A B) → Type
2cell Γ a b = term Γ (_ , a , b)

data term where
  var : {Γ : ctx} (v : Fin (length (snd Γ))) → term Γ (lookup (snd Γ) v)
  lunit : {Γ : ctx} {A B : obj Γ} (f : 1cell Γ A B) → 2cell Γ (Pred.co Pred.id f) f
  runit : {Γ : ctx} {A B : obj Γ} (f : 1cell Γ A B) → 2cell Γ (Pred.co f Pred.id) f
  assoc : {Γ : ctx} {A B C D : obj Γ} (f : 1cell Γ A B) (g : 1cell Γ B C) (h : 1cell Γ C D) → 2cell Γ (Pred.co (Pred.co f g) h) (Pred.co f (Pred.co g h))
  eqrefl : {Γ : ctx} {A B : obj Γ} {f : 1cell Γ A B} → 2cell Γ f f
  eqtrans : {Γ : ctx} {A B : obj Γ} {f g h : 1cell Γ A B} → 2cell Γ f g → 2cell Γ g h → 2cell Γ f h
  eqsym : {Γ : ctx} {A B : obj Γ} {f g : 1cell Γ A B} → 2cell Γ f g → 2cell Γ g f

eqtrans3 : {Γ : ctx} {A B : obj Γ} {f g h i : 1cell Γ A B} → 2cell Γ f g → 2cell Γ g h → 2cell Γ h i → 2cell Γ f i
eqtrans3 α β γ = eqtrans α (eqtrans β γ)

subst-tgt0 : {Γ : ctx} {A B B' : obj Γ} {a b : 1cell Γ A B} (p : B ≡ B') → 2cell Γ a b → 2cell Γ (Pred.subst-tgt p a) (Pred.subst-tgt p b)
subst-tgt0 {Γ = Γ} {A = A} refl α = α
