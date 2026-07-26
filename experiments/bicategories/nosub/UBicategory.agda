--- Type theoretical definition of incoherent unbiased tricategories / presentations of bicategories

open import Prelude
open import Data.List as List

import UCategory as Pred

data type (Γ : Pred.ctx) : Type where
  hom : {A : Pred.type (fst Γ)} → Pred.term Γ A → Pred.term Γ A → type Γ

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

obj : ctx → Type
obj Γ = Pred.obj (fst Γ)

1cell : (Γ : ctx) → obj Γ → obj Γ → Type
1cell Γ = Pred.1cell (fst Γ)

2cell : (Γ : ctx) {A B : obj Γ} → 1cell Γ A B → 1cell Γ A B → Type
2cell Γ a b = Pred.2cell (fst Γ) a b

pshape : Type
pshape = List Pred.pshape

pshape-src : pshape → Pred.pshape
pshape-src = List.map Pred.pshape-src

pshape-tgt : pshape → Pred.pshape
pshape-tgt = List.map Pred.pshape-tgt

data term : (Γ : ctx) (A : type (fst Γ)) → Type

3cell : (Γ : ctx) {A B : obj Γ} {a b : 1cell Γ A B} (α β : 2cell Γ a b) → Type
3cell Γ α β = term Γ (hom α β)

ps-from2 : (Γ : ctx) (S : Pred.Pred.pshape) {A B : obj Γ} {a b : 1cell Γ A B} (α : 2cell Γ a b) → Type
ps-from2 Γ zero α = ⊤
ps-from2 Γ (suc S) {a = a} {b = b} α = Σ (2cell Γ a b) λ β → 3cell Γ α β × ps-from2 Γ S β

ps-from1 : (Γ : ctx) (S : Pred.pshape) {A B : obj Γ} (a : 1cell Γ A B) → Type
ps-from1 Γ [] a = ⊤
ps-from1 Γ (L ∷ S) {A} {B} a = Σ (1cell Γ A B) λ b → Σ (2cell Γ a b) λ β → ps-from2 Γ L β × ps-from1 Γ S b

ps-from0 : (Γ : ctx) (S : pshape) (A : obj Γ) → Type
ps-from0 Γ [] A = ⊤
ps-from0 Γ (L ∷ S) A = Σ (obj Γ) λ B → Σ (1cell Γ A B) λ a → ps-from1 Γ L a × ps-from0 Γ S B

ps : ctx → pshape → Type
ps Γ S = Σ (obj Γ) (ps-from0 Γ S)

-- ps-src-from0 : {Γ : ctx} {S : pshape} (P : ps Γ S) → 

ps-src : {Γ : ctx} {S : pshape} → ps Γ S → Pred.ps (fst Γ) (pshape-src S)
ps-src (A , P) = A , {!!}

ps-tgt : {Γ : ctx} {S : pshape} → ps Γ S → Pred.ps (fst Γ) (pshape-src S)
ps-tgt P = {!!}

data term where
  var : {Γ : ctx} (v : Σ ℕ λ v → v < length (snd Γ)) → term Γ (uncurry (nth (snd Γ)) v)
  -- coh : {Γ : ctx} ...
  -- uco : {Γ : ctx} {S : pshape} (P : ps Γ S) → 3cell Γ {!Pred.coh (ps-src P)!} (Pred.coh (ps-tgt P))
