--- Type theoretical definition of incoherent unbiased bicategories / presentations of categories

module UCategory where

open import Prelude

import USet
module Pred = USet

-- data type (Γ : Pred.ctx) : Type where
  -- hom : {A : Pred.type (fst Γ)} → Pred.term Γ A → Pred.term Γ A → type Γ
type : Pred.ctx → Type
type Γ = Σ (Pred.type (fst Γ)) λ A → Pred.term Γ A × Pred.term Γ A

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

obj : ctx → Type
obj Γ = Pred.obj (fst Γ)

1cell : (Γ : ctx) → obj Γ → obj Γ → Type
1cell Γ A B = Pred.term (fst Γ) (A , B)

-- Shape of a 2-dimensional pasting scheme
pshape : Type
pshape = List Pred.pshape

pshape-src : pshape → Pred.pshape
pshape-src S = length S

pshape-tgt : pshape → Pred.pshape
pshape-tgt S = pshape-src S

data term : (Γ : ctx) (A : type (fst Γ)) → Type

2cell : (Γ : ctx) {A B : obj Γ} (a b : 1cell Γ A B) → Type
2cell Γ a b = term Γ (_ , a , b)

ps-from1 : (Γ : ctx) (S : Pred.pshape) {A B : obj Γ} (a : 1cell Γ A B) → Type
ps-from1 Γ zero a = ⊤
ps-from1 Γ (suc S) {A} {B} a = Σ (1cell Γ A B) λ b → Σ (2cell Γ a b) λ α → ps-from1 Γ S b

ps-from1-tgt : {Γ : ctx} {S : Pred.pshape} {A B : obj Γ} {a : 1cell Γ A B} → ps-from1 Γ S a → 1cell Γ A B
ps-from1-tgt {S = zero} {a = a} tt = a
ps-from1-tgt {S = suc S} (b , α , P) = ps-from1-tgt P

ps-from : (Γ : ctx) (S : pshape) (A : obj Γ) → Type
ps-from Γ [] A = ⊤
ps-from Γ (L ∷ S) A = Σ (obj Γ) λ B → Σ (1cell Γ A B) λ a → ps-from1 Γ L a × ps-from Γ S B

ps : ctx → pshape → Type
ps Γ S = Σ (obj Γ) λ A → ps-from Γ S A

ps-src0 : {Γ : ctx} {S : pshape} → ps Γ S → obj Γ
ps-src0 P = fst P

ps-tgt0 : {Γ : ctx} {S : pshape} → ps Γ S → obj Γ
ps-tgt0 {S = []} (A , _) = A
ps-tgt0 {S = L ∷ S} (A , B , a , _ , P) = ps-tgt0 {S = S} (B , P)

ps-src-from : {Γ : ctx} {S : pshape} (P : ps Γ S) → Pred.ps-from (fst Γ) (pshape-src S) (fst P)
ps-src-from {S = []} P = tt
ps-src-from {S = L ∷ S} (A , B , a , _ , P) = B , a , ps-src-from (B , P)

ps-src : {Γ : ctx} {S : pshape} → ps Γ S → Pred.ps (fst Γ) (pshape-src S)
ps-src {Γ} {S} (A , P) = A , ps-src-from (A , P)

ps-tgt-from : {Γ : ctx} {S : pshape} (P : ps Γ S) → Pred.ps-from (fst Γ) (pshape-tgt S) (fst P)
ps-tgt-from {S = []} P = tt
ps-tgt-from {S = L ∷ S} (A , B , a , P , Q) = B , ps-from1-tgt P , ps-tgt-from (B , Q)

ps-tgt : {Γ : ctx} {S : pshape} → ps Γ S → Pred.ps (fst Γ) (pshape-tgt S)
ps-tgt {Γ} {S} (A , P) = A , ps-tgt-from (A , P)

ps-glob-src : {Γ : ctx} {S : pshape} (P : ps Γ S) → Pred.ps-src (ps-src P) ≡ Pred.ps-src (ps-tgt P)
ps-glob-src {S = S} (A , P) = refl

ps-glob-tgt : {Γ : ctx} {S : pshape} (P : ps Γ S) → Pred.ps-tgt (ps-src P) ≡ Pred.ps-tgt (ps-tgt P)
ps-glob-tgt {S = []} (A , P) = refl
ps-glob-tgt {S = L ∷ S} (A , B , a , P , Q) = ps-glob-tgt (B , Q)

vars : ctx → Type
vars Γ = Fin (length (snd Γ))

data term where
  var : {Γ : ctx} (v : vars Γ) → term Γ (lookup (snd Γ) v)
  -- coh : {Γ : ctx} (S : Pred.pshape) (P : Pred.ps (fst Γ) S) (t u : Pred.term (fst Γ) (Pred.ps-hom P)) → 2cell Γ t u
  -- coh' : {Γ : Pred.ctx} {S : Pred.pshape} (P : Pred.ps Γ S) (t : Pred.term Γ (Pred.ps-hom P)) → 2cell (Γ , []) t (Pred.coh P) -- + reversibility
  coh : {Γ : ctx} (S : pshape) (P : ps Γ S) (t : Pred.term (fst Γ) (Pred.ps-hom (ps-src P))) (u : Pred.term (fst Γ) (Pred.ps-hom (ps-tgt P))) → 2cell Γ (Pred.subst-tgt (ps-glob-tgt P) t) u

elim : ∀ {ℓ} {Γ : ctx} (X : {A : type (fst Γ)} → term Γ A → Type ℓ)
  (fv : (v : vars Γ) → X (var v))
  (fc : (S : pshape) (P : ps Γ S) (t : Pred.term (fst Γ) (Pred.ps-hom (ps-src P))) (u : Pred.term (fst Γ) (Pred.ps-hom (ps-tgt P))) → X (coh S P t u))
  → {A : type (fst Γ)} (t : term Γ A) → X t
elim X fv fc (var v) = fv v
elim X fv fc (coh S P t u) = fc S P t u

lunit : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ (Pred.co Pred.id a) a
lunit {Γ} {A} {B} a = coh (0 ∷ []) (A , B , a , tt , tt) (Pred.co Pred.id a) a

runit : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ (Pred.co a Pred.id) a
runit {Γ} {A} {B} a = coh (0 ∷ []) (A , B , a , tt , tt) (Pred.co a Pred.id) a

assoc : {Γ : ctx} {A B C D : obj Γ} (a : 1cell Γ A B) (b : 1cell Γ B C) (c : 1cell Γ C D) → 2cell Γ (Pred.co (Pred.co a b) c) (Pred.co a (Pred.co b c))
assoc a b c = coh (0 ∷ 0 ∷ 0 ∷ []) (_ , _ , a , tt , _ , b , tt , _ , c , tt , tt) (Pred.co (Pred.co a b) c) (Pred.co a (Pred.co b c))

-- co1 : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ (Pred.co1 a) a
-- co1 a = coh 1 (_ , _ , a , tt) (Pred.co1 a) a

-- co1' : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ a (Pred.co1 a)
-- co1' a = coh 1 (_ , _ , a , tt) a (Pred.co1 a)

eqrefl : {Γ : ctx} {A B : obj Γ} {a : 1cell Γ A B} → 2cell Γ a a
eqrefl {Γ} {A} {B} {a} = coh (0 ∷ []) (_ , _ , a , tt , tt) a a

eqtrans : {Γ : ctx} {A B : obj Γ} {a b c : 1cell Γ A B} (α : 2cell Γ a b) (β : 2cell Γ b c) → 2cell Γ a c
eqtrans α β = coh (2 ∷ []) (_ , _ , _ , (_ , α , _ , β , tt) , tt) _ _

eqsym : {Γ : ctx} {A B : obj Γ} {a b : 1cell Γ A B} → 2cell Γ a b → 2cell Γ b a
eqsym α = coh (1 ∷ []) (_ , _ , _ , (_ , α , tt) , tt) _ _

subst-tgt0 : {Γ : ctx} {A B B' : obj Γ} {a b : 1cell Γ A B} (p : B ≡ B') → 2cell Γ a b → 2cell Γ (Pred.subst-tgt p a) (Pred.subst-tgt p b)
subst-tgt0 {Γ = Γ} {A = A} refl α = α
