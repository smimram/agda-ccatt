--- Type theoretical definition of incoherent unbiased categories
---
--- Version without explicit substitutions nor pre-syntax

module USet where

open import Prelude

import UProp as Pred

-- data type (Γ : Pred.ctx) : Type where
  -- hom : Pred.term Γ → Pred.term Γ → type Γ
type : (Γ : Pred.ctx) → Type
type Γ = Pred.term Γ × Pred.term Γ

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

-- Objects / 0-cells
obj : ctx → Type
obj Γ = Pred.term (fst Γ)

-- The shape of a pasting scheme consists in a number of composable arrows
pshape : Type
pshape = ℕ

-- A term
data term : (Γ : ctx) (A : type (fst Γ)) → Type

-- A pasting scheme of given shape from a given object, ie a substitution from to the shape
ps-from : (Γ : ctx) → pshape → obj Γ → Type
ps-from Γ zero A = ⊤
ps-from Γ (suc n) A = Σ (obj Γ) λ B → Σ (term Γ (A , B)) λ f → ps-from Γ n B

-- Substituted pasting schemes
ps : ctx → pshape → Type
ps Γ S = Σ (obj Γ) λ A → ps-from Γ S A

-- The source of a ps
ps-src : {Γ : ctx} {S : pshape} → ps Γ S → obj Γ
ps-src {Γ} {S} (A , _) = A

-- The target of a ps
ps-tgt : {Γ : ctx} {S : pshape} → ps Γ S → obj Γ
ps-tgt {Γ} {zero} (A , tt) = A
ps-tgt {Γ} {suc S} (A , B , f , P) = ps-tgt {S = S} (B , P)

-- The hom type of a ps
ps-hom : {Γ : ctx} {n : pshape} → ps Γ n → type (fst Γ)
ps-hom P = ps-src P , ps-tgt P

-- Variables in a ps
vars : ctx → Type
vars Γ = Fin (length (snd Γ))

-- Terms
data term where
  var : {Γ : ctx} (v : vars Γ) → term Γ (lookup (snd Γ) v)
  coh : {Γ : ctx} (S : pshape) (P : ps Γ S) → term Γ (ps-hom P)

-- Elimination principle for terms
elim : {Γ : ctx} {ℓ : Level} (X : {A : type (fst Γ)} → term Γ A → Type ℓ) (fv : (v : vars Γ) → X (var v)) (fc : (S : pshape) → (P : ps Γ S) → X (coh S P)) {A : type (fst Γ)} (t : term Γ A) → X t
elim X fv fc (var v) = fv v
elim X fv fc (coh S P) = fc S P

-- A 1-cell
1cell : (Γ : ctx) (A B : obj Γ) → Type
1cell Γ A B = term Γ (A , B)

-- Identity
id : {Γ : ctx} {A : obj Γ} → 1cell Γ A A
id {A = A} = coh 0 (A , tt)

-- Unary composition
co1 : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 1cell Γ A B
co1 {Γ} a = coh 1 (_ , _ , a , tt)

-- Composition
co : {Γ : ctx} {A B C : obj Γ} (a : 1cell Γ A B) (b : 1cell Γ B C) → 1cell Γ A C
co {Γ} {A} {B} {C} a b = coh 2 (A , B , a , C , b , tt)

subst-tgt : {Γ : ctx} {A B B' : obj Γ} → B ≡ B' → 1cell Γ A B → 1cell Γ A B'
subst-tgt {Γ = Γ} {A = A} p = subst (1cell Γ A) p

sub1 : (Δ Γ : ctx) → Pred.sub (fst Δ) (fst Γ) → Type
sub1 Δ (Γ' , []) σ = ⊤
sub1 Δ (Γ' , (A , B) ∷ Γ) σ = term Δ (Pred.ap σ A , Pred.ap σ B) × sub1 Δ (Γ' , Γ) σ

sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (fst Δ) (fst Γ)) (sub1 Δ Γ)

ap : {Δ Γ : ctx} (σ : sub Δ Γ) {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.ap (fst σ) A) (Pred.ap (fst σ) B)
ap-var : {Δ Γ : ctx} (σ : sub Δ Γ) (v : vars Γ) → 1cell Δ (Pred.ap (fst σ) (lookup (snd Γ) v .fst)) (Pred.ap (fst σ) (lookup (snd Γ) v .snd))
ap-ps : {Δ Γ : ctx} (σ : sub Δ Γ) (S : pshape) → ps Γ S → ps Δ S
ap-ps-from : {Δ Γ : ctx} (σ : sub Δ Γ) (S : pshape) (A : obj Γ) → ps-from Γ S A → ps-from Δ S (Pred.ap (fst σ) A)
ap-ps-src : {Δ Γ : ctx} (σ : sub Δ Γ) {S : pshape} (P : ps Γ S) → ps-src (ap-ps σ S P) ≡ Pred.ap (fst σ) (ps-src P)
ap-ps-tgt : {Δ Γ : ctx} (σ : sub Δ Γ) {S : pshape} (P : ps Γ S) → ps-tgt (ap-ps σ S P) ≡ Pred.ap (fst σ) (ps-tgt P)

ap σ (var v) = ap-var σ v
ap {Δ} σ (coh S P) = subst₂ (1cell Δ) (ap-ps-src σ P) (ap-ps-tgt σ P) (coh S (ap-ps σ S P))

ap-var {Δ} {Γ} σ v = lem Γ (fst σ) (snd σ) v
  where
  lem : (Γ : ctx) (σ' : Pred.sub (fst Δ) (fst Γ)) (σ : sub1 Δ Γ σ') (v : vars Γ) → 1cell Δ (Pred.ap σ' (lookup (snd Γ) v .fst)) (Pred.ap σ' (lookup (snd Γ) v .snd))
  lem (Γ' , _ ∷ Γ) σ' σ Fin.zero = fst σ
  lem (Γ' , _ ∷ Γ) σ' σ (Fin.suc v) = lem (Γ' , Γ) σ' (snd σ) v

ap-ps σ S (A , P) = Pred.ap (fst σ) A , ap-ps-from σ S A P

ap-ps-from σ zero A P = tt
ap-ps-from σ (suc S) A (B , a , P) = Pred.ap (fst σ) B , ap σ a , ap-ps-from σ S B P

ap-ps-src σ P = refl

ap-ps-tgt σ {zero} P = refl
ap-ps-tgt σ {suc S} (A , B , a , P) = ap-ps-tgt σ (B , P)
