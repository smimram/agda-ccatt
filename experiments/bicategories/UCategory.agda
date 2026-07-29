--- Type theoretical definition of incoherent unbiased bicategories / presentations of categories

module UCategory where

open import Prelude
open import Data.Product as Product
open import Data.List as List
open import Data.Fin as Fin hiding (_+_)

import UProp
import USet
module Pred = USet

type : Pred.ctx → Type
type Γ = Σ (Pred.type (Pred.ctx-pred Γ)) λ A → Pred.term Γ A × Pred.term Γ A

type-pred : {Γ : Pred.ctx} → type Γ → Pred.type (Pred.ctx-pred Γ)
type-pred = fst

type-src : {Γ : Pred.ctx} (A : type Γ) → Pred.term Γ (type-pred A)
type-src = fst ∘ snd

type-tgt : {Γ : Pred.ctx} (A : type Γ) → Pred.term Γ (type-pred A)
type-tgt = snd ∘ snd

wk0-type : {Γ : Pred.ctx} → type Γ → type (Pred.add0 Γ)
wk0-type A = Product.map Pred.wk0-type (λ a → Pred.sub-ap Pred.wk0 (fst a) , Pred.sub-ap Pred.wk0 (snd a)) A

wk1-type : {Γ : Pred.ctx} (A : Pred.type (Pred.ctx-pred Γ)) → type Γ → type (Pred.add1 Γ A)
wk1-type X A = Product.map (λ Y → Y) (λ a → Pred.wk1ap X (fst a) , Pred.wk1ap X (snd a)) A

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

-- Underlying set context
ctx-pred : ctx → Pred.ctx
ctx-pred = fst

ctx-pred² : ctx → UProp.ctx
ctx-pred² Γ = Pred.ctx-pred (ctx-pred Γ)

-- Includsion of set contexts
ctx-inc : Pred.ctx → ctx
ctx-inc Γ = Γ , []

ctx-empty : ctx
ctx-empty = ctx-inc Pred.ctx-empty

ctx-pt : ctx
ctx-pt = ctx-inc Pred.ctx-pt

data term : (Γ : ctx) (A : type (ctx-pred Γ)) → Type

vars : ctx → Type
vars Γ = Fin (length (snd Γ))

obj : ctx → Type
obj Γ = Pred.obj (ctx-pred Γ)

1cell : (Γ : ctx) → obj Γ → obj Γ → Type
1cell Γ A B = Pred.term (ctx-pred Γ) (A , B)

2cell : (Γ : ctx) {A B : obj Γ} (a b : 1cell Γ A B) → Type
2cell Γ a b = term Γ (_ , a , b)

-- Add a 0-generator
add0 : ctx → ctx
add0 (Γ' , Γ) = Pred.add0 Γ' , List.map wk0-type Γ

-- Add a 1-generator
add1 : (Γ : ctx) (A : Pred.type (ctx-pred² Γ)) → ctx
add1 (Γ' , Γ) A = (Pred.add1 Γ' A) , List.map (wk1-type A) Γ

-- Add a 2-generator
add2 : (Γ : ctx) (A : type (ctx-pred Γ)) → ctx
add2 (Γ' , Γ) A = Γ' , A ∷ Γ

-- The 0-generator we just added
last0 : (Γ : ctx) → obj (add0 Γ)
last0 Γ = Pred.last0 (fst Γ)

-- The 1-generator we just added
last1 : (Γ : ctx) (A : Pred.type (fst (fst Γ))) → Pred.term (fst (add1 Γ A)) A
last1 Γ A = Pred.last1 (fst Γ) A

-- The 2-generator we just added
last2 : (Γ : ctx) (A : type (fst Γ)) → term (add2 Γ A) A

sub2 : (Δ Γ : ctx) → Pred.sub (fst Δ) (fst Γ) → Type
sub2 Δ (Γ' , []) σ' = ⊤
sub2 Δ (Γ' , (A , a , b) ∷ Γ) σ' = 2cell Δ (Pred.sub-ap σ' a) (Pred.sub-ap σ' b) × sub2 Δ (Γ' , Γ) σ'

-- A substitution
sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (fst Δ) (fst Γ)) (sub2 Δ Γ)

sub-pred : {Δ Γ : ctx} → sub Δ Γ → Pred.sub (ctx-pred Δ) (ctx-pred Γ)
sub-pred = fst

-- Shape of a pasting scheme
pshape : Type
pshape = List Pred.pshape

pshape-src : pshape → Pred.pshape
pshape-src S = length S

pshape-tgt : pshape → Pred.pshape
pshape-tgt = pshape-src

ps-from1 : Pred.pshape → (Γ : ctx) {A B : obj Γ} (a : 1cell Γ A B) → ctx
ps-from1 zero Γ a = Γ
ps-from1 (suc S) Γ {A} {B} a = ps-from1 S (add2 (add1 Γ X) (_ , Pred.wk1ap X a , b)) b
  where
  X = (A , B)
  b = last1 Γ X

ps-from1-obj : (S : Pred.pshape) (Γ : ctx) {A B : obj Γ} (a : 1cell Γ A B) → obj (ps-from1 S Γ a) ≡ obj Γ
ps-from1-obj zero Γ a = refl
ps-from1-obj (suc S) Γ a = ps-from1-obj S (add2 (add1 Γ _) _) _

ps-from0 : pshape → (Γ : ctx) → obj Γ → ctx
ps-from0 [] Γ x = Γ
ps-from0 (S' ∷ S) Γ x = ps-from0 S (ps-from1 S' Γ' a) (transport (sym (ps-from1-obj S' Γ' a)) (last0 Γ))
  where
  A : Pred.type (ctx-pred² (add0 Γ))
  A = UProp.wk0ap x , last0 Γ
  a = last1 (add0 Γ) A
  Γ' = add1 (add0 Γ) A

ps : pshape → ctx
ps S = ps-from0 S ctx-pt (last0 ctx-empty)

-- A column of 2-cells only adds 1- and 2-cells: a substitution toward a context
-- Δ can thus be pushed along it
ps-from1-wk : (S : Pred.pshape) (Γ : ctx) {A B : obj Γ} (a : 1cell Γ A B)
              (Δ : Pred.ctx) (σ : Pred.sub (ctx-pred Γ) Δ) → Pred.sub (ctx-pred (ps-from1 S Γ a)) Δ
ps-from1-wk zero Γ a Δ σ = σ
ps-from1-wk (suc S) Γ {A} {B} a Δ σ = ps-from1-wk S (add2 (add1 Γ X) (X , Pred.wk1ap X a , b)) b Δ (Pred.sub-comp (Pred.wk1' X) σ)
  where
  X = (A , B)
  b = last1 Γ X

-- Pushing a substitution along a column does not change the image of the 0-cells
ps-from1-wk-ap : (S : Pred.pshape) (Γ : ctx) {A B : obj Γ} (a : 1cell Γ A B)
                 (Δ : Pred.ctx) (σ : Pred.sub (ctx-pred Γ) Δ) (z : Pred.obj Δ)
               → UProp.sub-ap (Pred.sub-pred (ps-from1-wk S Γ a Δ σ)) z ≡ transport (sym (ps-from1-obj S Γ a)) (UProp.sub-ap (fst σ) z)
ps-from1-wk-ap zero Γ a Δ σ z = refl
ps-from1-wk-ap (suc S) Γ {A} {B} a Δ σ z =
  trans
    (ps-from1-wk-ap S Γ₂ b Δ (Pred.sub-comp (Pred.wk1' X) σ) z)
    (cong (transport (sym (ps-from1-obj S Γ₂ b)))
          (trans (sym (UProp.sub-comp-ap (UProp.sub-id (ctx-pred² Γ)) (Pred.sub-pred σ) z))
                 (UProp.sub-id-ap (ctx-pred² Γ) (UProp.sub-ap (Pred.sub-pred σ) z))))
  where
  X = (A , B)
  b = last1 Γ X
  Γ₂ = add2 (add1 Γ X) (X , Pred.wk1ap X a , b)

-- The last 1-cell of a column (its source being the 1-cell we started with)
ps-from1-last : (S : Pred.pshape) (Γ : ctx) {A B : obj Γ} (a : 1cell Γ A B)
              → 1cell (ps-from1 S Γ a) (transport (sym (ps-from1-obj S Γ a)) A) (transport (sym (ps-from1-obj S Γ a)) B)
ps-from1-last zero Γ a = a
ps-from1-last (suc S) Γ {A} {B} a = ps-from1-last S (add2 (add1 Γ X) (X , Pred.wk1ap X a , b)) b
  where
  X = (A , B)
  b = last1 Γ X

-- Inclusion of the source into the ps, generalized to an arbitrary starting
-- point: we thread a substitution σ toward the linear pasting scheme being
-- built, x being the image of its last 0-cell y. The i-th arrow of the linear
-- scheme is sent to the first 1-cell of the i-th column.
ps-src-from : (S : pshape) (Γ : ctx) (x : obj Γ) (Δ : Pred.ctx) (y : Pred.obj Δ)
              (σ : Pred.sub (ctx-pred Γ) Δ) (p : x ≡ UProp.sub-ap (Pred.sub-pred σ) y)
            → Pred.sub (ctx-pred (ps-from0 S Γ x)) (Pred.ps-from (length S) Δ y)
ps-src-from [] Γ x Δ y σ p = σ
ps-src-from (S' ∷ S) Γ x Δ y σ p = ps-src-from S Γ₁ x₁ Δ₁ (Pred.last0 Δ) τ p₁
  where
  -- the extension of Γ by the new 0-cell, the new 1-cell and its column
  A : Pred.type (ctx-pred² (add0 Γ))
  A = UProp.wk0ap x , last0 Γ
  Γ' : ctx
  Γ' = add1 (add0 Γ) A
  a : 1cell Γ' (UProp.wk0ap x) (last0 Γ)
  a = last1 (add0 Γ) A
  Γ₁ : ctx
  Γ₁ = ps-from1 S' Γ' a
  x₁ : obj Γ₁
  x₁ = transport (sym (ps-from1-obj S' Γ' a)) (last0 Γ)
  -- the corresponding extension of Δ
  B : Pred.type (Pred.ctx-pred (Pred.add0 Δ))
  B = UProp.wk0ap y , Pred.last0 Δ
  Δ₁ : Pred.ctx
  Δ₁ = Pred.add1 (Pred.add0 Δ) B
  -- the weakening from Γ to Γ', along which σ is transported, and which is then extended by the new 0-cell
  wk : Pred.sub (ctx-pred Γ') (ctx-pred Γ)
  wk = Pred.sub-comp (Pred.wk1' A) Pred.wk0
  σ̂ : Pred.sub (ctx-pred Γ') Δ
  σ̂ = Pred.sub-comp wk σ
  σ₀ : Pred.sub (ctx-pred Γ') (Pred.add0 Δ)
  σ₀ = Pred.sub-add0 σ̂ (last0 Γ)
  -- the new 0-cell of Δ is sent to the new 0-cell of Γ, so that the new 1-cell of Δ can be sent to the new 1-cell a of Γ
  q : UProp.sub-ap (Pred.sub-pred σ₀) (UProp.wk0ap y) ≡ UProp.wk0ap x
  q = trans (Pred.sub-ap-add0 (Pred.sub-pred σ̂) (last0 Γ) y)
      (trans (sym (UProp.sub-comp-ap (Pred.sub-pred wk) (Pred.sub-pred σ) y))
      (trans (cong (UProp.sub-ap (Pred.sub-pred wk)) (sym p))
      (trans (sym (UProp.sub-comp-ap (UProp.sub-id (ctx-pred² (add0 Γ))) UProp.wk0 x))
             (UProp.sub-id-ap (ctx-pred² (add0 Γ)) (UProp.wk0ap x)))))
  a' : 1cell Γ' (UProp.sub-ap (Pred.sub-pred σ₀) (Pred.type-src B)) (UProp.sub-ap (Pred.sub-pred σ₀) (Pred.type-tgt B))
  a' = subst (λ u → 1cell Γ' u (last0 Γ)) (sym q) a
  -- ...and pushed along the column
  τ : Pred.sub (ctx-pred Γ₁) Δ₁
  τ = ps-from1-wk S' Γ' a Δ₁ (Pred.sub-add1 σ₀ a')
  p₁ : x₁ ≡ UProp.sub-ap (Pred.sub-pred τ) (Pred.last0 Δ)
  p₁ = sym (ps-from1-wk-ap S' Γ' a Δ₁ (Pred.sub-add1 σ₀ a') (Pred.last0 Δ))

-- Inclusion of the target into the ps: as above, but the i-th arrow is now sent
-- to the last 1-cell of the i-th column
ps-tgt-from : (S : pshape) (Γ : ctx) (x : obj Γ) (Δ : Pred.ctx) (y : Pred.obj Δ)
              (σ : Pred.sub (ctx-pred Γ) Δ) (p : x ≡ UProp.sub-ap (Pred.sub-pred σ) y)
            → Pred.sub (ctx-pred (ps-from0 S Γ x)) (Pred.ps-from (length S) Δ y)
ps-tgt-from [] Γ x Δ y σ p = σ
ps-tgt-from (S' ∷ S) Γ x Δ y σ p = ps-tgt-from S Γ₁ x₁ Δ₁ (Pred.last0 Δ) (Pred.sub-add1 τ₀ b') p₁
  where
  A : Pred.type (ctx-pred² (add0 Γ))
  A = UProp.wk0ap x , last0 Γ
  Γ' : ctx
  Γ' = add1 (add0 Γ) A
  a : 1cell Γ' (UProp.wk0ap x) (last0 Γ)
  a = last1 (add0 Γ) A
  Γ₁ : ctx
  Γ₁ = ps-from1 S' Γ' a
  x₁ : obj Γ₁
  x₁ = transport (sym (ps-from1-obj S' Γ' a)) (last0 Γ)
  B : Pred.type (Pred.ctx-pred (Pred.add0 Δ))
  B = UProp.wk0ap y , Pred.last0 Δ
  Δ₁ : Pred.ctx
  Δ₁ = Pred.add1 (Pred.add0 Δ) B
  wk : Pred.sub (ctx-pred Γ') (ctx-pred Γ)
  wk = Pred.sub-comp (Pred.wk1' A) Pred.wk0
  σ̂ : Pred.sub (ctx-pred Γ') Δ
  σ̂ = Pred.sub-comp wk σ
  σ₀ : Pred.sub (ctx-pred Γ') (Pred.add0 Δ)
  σ₀ = Pred.sub-add0 σ̂ (last0 Γ)
  q : UProp.sub-ap (Pred.sub-pred σ₀) (UProp.wk0ap y) ≡ UProp.wk0ap x
  q = trans (Pred.sub-ap-add0 (Pred.sub-pred σ̂) (last0 Γ) y)
      (trans (sym (UProp.sub-comp-ap (Pred.sub-pred wk) (Pred.sub-pred σ) y))
      (trans (cong (UProp.sub-ap (Pred.sub-pred wk)) (sym p))
      (trans (sym (UProp.sub-comp-ap (UProp.sub-id (ctx-pred² (add0 Γ))) UProp.wk0 x))
             (UProp.sub-id-ap (ctx-pred² (add0 Γ)) (UProp.wk0ap x)))))
  -- here we first push the substitution along the column, so that we can send the new 1-cell of Δ to the last 1-cell of the column
  τ₀ : Pred.sub (ctx-pred Γ₁) (Pred.add0 Δ)
  τ₀ = ps-from1-wk S' Γ' a (Pred.add0 Δ) σ₀
  e1 : UProp.sub-ap (Pred.sub-pred τ₀) (UProp.wk0ap y) ≡ transport (sym (ps-from1-obj S' Γ' a)) (UProp.wk0ap x)
  e1 = trans (ps-from1-wk-ap S' Γ' a (Pred.add0 Δ) σ₀ (UProp.wk0ap y))
             (cong (transport (sym (ps-from1-obj S' Γ' a))) q)
  e2 : UProp.sub-ap (Pred.sub-pred τ₀) (Pred.last0 Δ) ≡ x₁
  e2 = ps-from1-wk-ap S' Γ' a (Pred.add0 Δ) σ₀ (Pred.last0 Δ)
  b' : 1cell Γ₁ (UProp.sub-ap (Pred.sub-pred τ₀) (Pred.type-src B)) (UProp.sub-ap (Pred.sub-pred τ₀) (Pred.type-tgt B))
  b' = subst₂ (1cell Γ₁) (sym e1) (sym e2) (ps-from1-last S' Γ' a)
  p₁ : x₁ ≡ UProp.sub-ap (Pred.sub-pred (Pred.sub-add1 τ₀ b')) (Pred.last0 Δ)
  p₁ = sym e2

ps-src' : (S : pshape) → Pred.sub (ctx-pred (ps S)) (Pred.ps (pshape-src S))
ps-src' S = ps-src-from S ctx-pt (last0 ctx-empty) Pred.ctx-pt (Pred.last0 Pred.ctx-empty) (Pred.last0 Pred.ctx-empty ∷ [] , tt) refl

ps-src0 : (S : pshape) → UProp.sub (ctx-pred² (ps S)) (Pred.ctx-pred (Pred.ps (pshape-src S)))
ps-src0 S = fst (ps-src' S)

ps-src1 : (S : pshape) → Pred.sub1 (ctx-pred (ps S)) (Pred.ps (pshape-src S)) (ps-src0 S)
ps-src1 S = snd (ps-src' S)

-- Inclusion of the source into the ps
ps-src : (S : pshape) → sub (ps S) (ctx-inc (Pred.ps (pshape-src S)))
ps-src S = (ps-src0 S , ps-src1 S) , tt

ps-tgt' : (S : pshape) → Pred.sub (ctx-pred (ps S)) (Pred.ps (pshape-tgt S))
ps-tgt' S = ps-tgt-from S ctx-pt (last0 ctx-empty) Pred.ctx-pt (Pred.last0 Pred.ctx-empty) (Pred.last0 Pred.ctx-empty ∷ [] , tt) refl

ps-tgt0 : (S : pshape) → UProp.sub (ctx-pred² (ps S)) (Pred.ctx-pred (Pred.ps (pshape-tgt S)))
ps-tgt0 S = fst (ps-tgt' S)

ps-tgt1 : (S : pshape) → Pred.sub1 (ctx-pred (ps S)) (Pred.ps (pshape-tgt S)) (ps-tgt0 S)
ps-tgt1 S = snd (ps-tgt' S)

-- Inclusion of the target into the ps
ps-tgt : (S : pshape) → sub (ps S) (ctx-inc (Pred.ps (pshape-tgt S)))
ps-tgt S = (ps-tgt0 S , ps-tgt1 S) , tt

-- TEST: variant of the definition of ps where we explicitly handle natural numbers instead of being inductive
-- EX: [3,2] has
-- - 0-cells: 2 1 0
-- - 1-cells: (1,0) (1,0) (2,1) (2,1) (2,1)
-- - 1-cells: 2 ⇒ 3, 3 ⇒ 4, 0 ⇒ 1
-- (lists are "reversed" wrt the natural order)
-- ps' : pshape → ctx
-- ps' S = (ps0 S , ps1 S) , ps2 S
  -- where
  -- ps0 : pshape → UProp.ctx
  -- ps0 S = suc (length S)
  -- ps1 : (S : pshape) → List (Pred.type (ps0 S))
  -- ps1 [] = []
  -- ps1 (S' ∷ S) =
    -- List.map (Product.map wk wk) (ps1 S) ++
    -- List.replicate (suc S') (fromℕ< {m = suc (List.length S)} ≤-refl , fromℕ< {m = List.length S} (n≤1+n _))
    -- where
    -- wk = inject₁
  -- ps2 : (S : pshape) → List (type (ps0 S , ps1 S))
  -- ps2 [] = []
  -- ps2 (S' ∷ S) =
    -- List.map (Product.map wk λ x → {!!} , {!!}) (ps2 S) ++
    -- List.applyUpTo (λ i → (fromℕ< {m = suc (List.length S)} ≤-refl , fromℕ< {m = List.length S} (n≤1+n _)) , {!!} , {!!}) S'
    -- where
    -- wk : Pred.type (ps0 S) → Pred.type (ps0 (S' ∷ S))
    -- wk = {!!}

-- TEST: variant of the definition of ps where we explicitly handle natural numbers instead of being inductive
-- EX: [3,2] has
-- - 0-cells: 0 1 2
-- - 1-cells: (0,1) (0,1) (0,1) (1,2) (1,2)
-- - 1-cells: 0 ⇒ 1, 1 ⇒ 2, 3 ⇒ 4
-- ps' : pshape → ctx
-- ps' S = {!!} -- (ps0 S , ps1 S) , ps2 S
  -- where
  -- ps0 : pshape → UProp.ctx
  -- ps0 S = suc (length S)
  -- ps1 : ℕ → (S : pshape) → List (Pred.type {!!})
  -- ps1 k [] = []
  -- ps1 (S' ∷ S) =
    -- List.map (Product.map wk wk) (ps1 S) ++
    -- List.replicate (suc S') (fromℕ< {m = suc (List.length S)} ≤-refl , fromℕ< {m = List.length S} (n≤1+n _))
    -- where
    -- wk = inject₁
  -- ps2 : (S : pshape) → List (type (ps0 S , ps1 S))
  -- ps2 [] = []
  -- ps2 (S' ∷ S) =
    -- List.map (Product.map wk λ x → {!!} , {!!}) (ps2 S) ++
    -- List.applyUpTo (λ i → (fromℕ< {m = suc (List.length S)} ≤-refl , fromℕ< {m = List.length S} (n≤1+n _)) , {!!} , {!!}) S'
    -- where
    -- wk : Pred.type (ps0 S) → Pred.type (ps0 (S' ∷ S))
    -- wk = {!!}


data term where
  var : {Γ : ctx} (v : vars Γ) → term Γ (lookup (snd Γ) v)
  coh : {Γ : ctx} (S : pshape) (σ : sub Γ (ps S)) (t : 1cell (ps S) {!ps-src (ps S)!} {!!}) (u : 1cell (ps S) {!!} {!!}) → 2cell Γ {!!} {!!}

last2 Γ A = var zero

-- lunit : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ (Pred.co Pred.id a) a
-- lunit {Γ} {A} {B} a = coh (0 ∷ []) (A , B , a , tt , tt) (Pred.co Pred.id a) a

-- runit : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ (Pred.co a Pred.id) a
-- runit {Γ} {A} {B} a = coh (0 ∷ []) (A , B , a , tt , tt) (Pred.co a Pred.id) a

-- assoc : {Γ : ctx} {A B C D : obj Γ} (a : 1cell Γ A B) (b : 1cell Γ B C) (c : 1cell Γ C D) → 2cell Γ (Pred.co (Pred.co a b) c) (Pred.co a (Pred.co b c))
-- assoc a b c = coh (0 ∷ 0 ∷ 0 ∷ []) (_ , _ , a , tt , _ , b , tt , _ , c , tt , tt) (Pred.co (Pred.co a b) c) (Pred.co a (Pred.co b c))

-- -- co1 : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ (Pred.co1 a) a
-- -- co1 a = coh 1 (_ , _ , a , tt) (Pred.co1 a) a

-- -- co1' : {Γ : ctx} {A B : obj Γ} (a : 1cell Γ A B) → 2cell Γ a (Pred.co1 a)
-- -- co1' a = coh 1 (_ , _ , a , tt) a (Pred.co1 a)

-- eqrefl : {Γ : ctx} {A B : obj Γ} {a : 1cell Γ A B} → 2cell Γ a a
-- eqrefl {Γ} {A} {B} {a} = coh (0 ∷ []) (_ , _ , a , tt , tt) a a

-- eqtrans : {Γ : ctx} {A B : obj Γ} {a b c : 1cell Γ A B} (α : 2cell Γ a b) (β : 2cell Γ b c) → 2cell Γ a c
-- eqtrans α β = coh (2 ∷ []) (_ , _ , _ , (_ , α , _ , β , tt) , tt) _ _

-- eqsym : {Γ : ctx} {A B : obj Γ} {a b : 1cell Γ A B} → 2cell Γ a b → 2cell Γ b a
-- eqsym α = coh (1 ∷ []) (_ , _ , _ , (_ , α , tt) , tt) _ _

-- subst-tgt0 : {Γ : ctx} {A B B' : obj Γ} {a b : 1cell Γ A B} (p : B ≡ B') → 2cell Γ a b → 2cell Γ (Pred.subst-tgt p a) (Pred.subst-tgt p b)
-- subst-tgt0 {Γ = Γ} {A = A} refl α = α
