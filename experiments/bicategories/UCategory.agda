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
type Γ = Σ (Pred.type (fst Γ)) λ A → Pred.term Γ A × Pred.term Γ A

wk0-type : {Γ : Pred.ctx} → type Γ → type (Pred.add0 Γ)
wk0-type A = Product.map {!!} {!!} A -- Pred.sub-ap Pred.wk0

wk1-type : {Γ : Pred.ctx} (A : Pred.type (fst Γ)) → type Γ → type (Pred.add1 Γ A)
wk1-type X A = Product.map {!!} {!!} A

ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

-- Underlying set context
ctx-pred : ctx → Pred.ctx
ctx-pred = fst

-- Includsion of set contexts
ctx-inc : Pred.ctx → ctx
ctx-inc Γ = Γ , []

ctx-empty : ctx
ctx-empty = ctx-inc Pred.ctx-empty

ctx-pt : ctx
ctx-pt = ctx-inc Pred.ctx-pt

data term : (Γ : ctx) (A : type (fst Γ)) → Type

vars : ctx → Type
vars Γ = Fin (length (snd Γ))

obj : ctx → Type
obj Γ = Pred.obj (fst Γ)

1cell : (Γ : ctx) → obj Γ → obj Γ → Type
1cell Γ A B = Pred.term (fst Γ) (A , B)

2cell : (Γ : ctx) {A B : obj Γ} (a b : 1cell Γ A B) → Type
2cell Γ a b = term Γ (_ , a , b)

-- Add a 0-generator
add0 : ctx → ctx
add0 (Γ' , Γ) = Pred.add0 Γ' , List.map wk0-type Γ

-- Add a 1-generator
add1 : (Γ : ctx) (A : Pred.type (fst (fst Γ))) → ctx
add1 (Γ' , Γ) A = (Pred.add1 Γ' A) , List.map (wk1-type A) Γ

-- Add a 2-generator
add2 : (Γ : ctx) (A : type (fst Γ)) → ctx
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

sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (fst Δ) (fst Γ)) (sub2 Δ Γ)

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
  A : Pred.type (fst (fst (add0 Γ)))
  A = UProp.wk0ap x , last0 Γ
  a = last1 (add0 Γ) A
  Γ' = add1 (add0 Γ) A

ps : pshape → ctx
ps S = ps-from0 S ctx-pt (last0 ctx-empty)

ps-src0 : (S : pshape) → UProp.sub (Pred.ctx-pred (Pred.ps (pshape-src S))) (Pred.ctx-pred (ctx-pred (ps S)))
ps-src0 [] = # 0 ∷ []
ps-src0 (S' ∷ S) = {!!}

ps-src1 : (S : pshape) → Pred.sub1 (Pred.ps (pshape-src S)) (ctx-pred (ps S)) (ps-src0 S)
ps-src1 S = {!!}

-- Inclusion of the source into the ps
ps-src : (S : pshape) → sub (ctx-inc (Pred.ps (pshape-src S))) (ps S)
ps-src S = (ps-src0 S , ps-src1 S) , {!!}

-- Inclusion of the source into the ps
ps-tgt : (S : pshape) → sub (ctx-inc (Pred.ps (pshape-tgt S))) (ps S)
ps-tgt S = {!!}

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
ps' : pshape → ctx
ps' S = {!!} -- (ps0 S , ps1 S) , ps2 S
  where
  ps0 : pshape → UProp.ctx
  ps0 S = suc (length S)
  ps1 : ℕ → (S : pshape) → List (Pred.type {!!})
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
