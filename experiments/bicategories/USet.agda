{-# OPTIONS --allow-unsolved-metas #-}

--- Type theoretical definition of incoherent unbiased categories / sets

module USet where

open import Prelude
open import Data.Product as Product
open import Data.List as List
open import Data.Fin as Fin

import UProp as Pred

-- A type in a Prop-context is an arrow xᵢ→yᵢ
type : (Γ : Pred.ctx) → Type
type Γ = Pred.term Γ × Pred.term Γ

wk0-type : {Γ : Pred.ctx} → type Γ → type (Pred.add0 Γ)
wk0-type A = Product.map Pred.wk0ap Pred.wk0ap A

-- A context
ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

-- The empty context
ctx-empty : ctx
ctx-empty = Pred.ctx-empty , []

data term : (Γ : ctx) (A : type (fst Γ)) → Type

-- The 0-variables in a context
obj : ctx → Type
obj Γ = Pred.term (fst Γ)

-- A 1-cell in a context
1cell : (Γ : ctx) (A B : obj Γ) → Type
1cell Γ A B = term Γ (A , B)

-- The 1-variables in a context
vars : ctx → Type
vars Γ = Fin (length (snd Γ))

-- Add a 0-cell in a context
add0 : ctx → ctx
add0 (Γ' , Γ) = Pred.add0 Γ' , List.map wk0-type Γ

-- Add a 1-cell in a context
add1 : (Γ : ctx) (A : type (fst Γ)) → ctx
add1 (Γ' , Γ) A = Γ' , A ∷ Γ

-- The punctual context with one 0-cell
ctx-pt : ctx
ctx-pt = add0 ctx-empty

-- The 0-variable we just added
last0 : (Γ : ctx) → obj (add0 Γ)
last0 Γ = Pred.last0 (fst Γ)

-- The 1-variable we just added
last1 : (Γ : ctx) (A : type (fst Γ)) → term (add1 Γ A) A

-- A 1-substitution with given underlying 0-substitutiton
sub1 : (Δ Γ : ctx) → Pred.sub (fst Δ) (fst Γ) → Type
sub1 Δ (Γ' , []) σ' = ⊤
sub1 Δ (Γ' , (A , B) ∷ Γ) σ' = 1cell Δ (Pred.sub-ap σ' A) (Pred.sub-ap σ' B) × sub1 Δ (Γ' , Γ) σ'

-- Image of a variable under a substitution
sub1-lookup : {Δ Γ : ctx} {σ' : Pred.sub (fst Δ) (fst Γ)} (σ : sub1 Δ Γ σ') (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd))
sub1-lookup {Γ = Γ' , (A , B) ∷ Γ} σ zero = fst σ
sub1-lookup {Γ = Γ' , (A , B) ∷ Γ} σ (suc i) = sub1-lookup (snd σ) i

sub1-ap : {Δ Γ : ctx} {σ' : Pred.sub (fst Δ) (fst Γ)} (σ : sub1 Δ Γ σ') {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap σ' A) (Pred.sub-ap σ' B)

-- Composite substiutition
sub1-comp : {Γ₁ Γ₂ Γ₃ : ctx}
            {σ' : Pred.sub (fst Γ₁) (fst Γ₂)}
            {τ' : Pred.sub (fst Γ₂) (fst Γ₃)} →
            sub1 Γ₁ Γ₂ σ' → sub1 Γ₂ Γ₃ τ' → sub1 Γ₁ Γ₃ (Pred.sub-comp σ' τ')
sub1-comp {Γ₃ = Γ₃' , []} σ tt = tt
sub1-comp {Γ₁ = Γ₁} {Γ₃ = Γ₃' , (A , B) ∷ Γ₃} {σ'} {τ'} σ (a , τ) = subst₂ (1cell Γ₁) (Pred.sub-comp-ap σ' τ' A) (Pred.sub-comp-ap σ' τ' B) (sub1-ap σ a) , (sub1-comp σ τ)

sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (fst Δ) (fst Γ)) (sub1 Δ Γ)

-- Apply a substitution
sub-ap : {Δ Γ : ctx} (σ : sub Δ Γ) {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap (fst σ) A) (Pred.sub-ap (fst σ) B)
sub-ap σ a = sub1-ap (σ .snd) a

-- Compose substitutions
sub-comp : {Γ'' Γ' Γ : ctx} (τ : sub Γ'' Γ') (σ : sub Γ' Γ) → sub Γ'' Γ
sub-comp τ σ = Pred.sub-comp (fst τ) (fst σ) , sub1-comp (τ .snd) (σ .snd)

-- -- Substitution corresponding to weakening a 1-variable
-- wk1 : {Γ : ctx} (A : type (fst Γ)) → sub (add1 Γ A) Γ
-- wk1 {Γ = Γ' , []} A = Pred.sub-id Γ' , tt
-- wk1 {Γ = Γ' , x ∷ Γ} A = Pred.sub-id Γ' , {!!} , {!wk1 ?!}

-- Substitution corresponding to weakening a 1-variable
wk1 : (Γ : ctx) (A : type (fst Γ)) → sub1 (add1 Γ A) Γ (Pred.sub-id (fst Γ))

wk1' : {Γ : ctx} (A : type (fst Γ)) → sub (add1 Γ A) Γ
wk1' {Γ} A = Pred.sub-id (fst Γ) , wk1 Γ A

wk1ap : {Γ : ctx} {X : type (fst Γ)} (A : type (fst Γ)) → term Γ X → term (add1 Γ A) X
wk1ap A = {!sub-ap (wk1' A)!} -- sub-ap (wk1 A)

wk0 : {Γ : ctx} → sub (add0 Γ) Γ
wk0 {Γ' , Γ} = Pred.wk0 , σ Γ -- à peu près sub-id
  where
  σ : (Γ : _) → sub1 (add0 (Γ' , Γ)) (Γ' , Γ) Pred.wk0
  σ [] = tt
  σ (A ∷ Γ) = {!A!} , {!σ Γ!}

-- The shape of a pasting scheme is the number of arrows we compose
pshape : Type
pshape = ℕ

-- {-# TERMINATING #-}
-- ps-from : {Γ : Pred.ctx} (n : Pred.term Γ) → List (type Γ)
-- ps-from zero = []
-- ps-from (suc n) = (suc n , inject₁ n) ∷ ps-from (inject₁ n)

-- ps : pshape → ctx
-- ps n = suc n , ps-from (fromℕ n)

-- ps-src : (S : pshape) → obj (ps S)
-- ps-src n = fromℕ n

-- ps-tgt : (S : pshape) → obj (ps S)
-- ps-tgt S = Fin.zero

--- TODO: the following would be in theory a much nicer way to define ps

-- Extend a context by a shape with given starting 0-cell
ps-from : pshape → (Γ : ctx) → obj Γ → ctx
ps-from zero Γ A = Γ
ps-from (suc S) Γ A = ps-from S (add1 (add0 Γ) (Pred.wk0ap A , B)) B
  where
  B = last0 Γ

-- Convert a shape to an actual context
ps : pshape → ctx
ps S = ps-from S ctx-pt (last0 ctx-empty)

ps-src-from : (S : pshape) (Γ : ctx) (A : obj Γ) (Z : obj Γ) → obj (ps-from S Γ A)
ps-src-from zero Γ A Z = Z
ps-src-from (suc S) Γ A Z = ps-src-from S (add1 (add0 Γ) (Pred.wk0ap A , _)) _ (Pred.wk0ap Z)

ps-src : (S : pshape) → obj (ps S)
ps-src S = ps-src-from S ctx-pt _ zero

ps-tgt-from : (S : pshape) (Γ : ctx) (A : obj Γ) → obj (ps-from S Γ A)
ps-tgt-from zero Γ A = A
ps-tgt-from (suc S) Γ A = ps-tgt-from S _ _

ps-tgt : (S : pshape) → obj (ps S)
ps-tgt S = ps-tgt-from S ctx-pt _

ps-hom : (S : pshape) → type (fst (ps S))
ps-hom S = ps-src S , ps-tgt S

-- A term is either a variable or an unbiased composition of terms
data term where
  var : {Γ : ctx} (v : vars Γ) → term Γ (List.lookup (snd Γ) v)
  coh : {Γ : ctx} (S : pshape) (σ : sub Γ (ps S)) → 1cell Γ (Pred.sub-ap (fst σ) (ps-src S)) (Pred.sub-ap (fst σ) (ps-tgt S))

last1 Γ A = var (Fin.fromℕ< {m = 0} (s≤s z≤n))

wk1 (Γ' , []) A = tt
wk1 (Γ' , x ∷ Γ) A = {!var {Γ = Γ' , x ∷ Γ} (suc zero)!} , {!wk1 (Γ' , Γ) A!}

sub1-ap σ (var v) = sub1-lookup σ v
sub1-ap {σ' = σ'} σ (coh S (τ' , τ)) = subst₂ (1cell _) (sym (Pred.sub-comp-ap σ' τ' (ps-src S))) (sym (Pred.sub-comp-ap σ' τ' (ps-tgt S))) (coh S (sub-comp (σ' , σ) (τ' , τ)))

id : {Γ : ctx} {A : obj Γ} → 1cell Γ A A
id {A = A} = coh 0 (A ∷ [] , tt)

co : {Γ : ctx} {A B C : obj Γ} (a : 1cell Γ A B) (b : 1cell Γ B C) → 1cell Γ A C
co {Γ} {A} {B} {C} a b = coh 2 (C ∷ B ∷ A ∷ [] , b , a , tt)

-- -- subst-tgt : {Γ : ctx} {A B B' : obj Γ} → B ≡ B' → 1cell Γ A B → 1cell Γ A B'
-- -- subst-tgt {Γ = Γ} {A = A} p = subst (1cell Γ A) p
