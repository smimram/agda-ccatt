{-# OPTIONS --allow-unsolved-metas #-}

--- Type theoretical definition of incoherent unbiased categories / sets

module USet where

open import Prelude
open import Data.Product as Product
open import Data.List as List
open import Data.Fin as Fin

import Prop as Pred

-- A type in a Prop-context is an arrow xᵢ→yᵢ
type : (Γ : Pred.ctx) → Type
type Γ = Pred.term Γ × Pred.term Γ

type-src : {Γ : Pred.ctx} → type Γ → Pred.term Γ
type-src = fst

type-tgt : {Γ : Pred.ctx} → type Γ → Pred.term Γ
type-tgt = snd

-- A type weakened by adding a 0-variable
wk0-type : {Γ : Pred.ctx} → type Γ → type (Pred.add0 Γ)
wk0-type A = Product.map Pred.wk0ap Pred.wk0ap A

-- A context
ctx : Type
ctx = Σ Pred.ctx (List ∘ type)

-- Inderlying prop context
ctx-pred : ctx → Pred.ctx
ctx-pred = fst

-- Inclusion of a prop context
ctx-inc : Pred.ctx → ctx
ctx-inc Γ = Γ , []

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

-- A 1-substitution is determined by the images of the variables
sub1-mk : {Δ Γ : ctx} (σ' : Pred.sub (fst Δ) (fst Γ))
          (f : (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd)))
        → sub1 Δ Γ σ'
sub1-mk {Γ = Γ' , []} σ' f = tt
sub1-mk {Γ = Γ' , A ∷ Γ} σ' f = f zero , sub1-mk {Γ = Γ' , Γ} σ' (f ∘ suc)

sub1-ap : {Δ Γ : ctx} {σ' : Pred.sub (fst Δ) (fst Γ)} (σ : sub1 Δ Γ σ') {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap σ' A) (Pred.sub-ap σ' B)

-- Composite substiutition
sub1-comp : {Γ₁ Γ₂ Γ₃ : ctx}
            {σ' : Pred.sub (ctx-pred Γ₁) (ctx-pred Γ₂)}
            {τ' : Pred.sub (ctx-pred Γ₂) (ctx-pred Γ₃)} →
            sub1 Γ₁ Γ₂ σ' → sub1 Γ₂ Γ₃ τ' → sub1 Γ₁ Γ₃ (Pred.sub-comp σ' τ')
sub1-comp {Γ₃ = Γ₃' , []} σ tt = tt
sub1-comp {Γ₁ = Γ₁} {Γ₃ = Γ₃' , (A , B) ∷ Γ₃} {σ'} {τ'} σ (a , τ) = subst₂ (1cell Γ₁) (Pred.sub-comp-ap σ' τ' A) (Pred.sub-comp-ap σ' τ' B) (sub1-ap σ a) , (sub1-comp σ τ)

sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (ctx-pred Δ) (ctx-pred Γ)) (sub1 Δ Γ)

sub-pred : {Δ Γ : ctx} → sub Δ Γ → Pred.sub (ctx-pred Δ) (ctx-pred Γ)
sub-pred = fst

-- Apply a substitution
sub-ap : {Δ Γ : ctx} (σ : sub Δ Γ) {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap (fst σ) A) (Pred.sub-ap (fst σ) B)
sub-ap σ a = sub1-ap (σ .snd) a

-- Compose substitutions
sub-comp : {Γ'' Γ' Γ : ctx} (τ : sub Γ'' Γ') (σ : sub Γ' Γ) → sub Γ'' Γ
sub-comp τ σ = Pred.sub-comp (fst τ) (fst σ) , sub1-comp (τ .snd) (σ .snd)

sub1-id : (Γ : ctx) → sub1 Γ Γ (Pred.sub-id (ctx-pred Γ))
sub1-id (Γ , []) = tt
sub1-id (Γ , A ∷ Δ) = {!!} , {!!}

-- Identity substitution
sub-id : (Γ : ctx) → sub Γ Γ
sub-id Γ = (Pred.sub-id (ctx-pred Γ)) , sub1-id Γ

-- Inclusion of prop substitutions
sub-inc : {Γ' Γ : Pred.ctx} (σ : Pred.sub Γ' Γ) → sub (ctx-inc Γ') (ctx-inc Γ)
sub-inc σ = σ , tt

-- Extending a substitution by a 0-cell does not change the image of the other
-- 0-variables
sub-ap-add0 : {Δ Γ : Pred.ctx} (σ' : Pred.sub Δ Γ) (z : Pred.term Δ) (x : Pred.term Γ)
            → Pred.sub-ap (z ∷ σ') (Pred.wk0ap x) ≡ Pred.sub-ap σ' x
sub-ap-add0 σ' z x = cong (Pred.sub-ap (z ∷ σ')) (Pred.wk0-ap x)

-- Extend a substitution by the image of a new 0-cell: the 1-cells are the old
-- ones, whose type has to be transported along the above
sub-add0-1 : {Θ : ctx} (Δ : ctx) {σ' : Pred.sub (fst Θ) (fst Δ)} (σ : sub1 Θ Δ σ') (z : obj Θ) → sub1 Θ (add0 Δ) (z ∷ σ')
sub-add0-1 (Δ' , []) σ z = tt
sub-add0-1 {Θ} (Δ' , (A , B) ∷ Δ) {σ'} (a , σ) z =
  subst₂ (1cell Θ) (sym (sub-ap-add0 σ' z A)) (sym (sub-ap-add0 σ' z B)) a ,
  sub-add0-1 (Δ' , Δ) σ z

sub-add0 : {Θ Δ : ctx} (σ : sub Θ Δ) (z : obj Θ) → sub Θ (add0 Δ)
sub-add0 {Δ = Δ} σ z = z ∷ fst σ , sub-add0-1 Δ (snd σ) z

-- Extend a substitution by the image of a new 1-cell (the 0-part is unchanged)
sub-add1 : {Θ Δ : ctx} (σ : sub Θ Δ) {X : type (fst Δ)}
           (a : 1cell Θ (Pred.sub-ap (fst σ) (fst X)) (Pred.sub-ap (fst σ) (snd X)))
         → sub Θ (add1 Δ X)
sub-add1 σ a = fst σ , a , snd σ

-- Substitution corresponding to weakening a 1-variable (defined below, since it
-- requires the terms)
wk1 : (Γ : ctx) (A : type (fst Γ)) → sub1 (add1 Γ A) Γ (Pred.sub-id (fst Γ))

wk1' : {Γ : ctx} (A : type (fst Γ)) → sub (add1 Γ A) Γ
wk1' {Γ} A = Pred.sub-id (fst Γ) , wk1 Γ A

wk1ap : {Γ : ctx} {X : type (fst Γ)} (A : type (fst Γ)) → term Γ X → term (add1 Γ A) X
wk1ap {Γ} {X} A a = subst₂ (λ x y → term (add1 Γ A) (x , y)) (Pred.sub-id-ap (fst Γ) (fst X)) (Pred.sub-id-ap (fst Γ) (snd X)) (sub-ap (wk1' A) a)

-- Substitution corresponding to weakening a 0-variable (defined below, since it
-- requires the terms)
wk0-1 : (Γ : ctx) → sub1 (add0 Γ) Γ Pred.wk0

wk0 : {Γ : ctx} → sub (add0 Γ) Γ
wk0 {Γ} = Pred.wk0 , wk0-1 Γ

-- The shape of a pasting scheme is the number of arrows we compose
pshape : Type
pshape = ℕ

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

-- Weakening sends a variable to the corresponding variable of the extended context
wk0-1 Γ = sub1-mk Pred.wk0 λ v →
  let (v' , e) = map-lookup (wk0-type {fst Γ}) (snd Γ) v in
  subst (term (add0 Γ)) e (var v')

wk1 Γ A = sub1-mk (Pred.sub-id (fst Γ)) λ v →
  subst₂ (λ x y → term (add1 Γ A) (x , y))
         (sym (Pred.sub-id-ap (fst Γ) (lookup (snd Γ) v .fst)))
         (sym (Pred.sub-id-ap (fst Γ) (lookup (snd Γ) v .snd)))
         (var {Γ = add1 Γ A} (suc v))

sub1-ap σ (var v) = sub1-lookup σ v
sub1-ap {σ' = σ'} σ (coh S (τ' , τ)) = subst₂ (1cell _) (sym (Pred.sub-comp-ap σ' τ' (ps-src S))) (sym (Pred.sub-comp-ap σ' τ' (ps-tgt S))) (coh S (sub-comp (σ' , σ) (τ' , τ)))

-- Identity 1-cell
id : {Γ : ctx} {A : obj Γ} → 1cell Γ A A
id {A = A} = coh 0 (A ∷ [] , tt)

-- Composition of 1-cells
co : {Γ : ctx} {A B C : obj Γ} (a : 1cell Γ A B) (b : 1cell Γ B C) → 1cell Γ A C
co {Γ} {A} {B} {C} a b = coh 2 (C ∷ B ∷ A ∷ [] , b , a , tt)
