-- {-# OPTIONS --allow-unsolved-metas #-}

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

-- A 1-substitution with given underlying 0-substitutiton: this is an inductive
-- datatype (and not a nested tuple computed from the context) so that the
-- 1-cells it contains are structural subterms, which is what makes the
-- recursions of sub-comp-ap' / sub-comp-assoc / sub1-comp-assoc and their
-- identity counterparts pass the termination checker
data sub1 (Δ : ctx) : (Γ : ctx) → Pred.sub (fst Δ) (fst Γ) → Type

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

-- Image of a variable under a substitution (defined below, since it matches
-- on the substitution)
sub1-lookup : {Δ Γ : ctx} {σ' : Pred.sub (fst Δ) (fst Γ)} (σ : sub1 Δ Γ σ') (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd))

-- A 1-substitution is determined by the images of the variables (defined below)
sub1-mk : {Δ Γ : ctx} (σ' : Pred.sub (fst Δ) (fst Γ))
          (f : (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd)))
        → sub1 Δ Γ σ'

-- The variables of a substitution built from the images of the variables are
-- the expected ones
sub1-lookup-mk : {Δ Γ : ctx} (σ' : Pred.sub (fst Δ) (fst Γ))
                 (f : (i : vars Γ) → term Δ (Pred.sub-ap σ' (lookup (snd Γ) i .fst) , Pred.sub-ap σ' (lookup (snd Γ) i .snd)))
                 (i : vars Γ) → sub1-lookup {Γ = Γ} (sub1-mk σ' f) i ≡ f i

sub1-ap : {Δ Γ : ctx} {σ' : Pred.sub (fst Δ) (fst Γ)} (σ : sub1 Δ Γ σ') {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap σ' A) (Pred.sub-ap σ' B)

-- Composite substiutition (defined below)
sub1-comp : {Γ₁ Γ₂ Γ₃ : ctx}
            {σ' : Pred.sub (ctx-pred Γ₁) (ctx-pred Γ₂)}
            {τ' : Pred.sub (ctx-pred Γ₂) (ctx-pred Γ₃)} →
            sub1 Γ₁ Γ₂ σ' → sub1 Γ₂ Γ₃ τ' → sub1 Γ₁ Γ₃ (Pred.sub-comp σ' τ')

sub : ctx → ctx → Type
sub Δ Γ = Σ (Pred.sub (ctx-pred Δ) (ctx-pred Γ)) (sub1 Δ Γ)

sub-pred : {Δ Γ : ctx} → sub Δ Γ → Pred.sub (ctx-pred Δ) (ctx-pred Γ)
sub-pred = fst

-- Apply a substitution
sub-ap : {Δ Γ : ctx} (σ : sub Δ Γ) {A B : obj Γ} → 1cell Γ A B → 1cell Δ (Pred.sub-ap (fst σ) A) (Pred.sub-ap (fst σ) B)
sub-ap σ a = sub1-ap (σ .snd) a

-- Apply a substitution to a type: this is the type of the image of a term of
-- the given type
sub-ap-type : {Δ Γ : ctx} (σ : sub Δ Γ) → type (ctx-pred Γ) → type (ctx-pred Δ)
sub-ap-type σ X = Pred.sub-ap (fst σ) (fst X) , Pred.sub-ap (fst σ) (snd X)

-- Compose substitutions
sub-comp : {Γ'' Γ' Γ : ctx} (τ : sub Γ'' Γ') (σ : sub Γ' Γ) → sub Γ'' Γ
sub-comp τ σ = Pred.sub-comp (fst τ) (fst σ) , sub1-comp (τ .snd) (σ .snd)

-- Identity substitution (defined below, since it requires the terms)
sub1-id : (Γ : ctx) → sub1 Γ Γ (Pred.sub-id (ctx-pred Γ))

-- Identity substitution
sub-id : (Γ : ctx) → sub Γ Γ
sub-id Γ = (Pred.sub-id (ctx-pred Γ)) , sub1-id Γ

-- The identity substitution does not change types
sub-id-type : (Γ : ctx) (X : type (ctx-pred Γ)) → sub-ap-type (sub-id Γ) X ≡ X
sub-id-type Γ X = cong₂ _,_ (Pred.sub-id-ap (ctx-pred Γ) (fst X)) (Pred.sub-id-ap (ctx-pred Γ) (snd X))

-- Composition of substitutions acts on types by composing the actions
sub-comp-type : {Γ₁ Γ₂ Γ₃ : ctx} (σ : sub Γ₁ Γ₂) (τ : sub Γ₂ Γ₃) (X : type (ctx-pred Γ₃))
              → sub-ap-type σ (sub-ap-type τ X) ≡ sub-ap-type (sub-comp σ τ) X
sub-comp-type σ τ X =
  cong₂ _,_ (Pred.sub-comp-ap (fst σ) (fst τ) (fst X)) (Pred.sub-comp-ap (fst σ) (fst τ) (snd X))

-- Inclusion of prop substitutions
sub-inc : {Γ' Γ : Pred.ctx} (σ : Pred.sub Γ' Γ) → sub (ctx-inc Γ') (ctx-inc Γ)

-- Extending a substitution by a 0-cell does not change the image of the other 0-variables
sub-ap-add0 : {Δ Γ : Pred.ctx} (σ' : Pred.sub Δ Γ) (z : Pred.term Δ) (x : Pred.term Γ)
            → Pred.sub-ap (z ∷ σ') (Pred.wk0ap x) ≡ Pred.sub-ap σ' x
sub-ap-add0 σ' z x = cong (Pred.sub-ap (z ∷ σ')) (Pred.wk0-ap x)

-- Extend a substitution by the image of a new 0-cell: the 1-cells are the old
-- ones, whose type has to be transported along the above
sub-add0-1 : {Θ : ctx} (Δ : ctx) {σ' : Pred.sub (fst Θ) (fst Δ)} (σ : sub1 Θ Δ σ') (z : obj Θ) → sub1 Θ (add0 Δ) (z ∷ σ')

sub-add0 : {Θ Δ : ctx} (σ : sub Θ Δ) (z : obj Θ) → sub Θ (add0 Δ)
sub-add0 {Δ = Δ} σ z = z ∷ fst σ , sub-add0-1 Δ (snd σ) z

-- Extend a substitution by the image of a new 1-cell (the 0-part is unchanged)
sub-add1 : {Θ Δ : ctx} (σ : sub Θ Δ) {X : type (fst Δ)}
           (a : 1cell Θ (Pred.sub-ap (fst σ) (fst X)) (Pred.sub-ap (fst σ) (snd X)))
         → sub Θ (add1 Δ X)

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

-- A 1-substitution is a list of 1-cells, one for each 1-variable of the context
infixr 5 _∷_
data sub1 Δ where
  []  : {Γ' : Pred.ctx} {σ' : Pred.sub (fst Δ) Γ'} → sub1 Δ (Γ' , []) σ'
  _∷_ : {Γ' : Pred.ctx} {X : type Γ'} {Γ : List (type Γ')} {σ' : Pred.sub (fst Δ) Γ'}
        (a : 1cell Δ (Pred.sub-ap σ' (fst X)) (Pred.sub-ap σ' (snd X)))
        (σ : sub1 Δ (Γ' , Γ) σ') → sub1 Δ (Γ' , X ∷ Γ) σ'

-- The operations on 1-substitutions can only be defined here, since they have
-- to match on (or produce) the constructors of sub1

sub1-lookup (a ∷ σ) zero = a
sub1-lookup (a ∷ σ) (suc i) = sub1-lookup σ i

sub1-mk {Γ = Γ' , []} σ' f = []
sub1-mk {Γ = Γ' , A ∷ Γ} σ' f = f zero ∷ sub1-mk {Γ = Γ' , Γ} σ' (f ∘ suc)

sub1-lookup-mk {Γ = Γ' , A ∷ Γ} σ' f zero = refl
sub1-lookup-mk {Γ = Γ' , A ∷ Γ} σ' f (suc i) = sub1-lookup-mk {Γ = Γ' , Γ} σ' (f ∘ suc) i

sub1-comp σ [] = []
sub1-comp {Γ₁ = Γ₁} {Γ₃ = Γ₃' , (A , B) ∷ Γ₃} {σ'} {τ'} σ (a ∷ τ) = subst₂ (1cell Γ₁) (Pred.sub-comp-ap σ' τ' A) (Pred.sub-comp-ap σ' τ' B) (sub1-ap σ a) ∷ sub1-comp σ τ

sub-inc σ = σ , []

sub-add0-1 (Δ' , []) [] z = []
sub-add0-1 {Θ} (Δ' , (A , B) ∷ Δ) {σ'} (a ∷ σ) z =
  subst₂ (1cell Θ) (sym (sub-ap-add0 σ' z A)) (sym (sub-ap-add0 σ' z B)) a ∷
  sub-add0-1 (Δ' , Δ) σ z

sub-add1 σ a = fst σ , a ∷ snd σ

last1 Γ A = var (Fin.fromℕ< {m = 0} (s≤s z≤n))

-- Weakening sends a variable to the corresponding variable of the extended context
wk0-1 Γ = sub1-mk Pred.wk0 λ v →
  let (v' , e) = map-lookup (wk0-type {fst Γ}) (snd Γ) v in
  subst (term (add0 Γ)) e (var v')

-- The identity substitution sends a variable to itself
sub1-id Γ = sub1-mk (Pred.sub-id (ctx-pred Γ)) λ v →
  subst₂ (λ x y → term Γ (x , y))
         (sym (Pred.sub-id-ap (ctx-pred Γ) (lookup (snd Γ) v .fst)))
         (sym (Pred.sub-id-ap (ctx-pred Γ) (lookup (snd Γ) v .snd)))
         (var v)

wk1 Γ A = sub1-mk (Pred.sub-id (fst Γ)) λ v →
  subst₂ (λ x y → term (add1 Γ A) (x , y))
         (sym (Pred.sub-id-ap (fst Γ) (lookup (snd Γ) v .fst)))
         (sym (Pred.sub-id-ap (fst Γ) (lookup (snd Γ) v .snd)))
         (var {Γ = add1 Γ A} (suc v))

sub1-ap σ (var v) = sub1-lookup σ v
sub1-ap {σ' = σ'} σ (coh S (τ' , τ)) = subst₂ (1cell _) (sym (Pred.sub-comp-ap σ' τ' (ps-src S))) (sym (Pred.sub-comp-ap σ' τ' (ps-tgt S))) (coh S (sub-comp (σ' , σ) (τ' , τ)))

-- Identity 1-cell
id : {Γ : ctx} {A : obj Γ} → 1cell Γ A A
id {A = A} = coh 0 (A ∷ [] , [])

-- Composition of 1-cells
co : {Γ : ctx} {A B C : obj Γ} (a : 1cell Γ A B) (b : 1cell Γ B C) → 1cell Γ A C
co {Γ} {A} {B} {C} a b = coh 2 (C ∷ B ∷ A ∷ [] , b ∷ a ∷ [])

--- Functoriality of substitution

-- A term together with its type: stating equalities between terms of a priori
-- different types is much more convenient there than transporting all the time
term' : ctx → Type
term' Γ = Σ (type (ctx-pred Γ)) (term Γ)

-- Two terms of a priori different types are equal when one transports to the
-- other (any proof of the equality of the types will do since we have K)
term'-≡ : {Γ : ctx} {X Y : type (ctx-pred Γ)} {a : term Γ X} {b : term Γ Y} (p : X ≡ Y)
        → _≡_ {A = term' Γ} (X , a) (Y , b) → subst (term Γ) p a ≡ b
term'-≡ {Γ} {a = a} p refl = cong (λ q → subst (term Γ) q a) (uip p refl)

-- Transporting a term does not change it
subst₂-term' : {Γ : ctx} {A A' B B' : obj Γ} (p : A ≡ A') (q : B ≡ B') (a : 1cell Γ A B)
             → _≡_ {A = term' Γ} ((A' , B') , subst₂ (1cell Γ) p q a) ((A , B) , a)
subst₂-term' refl refl a = refl

-- Transporting the empty substitution does not change it
subst-[] : {Δ : ctx} {Γ' : Pred.ctx} {σ' τ' : Pred.sub (ctx-pred Δ) Γ'} (p : σ' ≡ τ')
         → subst (sub1 Δ (Γ' , [])) p [] ≡ []
subst-[] refl = refl

-- Transporting a substitution along an equality of the underlying
-- 0-substitutions amounts to transporting its components
subst-∷ : {Δ : ctx} {Γ' : Pred.ctx} {X : type Γ'} {Γ : List (type Γ')}
          {σ' τ' : Pred.sub (ctx-pred Δ) Γ'} (p : σ' ≡ τ')
          (a : 1cell Δ (Pred.sub-ap σ' (fst X)) (Pred.sub-ap σ' (snd X)))
          (σ : sub1 Δ (Γ' , Γ) σ')
        → subst (sub1 Δ (Γ' , X ∷ Γ)) p (a ∷ σ)
          ≡ subst (λ ρ → 1cell Δ (Pred.sub-ap ρ (fst X)) (Pred.sub-ap ρ (snd X))) p a
            ∷ subst (sub1 Δ (Γ' , Γ)) p σ
subst-∷ refl a σ = refl

-- Applying a substitution to a term with its type
sub-ap' : {Δ Γ : ctx} (σ : sub Δ Γ) → term' Γ → term' Δ
sub-ap' σ (X , a) = sub-ap-type σ X , sub-ap σ a

-- The image of a coherence is the coherence over the composed substitution
sub-ap-coh' : {Δ Γ : ctx} (σ : sub Δ Γ) (S : pshape) (θ : sub Γ (ps S))
            → sub-ap' σ (sub-ap-type θ (ps-hom S) , coh S θ) ≡ (sub-ap-type (sub-comp σ θ) (ps-hom S) , coh S (sub-comp σ θ))
sub-ap-coh' σ S θ = subst₂-term' _ _ _

-- The image of a variable under a composite substitution
sub1-lookup-comp' : {Γ₁ Γ₂ Γ₃ : ctx} (σ : sub Γ₁ Γ₂) {τ' : Pred.sub (ctx-pred Γ₂) (ctx-pred Γ₃)}
                    (τ : sub1 Γ₂ Γ₃ τ') (v : vars Γ₃)
                  → sub-ap' σ (_ , sub1-lookup τ v) ≡ (_ , sub1-lookup (sub1-comp (snd σ) τ) v)
sub1-lookup-comp' σ (a ∷ τ) zero = sym (subst₂-term' _ _ _)
sub1-lookup-comp' σ (a ∷ τ) (suc v) = sub1-lookup-comp' σ τ v

-- Applying a composite substitution amounts to applying the substitutions in turn
-- (the type of the term is a separate implicit argument, so that the argument
-- carrying the recursion is the term itself)
sub-comp-ap' : {Γ₁ Γ₂ Γ₃ : ctx} (σ : sub Γ₁ Γ₂) (τ : sub Γ₂ Γ₃) {X : type (ctx-pred Γ₃)} (a : term Γ₃ X)
             → sub-ap' σ (sub-ap' τ (X , a)) ≡ sub-ap' (sub-comp σ τ) (X , a)

-- Composition of substitutions is associative
sub-comp-assoc : {Γ₁ Γ₂ Γ₃ Γ₄ : ctx} (σ : sub Γ₁ Γ₂) (τ : sub Γ₂ Γ₃) (θ : sub Γ₃ Γ₄)
               → sub-comp (sub-comp σ τ) θ ≡ sub-comp σ (sub-comp τ θ)

sub1-comp-assoc : {Γ₁ Γ₂ Γ₃ Γ₄ : ctx} (σ : sub Γ₁ Γ₂) (τ : sub Γ₂ Γ₃)
                  {θ' : Pred.sub (ctx-pred Γ₃) (ctx-pred Γ₄)} (θ : sub1 Γ₃ Γ₄ θ')
                → subst (sub1 Γ₁ Γ₄) (Pred.sub-comp-assoc (fst σ) (fst τ) θ')
                        (sub1-comp (sub1-comp (snd σ) (snd τ)) θ)
                  ≡ sub1-comp (snd σ) (sub1-comp (snd τ) θ)

sub-comp-ap' σ τ (var v) = sub1-lookup-comp' σ (snd τ) v
sub-comp-ap' σ τ {X} (coh S θ) =
  begin
    sub-ap' σ (sub-ap' τ (X , coh S θ))
  ≡⟨ cong (sub-ap' σ) (sub-ap-coh' τ S θ) ⟩
    sub-ap' σ (_ , coh S (sub-comp τ θ))
  ≡⟨ sub-ap-coh' σ S (sub-comp τ θ) ⟩
    (_ , coh S (sub-comp σ (sub-comp τ θ)))
  ≡⟨ cong (λ ρ → sub-ap-type ρ (ps-hom S) , coh S ρ) (sym (sub-comp-assoc σ τ θ)) ⟩
    (_ , coh S (sub-comp (sub-comp σ τ) θ))
  ≡⟨ sym (sub-ap-coh' (sub-comp σ τ) S θ) ⟩
    sub-ap' (sub-comp σ τ) (X , coh S θ)
  ∎

sub-comp-assoc σ τ θ = Σ-≡ (Pred.sub-comp-assoc (fst σ) (fst τ) (fst θ)) (sub1-comp-assoc σ τ (snd θ))

sub1-comp-assoc σ τ {θ'} [] = subst-[] (Pred.sub-comp-assoc (fst σ) (fst τ) θ')
sub1-comp-assoc {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} σ τ {θ'} (_∷_ {Γ' = Γ₄'} {X = X} {Γ = Γ₄} a θ) =
  begin
    subst (sub1 Γ₁ (Γ₄' , X ∷ Γ₄)) p (hd ∷ tl)
  ≡⟨ subst-∷ p hd tl ⟩
    (subst (term Γ₁ ∘ typ) p hd ∷ subst (sub1 Γ₁ (Γ₄' , Γ₄)) p tl)
  ≡⟨ cong₂ _∷_ first (sub1-comp-assoc σ τ θ) ⟩
    (rhs-hd ∷ sub1-comp (snd σ) (sub1-comp (snd τ) θ))
  ∎
  where
  -- the associativity of the underlying 0-substitutions
  p : Pred.sub-comp (Pred.sub-comp (fst σ) (fst τ)) θ'
    ≡ Pred.sub-comp (fst σ) (Pred.sub-comp (fst τ) θ')
  p = Pred.sub-comp-assoc (fst σ) (fst τ) θ'
  -- the type of the last variable, as a function of the 0-substitution
  typ : Pred.sub (ctx-pred Γ₁) Γ₄' → type (ctx-pred Γ₁)
  typ ρ = Pred.sub-ap ρ (fst X) , Pred.sub-ap ρ (snd X)
  -- the type of the last 1-cell, and its type in Γ₂ once τ and θ are composed
  Xθ : type (ctx-pred Γ₃)
  Xθ = Pred.sub-ap θ' (fst X) , Pred.sub-ap θ' (snd X)
  Xτθ : type (ctx-pred Γ₂)
  Xτθ = Pred.sub-ap (Pred.sub-comp (fst τ) θ') (fst X) , Pred.sub-ap (Pred.sub-comp (fst τ) θ') (snd X)
  -- the two composites: (σ∘τ)∘θ on the left, σ∘(τ∘θ) on the right
  hd = subst₂ (1cell Γ₁) (Pred.sub-comp-ap (Pred.sub-comp (fst σ) (fst τ)) θ' (fst X))
                         (Pred.sub-comp-ap (Pred.sub-comp (fst σ) (fst τ)) θ' (snd X))
                         (sub-ap (sub-comp σ τ) a)
  tl = sub1-comp (sub1-comp (snd σ) (snd τ)) θ
  mid = subst₂ (1cell Γ₂) (Pred.sub-comp-ap (fst τ) θ' (fst X))
                          (Pred.sub-comp-ap (fst τ) θ' (snd X))
                          (sub-ap τ a)
  rhs-hd = subst₂ (1cell Γ₁) (Pred.sub-comp-ap (fst σ) (Pred.sub-comp (fst τ) θ') (fst X))
                             (Pred.sub-comp-ap (fst σ) (Pred.sub-comp (fst τ) θ') (snd X))
                             (sub-ap σ mid)
  -- the two images of the last 1-cell agree, as terms with their types
  img : _≡_ {A = term' Γ₁} (typ (Pred.sub-comp (Pred.sub-comp (fst σ) (fst τ)) θ') , hd)
                           (typ (Pred.sub-comp (fst σ) (Pred.sub-comp (fst τ) θ')) , rhs-hd)
  img =
    begin
      (typ (Pred.sub-comp (Pred.sub-comp (fst σ) (fst τ)) θ') , hd)
    ≡⟨ subst₂-term' (Pred.sub-comp-ap (Pred.sub-comp (fst σ) (fst τ)) θ' (fst X))
                    (Pred.sub-comp-ap (Pred.sub-comp (fst σ) (fst τ)) θ' (snd X))
                    (sub-ap (sub-comp σ τ) a) ⟩
      sub-ap' (sub-comp σ τ) (Xθ , a)
    ≡⟨ sym (sub-comp-ap' σ τ a) ⟩
      sub-ap' σ (sub-ap' τ (Xθ , a))
    ≡⟨ cong (sub-ap' σ) (sym (subst₂-term' (Pred.sub-comp-ap (fst τ) θ' (fst X))
                                           (Pred.sub-comp-ap (fst τ) θ' (snd X))
                                           (sub-ap τ a))) ⟩
      sub-ap' σ (Xτθ , mid)
    ≡⟨ sym (subst₂-term' (Pred.sub-comp-ap (fst σ) (Pred.sub-comp (fst τ) θ') (fst X))
                         (Pred.sub-comp-ap (fst σ) (Pred.sub-comp (fst τ) θ') (snd X))
                         (sub-ap σ mid)) ⟩
      (typ (Pred.sub-comp (fst σ) (Pred.sub-comp (fst τ) θ')) , rhs-hd)
    ∎
  -- the image of the last 1-variable
  first : subst (term Γ₁ ∘ typ) p hd ≡ rhs-hd
  first =
    begin
      subst (term Γ₁ ∘ typ) p hd
    ≡⟨ subst-∘ {P = term Γ₁} {f = typ} p ⟩
      subst (term Γ₁) (cong typ p) hd
    ≡⟨ term'-≡ (cong typ p) img ⟩
      rhs-hd
    ∎

-- Applying the identity substitution does not change a term
sub-id-ap' : (Γ : ctx) {X : type (ctx-pred Γ)} (a : term Γ X) → sub-ap' (sub-id Γ) (X , a) ≡ (X , a)

-- The identity substitution is a left unit for composition
sub-comp-id : {Δ Γ : ctx} (σ : sub Δ Γ) → sub-comp (sub-id Δ) σ ≡ σ

sub1-comp-id : {Δ Γ : ctx} {σ' : Pred.sub (ctx-pred Δ) (ctx-pred Γ)} (σ : sub1 Δ Γ σ')
             → subst (sub1 Δ Γ) (Pred.sub-comp-id σ') (sub1-comp (sub1-id Δ) σ) ≡ σ

sub-id-ap' Γ {X} (var v) =
  trans
    (cong (λ a → sub-ap-type (sub-id Γ) X , a)
          (sub1-lookup-mk {Δ = Γ} {Γ = Γ} (Pred.sub-id (ctx-pred Γ))
                          (λ i → subst₂ (λ x y → term Γ (x , y))
                                        (sym (Pred.sub-id-ap (ctx-pred Γ) (lookup (snd Γ) i .fst)))
                                        (sym (Pred.sub-id-ap (ctx-pred Γ) (lookup (snd Γ) i .snd)))
                                        (var i))
                          v))
    (subst₂-term' (sym (Pred.sub-id-ap (ctx-pred Γ) (fst X)))
                  (sym (Pred.sub-id-ap (ctx-pred Γ) (snd X)))
                  (var v))
sub-id-ap' Γ (coh S θ) =
  trans
    (sub-ap-coh' (sub-id Γ) S θ)
    (cong (λ ρ → sub-ap-type ρ (ps-hom S) , coh S ρ) (sub-comp-id θ))

sub-comp-id σ = Σ-≡ (Pred.sub-comp-id (fst σ)) (sub1-comp-id (snd σ))

sub1-comp-id {σ' = σ'} [] = subst-[] (Pred.sub-comp-id σ')
sub1-comp-id {Δ} {σ' = σ'} (_∷_ {Γ' = Γ'} {X = X} {Γ = Γ} a σ) =
  begin
    subst (sub1 Δ (Γ' , X ∷ Γ)) p (hd ∷ tl)
  ≡⟨ subst-∷ p hd tl ⟩
    (subst (term Δ ∘ typ) p hd ∷ subst (sub1 Δ (Γ' , Γ)) p tl)
  ≡⟨ cong₂ _∷_ first (sub1-comp-id σ) ⟩
    (a ∷ σ)
  ∎
  where
  -- the unitality of the underlying 0-substitutions
  p : Pred.sub-comp (Pred.sub-id (ctx-pred Δ)) σ' ≡ σ'
  p = Pred.sub-comp-id σ'
  -- the type of the last variable, as a function of the 0-substitution
  typ : Pred.sub (ctx-pred Δ) Γ' → type (ctx-pred Δ)
  typ ρ = Pred.sub-ap ρ (fst X) , Pred.sub-ap ρ (snd X)
  -- the composite of the identity with σ
  hd = subst₂ (1cell Δ) (Pred.sub-comp-ap (Pred.sub-id (ctx-pred Δ)) σ' (fst X))
                        (Pred.sub-comp-ap (Pred.sub-id (ctx-pred Δ)) σ' (snd X))
                        (sub-ap (sub-id Δ) a)
  tl = sub1-comp (sub1-id Δ) σ
  -- the identity does not change the last 1-cell, as a term with its type
  img : _≡_ {A = term' Δ} (typ (Pred.sub-comp (Pred.sub-id (ctx-pred Δ)) σ') , hd) (typ σ' , a)
  img =
    begin
      (typ (Pred.sub-comp (Pred.sub-id (ctx-pred Δ)) σ') , hd)
    ≡⟨ subst₂-term' (Pred.sub-comp-ap (Pred.sub-id (ctx-pred Δ)) σ' (fst X))
                    (Pred.sub-comp-ap (Pred.sub-id (ctx-pred Δ)) σ' (snd X))
                    (sub-ap (sub-id Δ) a) ⟩
      sub-ap' (sub-id Δ) (typ σ' , a)
    ≡⟨ sub-id-ap' Δ a ⟩
      (typ σ' , a)
    ∎
  -- the image of the last 1-variable
  first : subst (term Δ ∘ typ) p hd ≡ a
  first =
    begin
      subst (term Δ ∘ typ) p hd
    ≡⟨ subst-∘ {P = term Δ} {f = typ} p ⟩
      subst (term Δ) (cong typ p) hd
    ≡⟨ term'-≡ (cong typ p) img ⟩
      a
    ∎

--- The above, in transported form

-- Applying a composite substitution amounts to applying the substitutions in turn
sub-comp-ap : {Γ₁ Γ₂ Γ₃ : ctx} (σ : sub Γ₁ Γ₂) (τ : sub Γ₂ Γ₃) {X : type (ctx-pred Γ₃)} (a : term Γ₃ X)
            → subst (term Γ₁) (sub-comp-type σ τ X) (sub-ap σ (sub-ap τ a)) ≡ sub-ap (sub-comp σ τ) a
sub-comp-ap σ τ a = term'-≡ _ (sub-comp-ap' σ τ a)

-- Applying the identity substitution does not change a term
sub-id-ap : (Γ : ctx) {X : type (ctx-pred Γ)} (a : term Γ X)
          → subst (term Γ) (sub-id-type Γ X) (sub-ap (sub-id Γ) a) ≡ a
sub-id-ap Γ a = term'-≡ _ (sub-id-ap' Γ a)
