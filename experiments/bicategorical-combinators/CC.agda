--- Cartesian closed categories
--- see for instance Lambek and Scott p.52

open import Prelude
open import Ty
open import PS
-- open import CCBase public

infixr 6 _·_

data Tm {n : ℕ} (Γ : Con n) : Arr n → Type where
  var  : {A : Arr n} → A ∈ Γ → Tm Γ A
  id   : {A : Ty n} → Tm Γ (A , A)
  _·_  : {A B C : Ty n} → Tm Γ (A , B) → Tm Γ (B , C) → Tm Γ (A , C)
  term : {A : Ty n} → Tm Γ (A , 𝟙)
  pa : {X A B : Ty n} → Tm Γ (X , A) → Tm Γ (X , B) → Tm Γ (X , A × B)
  fst  : {A B : Ty n} → Tm Γ (A × B , A)
  snd  : {A B : Ty n} → Tm Γ (A × B , B)
  abs  : {A B C : Ty n} → Tm Γ (A × B , C) → Tm Γ (A , B ↝ C)
  app  : {A B : Ty n} → Tm Γ ((A ↝ B) × A , B)

infixr 5 _⇒_

data _⇒_ {n : ℕ} {Γ : Con n} : {A : Arr n} → Tm Γ A → Tm Γ A → Type where
  --- products
  pa-fst : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pa f g · fst ⇒ f
  pa-snd : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → pa f g · snd ⇒ g
  pa-eta : {A B C : Ty n} (f : Tm Γ (A , B × C)) → f ⇒ pa (f · fst) (f · snd)
  pa-fst' : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → f ⇒ pa f g · fst
  pa-snd' : {X A B : Ty n} (f : Tm Γ (X , A)) (g : Tm Γ (X , B)) → g ⇒ pa f g · snd
  pa-eta' : {A B C : Ty n} (f : Tm Γ (A , B × C)) → pa (f · fst) (f · snd) ⇒ f
  pa2 : {X A B : Ty n} {f f' : Tm Γ (X , A)} {g g' : Tm Γ (X , B)} → f ⇒ f' → g ⇒ g' → pa f g ⇒ pa f' g'
  --- terminal
  term-can : {A : Ty n} (f : Tm Γ (A , 𝟙)) → f ⇒ term
  term-can' : {A : Ty n} (f : Tm Γ (A , 𝟙)) → term ⇒ f
  --- closure
  eps : {A B C : Ty n} (f : Tm Γ (A × B , C)) → pa (fst · abs f) snd · app ⇒ f
  eta : {A B C : Ty n} (f : Tm Γ (A , B ↝ C)) → f ⇒ abs (pa (fst · f) snd · app)
  eps' : {A B C : Ty n} (f : Tm Γ (A × B , C)) → f ⇒ pa (fst · abs f) snd · app
  eta' : {A B C : Ty n} (f : Tm Γ (A , B ↝ C)) → abs (pa (fst · f) snd · app) ⇒ f
  abs2 : {A B C : Ty n} {f f' : Tm Γ (A × B , C)} → f ⇒ f' → abs f ⇒ abs f'
  --- (bi)category
  unitl : {A B : Ty n} (f : Tm Γ (A , B)) → id · f ⇒ f
  unitr : {A B : Ty n} (f : Tm Γ (A , B)) → f · id ⇒ f
  assoc : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → (f · g) · h ⇒ f · (g · h)
  unitl' : {A B : Ty n} (f : Tm Γ (A , B)) → f ⇒ id · f
  unitr' : {A B : Ty n} (f : Tm Γ (A , B)) → f ⇒ f · id
  assoc' : {A B C D : Ty n} (f : Tm Γ (A , B)) (g : Tm Γ (B , C)) (h : Tm Γ (C , D)) → f · (g · h) ⇒ (f · g) · h
  id2 : {A : Arr n} {f : Tm Γ A} → f ⇒ f
  co2 : {A : Arr n} {f g h : Tm Γ A} → f ⇒ g → g ⇒ h → f ⇒ h
  whiskl : {A B C : Ty n} (f : Tm Γ (A , B)) {g g' : Tm Γ (B , C)} (α : g ⇒ g') → f · g ⇒ f · g'
  whiskr : {A B C : Ty n} {f f' : Tm Γ (A , B)} (α : f ⇒ f') (g : Tm Γ (B , C)) → f · g ⇒ f' · g

term2 : {n : ℕ} {Γ : Con n} {A : Ty n} (f g : Tm Γ (A , 𝟙)) → f ⇒ g
term2 f g = co2 (term-can f) (term-can' g)

data _∼_ {n : ℕ} {Γ : Con n} : {A B : Ty n} {t u : Tm Γ (A , B)} (α β : t ⇒ u) → Type where
  -- finite prodcuts
  term-can2 : {A : Ty n} {f g : Tm Γ (A , 𝟙)} (α : f ⇒ g) → α ∼ term2 f g
  pa2-eta : {A B C : Ty n} {f g : Tm Γ (A , B × C)} (α : f ⇒ g) → co2 α (pa-eta g) ∼ co2 (pa-eta f) (pa2 (whiskr α fst) (whiskr α snd))
  pa2-fst : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (A , C)} (α : f ⇒ f') (β : g ⇒ g') → co2 (whiskr (pa2 α β) fst) (pa-fst f' g') ∼ (co2 (pa-fst f g) α)
  pa2-snd : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (A , C)} (α : f ⇒ f') (β : g ⇒ g') → co2 (whiskr (pa2 α β) snd) (pa-snd f' g') ∼ (co2 (pa-snd f g) β)
  ∼pa : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (A , C)} {α α' : f ⇒ f'} {β β' : g ⇒ g'} → α ∼ α' → β ∼ β' → pa2 α β ∼ pa2 α' β'
  -- closure
  eta-eps : {A B C : Ty n} (f : Tm Γ (A , B ↝ C)) → co2 (whiskr (pa2 (whiskl fst (eta f)) id2) app) (eps (pa (fst · f) snd · app)) ∼ id2
  eta-nat : {A B C : Ty n} {f g : Tm Γ (A × B , C)} (α : f ⇒ g) → co2 (eps f) α ∼ co2 (whiskr (pa2 (whiskl fst (abs2 α)) id2) app) (eps g)
  eps-nat : {A B C : Ty n} {f g : Tm Γ (A , B ↝ C)} (α : f ⇒ g) → co2 (eta f) (abs2 (whiskr (pa2 (whiskl fst α) id2) app)) ∼ co2 α (eta g)
  -- (bi)category
  ∼refl : {A : Arr n} {f g : Tm Γ A} (α : f ⇒ g) → α ∼ α
  ∼sym : {A : Arr n} {f g : Tm Γ A} {α β : f ⇒ g} → α ∼ β → β ∼ α
  ∼trans : {A : Arr n} {f g : Tm Γ A} {α β γ : f ⇒ g} → α ∼ β → β ∼ γ → α ∼ γ

-- Some derived laws
module _ {n : ℕ} {Γ : Con n} where
  infixr 6 _⇒·_
  _⇒·_ :  {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (B , C)} → f ⇒ f' → g ⇒ g' → f · g ⇒ f' · g'
  _⇒·_ α β = co2 (whiskr α _) (whiskl _ β)

  co2³ : {A : Arr n} {f1 f2 f3 f4 : Tm Γ A} → f1 ⇒ f2 → f2 ⇒ f3 → f3 ⇒ f4 → f1 ⇒ f4
  co2³ α β γ = co2 α (co2 β γ)

  pa2-fst' : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (A , C)} (α : f ⇒ f') (β : g ⇒ g') → co2³ (pa-fst' f g) (whiskr (pa2 α β) fst) (pa-fst f' g') ∼ α
  pa2-fst' = {!!} -- derived from pa2-fst and inverse laws

  pa2-snd' : {A B C : Ty n} {f f' : Tm Γ (A , B)} {g g' : Tm Γ (A , C)} (α : f ⇒ f') (β : g ⇒ g') → co2³ (pa-snd' f g) (whiskr (pa2 α β) snd) (pa-snd f' g') ∼ β
  pa2-snd' = {!!} -- derived from pa2-snd and inverse laws

  -- coh eta-eps  {a b c : .} (f : a → b ⇒ c) : co21 (F2 b (eta f)) app = eps' (co1 (F1 b f) app)
  -- eta-eps'

-- Substitutions
Sub : {n n' : ℕ} (τ : SubTy n n') (Γ : Con n) (Γ' : Con n') → Type
Sub _ Γ ε = Unit
Sub τ Γ (Γ' ▹ (A , B)) = Sub τ Γ Γ' ∧ Tm Γ (A [ τ ]' , B [ τ ]')

-- Terminal substitution
SubTerm : {n : ℕ} (Γ : Con n) → Sub (SubTyId n) Γ ε
SubTerm Γ = tt

-- Application of a substitution
_[_] : {n : ℕ} {Γ : Con n} {n' : ℕ} {Γ' : Con n'} {A B : Ty n'} → Tm Γ' (A , B) → {τ : SubTy n n'} (σ : Sub τ Γ Γ') → Tm Γ (A [ τ ]' , B [ τ ]')
var here [ σ , t ] = t
var (drop x) [ σ , t ] = var x [ σ ]
id [ σ ] = id
(f · g) [ σ ] = f [ σ ] · g [ σ ]
term [ σ ] = term
pa f g [ σ ] = pa (f [ σ ]) (g [ σ ])
fst [ σ ] = fst
snd [ σ ] = snd
abs t [ σ ] = abs (t [ σ ])
app [ σ ] = app

-- Equivalence of substitutions
_⇒Sub_ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ σ' : Sub τ Γ Γ') → Type
_⇒Sub_ {Γ' = ε} tt tt = Unit
_⇒Sub_ {Γ' = Γ' ▹ A} (σ , t) (σ' , t') = (σ ⇒Sub σ') ∧ (t ⇒ t')

⇒SubRefl : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} (σ : Sub τ Γ Γ') → σ ⇒Sub σ
⇒SubRefl {Γ' = ε} σ = tt
⇒SubRefl {Γ' = Γ' ▹ A} (σ , t) = ⇒SubRefl σ , id2

-- ⇒SubSym : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ⇒Sub σ' → σ' ⇒Sub σ
-- ⇒SubSym {Γ' = ε} tt = tt
-- ⇒SubSym {Γ' = Γ' ▹ A} (p , q) = ⇒SubSym p , ⇒sym q

-- Applying equivalent substitutions to a term gives equivalent results
-- (recursion on the term, so that _[_]⇒ below can recurse on the proof)
[]⇒ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} (t : Tm Γ' A) {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → σ ⇒Sub σ' → t [ σ ] ⇒ t [ σ' ]
[]⇒ (var here) (σ , p) = p
[]⇒ (var (drop x)) (σ , p) = []⇒ (var x) σ
[]⇒ id p = id2
[]⇒ (f · g) p = _⇒·_ ([]⇒ f p) ([]⇒ g p)
[]⇒ term p = id2
[]⇒ (pa f g) p = pa2 ([]⇒ f p) ([]⇒ g p)
[]⇒ fst p = id2
[]⇒ snd p = id2
[]⇒ (abs t) p = abs2 ([]⇒ t p)
[]⇒ app p = id2

_[_]⇒ : {n n' : ℕ} {Γ : Con n} {Γ' : Con n'} {A : Arr n'} {t u : Tm Γ' A} {τ : SubTy n n'} {σ σ' : Sub τ Γ Γ'} → t ⇒ u → σ ⇒Sub σ' → t [ σ ] ⇒ u [ σ' ]
pa-fst f g [ q ]⇒ = co2 (pa-fst (f [ _ ]) (g [ _ ])) ([]⇒ f q)
pa-snd f g [ q ]⇒ = co2 (pa-snd (f [ _ ]) (g [ _ ])) ([]⇒ g q)
pa-eta f [ q ]⇒ = co2 ([]⇒ f q) (pa-eta (f [ _ ]))
pa-fst' f g [ q ]⇒ = co2 ([]⇒ f q) (pa-fst' (f [ _ ]) (g [ _ ]))
pa-snd' f g [ q ]⇒ = co2 ([]⇒ g q) (pa-snd' (f [ _ ]) (g [ _ ]))
pa-eta' f [ q ]⇒ = co2 (pa-eta' (f [ _ ])) ([]⇒ f q)
pa2 α β [ q ]⇒ = pa2 (α [ q ]⇒) (β [ q ]⇒)
term-can f [ q ]⇒ = term-can (f [ _ ])
term-can' f [ q ]⇒ = term-can' (f [ _ ])
eps f [ q ]⇒ = co2 (eps (f [ _ ])) ([]⇒ f q)
eta f [ q ]⇒ = co2 ([]⇒ f q) (eta (f [ _ ]))
eps' f [ q ]⇒ = co2 ([]⇒ f q) (eps' (f [ _ ]))
eta' f [ q ]⇒ = co2 (eta' (f [ _ ])) ([]⇒ f q)
unitl f [ q ]⇒ = co2 (unitl (f [ _ ])) ([]⇒ f q)
unitr f [ q ]⇒ = co2 (unitr (f [ _ ])) ([]⇒ f q)
assoc f g h [ q ]⇒ = co2 (assoc (f [ _ ]) (g [ _ ]) (h [ _ ])) (_⇒·_ ([]⇒ f q) (_⇒·_ ([]⇒ g q) ([]⇒ h q)))
unitl' f [ q ]⇒ = co2 ([]⇒ f q) (unitl' (f [ _ ]))
unitr' f [ q ]⇒ = co2 ([]⇒ f q) (unitr' (f [ _ ]))
assoc' f g h [ q ]⇒ = co2 (_⇒·_ ([]⇒ f q) (_⇒·_ ([]⇒ g q) ([]⇒ h q))) (assoc' (f [ _ ]) (g [ _ ]) (h [ _ ]))
abs2 p [ q ]⇒ = abs2 (p [ q ]⇒)
id2 {f = f} [ q ]⇒ = []⇒ f q
co2 p p' [ q ]⇒ = co2 (p [ q ]⇒) (p' [ ⇒SubRefl _ ]⇒)
whiskl f α [ q ]⇒ = _⇒·_ ([]⇒ f q) (α [ q ]⇒)
whiskr α f [ q ]⇒ = _⇒·_ (α [ q ]⇒) ([]⇒ f q)

-- Composition of substitutions
_∘_ : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {τ : SubTy n n'} {τ' : SubTy n' n''} → Sub τ' Γ' Γ'' → Sub τ Γ Γ' → Sub (τ' ∘' τ) Γ Γ''
_∘_ {Γ'' = ε} σ' σ = tt
_∘_ {Γ'' = Γ'' ▹ A} (σ' , t') σ = (σ' ∘ σ) , (t' [ σ ])

-- Functoriality of substitution application
[∘] : {n n' n'' : ℕ} {Γ : Con n} {Γ' : Con n'} {Γ'' : Con n''} {A : Arr n''} {τ : SubTy n n'} {τ' : SubTy n' n''} (t : Tm Γ'' A) (σ' : Sub τ' Γ' Γ'') (σ : Sub τ Γ Γ') → t [ σ' ] [ σ ] ≡ t [ σ' ∘ σ ]
[∘] (var here) (σ' , f) σ = refl
[∘] (var (drop x)) (σ' , f) σ = [∘] (var x) σ' σ
[∘] id σ' σ = refl
[∘] (f · g) σ' σ = cong₂ _·_ ([∘] f σ' σ) ([∘] g σ' σ)
[∘] term σ' σ = refl
[∘] (pa f g) σ' σ = cong₂ pa ([∘] f σ' σ) ([∘] g σ' σ)
[∘] fst σ' σ = refl
[∘] snd σ' σ = refl
[∘] (abs t) σ' σ = cong abs ([∘] t σ' σ)
[∘] app σ' σ = refl

---
--- Currying
---

-- Currying against the terminal source, which brings a term with source A back
-- to a term with source 𝟙
curry : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (A , B) → Tm Γ (𝟙 , A ↝ B)
curry t = abs (snd · t)

-- ... and its inverse
uncurry : {n : ℕ} {Γ : Con n} {A B : Ty n} → Tm Γ (𝟙 , A ↝ B) → Tm Γ (A , B)
uncurry t = pa (term · t) id · app

---
--- Normal forms
---

-- Bind the last variable of the context
close : {n : ℕ} {Γ : Con n} {A B C : Ty n} → Tm (Γ ▹ (𝟙 , A)) (B , C) → Tm Γ (B × A , C)
close (var here) = snd
close (var (drop x)) = fst · var x
close id = fst
close (f · g) = pa (close f) snd · close g
close term = term
close (pa f g) = pa (close f) (close g)
close fst = fst · fst
close snd = fst · snd
close (abs t) = abs (pa (pa (fst · fst) snd) (fst · snd) · close t)
close app = fst · app

-- NOTE: we could extend neutral terms to have A as source instead of 𝟙. However, the PS condition would be more difficult to formulate because we can look up stuff both in the context and in the source.

-- Canonical terms: in βη-long form
data canonical {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type
-- Neutral terms
data neutral {n : ℕ} : {Γ : Con n} {A : Ty n} (t : Tm Γ (𝟙 , A)) → Type

data canonical {n} where
  can-pa : {Γ : Con n} {A B : Ty n} {tl : Tm Γ (𝟙 , A)} {tr : Tm Γ (𝟙 , B)} → canonical tl → canonical tr → canonical {A = A × B} (pa tl tr)
  can-term : {Γ : Con n} → canonical {Γ = Γ} {A = 𝟙} term
  can-abs : {Γ : Con n} {A B : Ty n} {t : Tm (Γ ▹ (𝟙 , A)) (𝟙 , B)} → canonical t → canonical {A = A ↝ B} (abs (close t))
  can-neu : {Γ : Con n} {x : Fin n} {t : Tm Γ (𝟙 , X x)} → neutral t → canonical {A = X x} t

data neutral {n} where
  neu-var : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A)} → canonical t → (x : (A , B) ∈ Γ) → neutral (t · var x)
  neu-app : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A ↝ B)} {u : Tm Γ (𝟙 , A)} → neutral t → canonical u → neutral (pa t u · app)
  neu-fst : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · fst)
  neu-snd : {Γ : Con n} {A B : Ty n} {t : Tm Γ (𝟙 , A × B)} → neutral t → neutral (t · snd)
