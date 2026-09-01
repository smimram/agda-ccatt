------------------------------------------------------------------------
-- Adjunctions between categories, in the unit-counit formulation: two
-- natural transformations subject to the two triangle identities. Since
-- L ∘F Id is not definitionally L (the functoriality proofs differ), the
-- triangle identities are stated componentwise rather than by whiskering
-- in the functor category.
--
-- An adjoint equivalence is then an adjunction whose unit and counit are
-- invertible (Equivalence, at the end of the file).
--
-- This is the 1-categorical warm-up for Biadjunction: the transposition
-- ⌊_⌋/⌈_⌉ derived below is what becomes the lifting ⇑₁ of a biuniversal
-- arrow, and ⌈⌊⌋⌉/⌊⌈⌉⌋ what becomes ε/η.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import adjunction.Adjunction as Adj
--   open Adj using (Adjunction)
--
-- so that "open Adjunction A" unambiguously refers to the record module.

module adjunction.Adjunction where

open import Level using (Level; _⊔_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

import Category as Cat
open Cat using (Category)
import Functor as Fun
open Fun using (Functor; Id; _∘F_)
import adjunction.NaturalTransformation as NatTrans
open NatTrans using (NaturalTransformation; [_,_]; _≅N_; ≅N-pointwise)

private
  variable
    o ℓ e o' ℓ' e' : Level

record Adjunction {C : Category o ℓ e} {D : Category o' ℓ' e'}
       (L : Functor C D) (R : Functor D C) :
       Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') where

  private module C = Category C
  private module D = Category D
  private module L = Functor L
  private module R = Functor R
  private module CR {A B : C.Obj} = SetoidReasoning (C.hom-setoid A B)
  private module DR {A B : D.Obj} = SetoidReasoning (D.hom-setoid A B)

  ----------------------------------------------------------------------
  -- The unit and the counit
  ----------------------------------------------------------------------

  field
    unit   : NaturalTransformation Id (R ∘F L)
    counit : NaturalTransformation (L ∘F R) Id

  private module u = NaturalTransformation unit
  private module c = NaturalTransformation counit

  -- their components, with the composites in the types unfolded
  η : (A : C.Obj) → A C.⇒ R.F₀ (L.F₀ A)
  η = u.η

  ε : (B : D.Obj) → L.F₀ (R.F₀ B) D.⇒ B
  ε = c.η

  -- their naturality, likewise
  η-natural : {A B : C.Obj} (f : A C.⇒ B) →
              η B C.∘ f C.≈ R.F₁ (L.F₁ f) C.∘ η A
  η-natural = u.natural

  ε-natural : {A B : D.Obj} (f : A D.⇒ B) →
              ε B D.∘ L.F₁ (R.F₁ f) D.≈ f D.∘ ε A
  ε-natural = c.natural

  ----------------------------------------------------------------------
  -- The triangle identities
  ----------------------------------------------------------------------

  field
    -- the zig-zag law for L: ε L ∘ L η = id
    triangleˡ : (A : C.Obj) → ε (L.F₀ A) D.∘ L.F₁ (η A) D.≈ D.id
    -- the zig-zag law for R: R ε ∘ η R = id
    triangleʳ : (B : D.Obj) → R.F₁ (ε B) C.∘ η (R.F₀ B) C.≈ C.id

  ----------------------------------------------------------------------
  -- Transposition
  ----------------------------------------------------------------------

  -- the two adjuncts of a morphism: ⌊_⌋ transposes across the adjunction
  -- towards C, and ⌈_⌉ towards D
  ⌊_⌋ : {A : C.Obj} {B : D.Obj} → L.F₀ A D.⇒ B → A C.⇒ R.F₀ B
  ⌊_⌋ {A} f = R.F₁ f C.∘ η A

  ⌈_⌉ : {A : C.Obj} {B : D.Obj} → A C.⇒ R.F₀ B → L.F₀ A D.⇒ B
  ⌈_⌉ {B = B} g = ε B D.∘ L.F₁ g

  ⌊⌋-cong : {A : C.Obj} {B : D.Obj} {f f' : L.F₀ A D.⇒ B} →
            f D.≈ f' → ⌊ f ⌋ C.≈ ⌊ f' ⌋
  ⌊⌋-cong p = C.∘-congˡ (R.F-cong p)

  ⌈⌉-cong : {A : C.Obj} {B : D.Obj} {g g' : A C.⇒ R.F₀ B} →
            g C.≈ g' → ⌈ g ⌉ D.≈ ⌈ g' ⌉
  ⌈⌉-cong p = D.∘-congʳ (L.F-cong p)

  -- the unit and the counit are the transposes of the identities
  ⌊⌋-id : {A : C.Obj} → ⌊ D.id {L.F₀ A} ⌋ C.≈ η A
  ⌊⌋-id = C.≈-trans (C.∘-congˡ R.F-id) C.identityˡ

  ⌈⌉-id : {B : D.Obj} → ⌈ C.id {R.F₀ B} ⌉ D.≈ ε B
  ⌈⌉-id = D.≈-trans (D.∘-congʳ L.F-id) D.identityʳ

  ----------------------------------------------------------------------
  -- Transposition is a natural bijection
  ----------------------------------------------------------------------

  ⌈⌊⌋⌉ : {A : C.Obj} {B : D.Obj} (f : L.F₀ A D.⇒ B) → ⌈ ⌊ f ⌋ ⌉ D.≈ f
  ⌈⌊⌋⌉ {A} {B} f = begin
    ε B D.∘ L.F₁ (R.F₁ f C.∘ η A)          ≈⟨ D.∘-congʳ (L.F-∘ (R.F₁ f) (η A)) ⟩
    ε B D.∘ (L.F₁ (R.F₁ f) D.∘ L.F₁ (η A)) ≈⟨ D.assoc' ⟩
    (ε B D.∘ L.F₁ (R.F₁ f)) D.∘ L.F₁ (η A) ≈⟨ D.∘-congˡ (ε-natural f) ⟩
    (f D.∘ ε (L.F₀ A)) D.∘ L.F₁ (η A)      ≈⟨ D.assoc ⟩
    f D.∘ (ε (L.F₀ A) D.∘ L.F₁ (η A))      ≈⟨ D.∘-congʳ (triangleˡ A) ⟩
    f D.∘ D.id                             ≈⟨ D.identityʳ ⟩
    f                                      ∎
    where open DR

  ⌊⌈⌉⌋ : {A : C.Obj} {B : D.Obj} (g : A C.⇒ R.F₀ B) → ⌊ ⌈ g ⌉ ⌋ C.≈ g
  ⌊⌈⌉⌋ {A} {B} g = begin
    R.F₁ (ε B D.∘ L.F₁ g) C.∘ η A          ≈⟨ C.∘-congˡ (R.F-∘ (ε B) (L.F₁ g)) ⟩
    (R.F₁ (ε B) C.∘ R.F₁ (L.F₁ g)) C.∘ η A ≈⟨ C.assoc ⟩
    R.F₁ (ε B) C.∘ (R.F₁ (L.F₁ g) C.∘ η A) ≈⟨ C.∘-congʳ (C.≈-sym (η-natural g)) ⟩
    R.F₁ (ε B) C.∘ (η (R.F₀ B) C.∘ g)      ≈⟨ C.assoc' ⟩
    (R.F₁ (ε B) C.∘ η (R.F₀ B)) C.∘ g      ≈⟨ C.∘-congˡ (triangleʳ B) ⟩
    C.id C.∘ g                             ≈⟨ C.identityˡ ⟩
    g                                      ∎
    where open CR

  -- so each adjunct is the unique morphism with the expected transpose
  ⌈⌉-unique : {A : C.Obj} {B : D.Obj} (g : A C.⇒ R.F₀ B) (f : L.F₀ A D.⇒ B) →
              ⌊ f ⌋ C.≈ g → f D.≈ ⌈ g ⌉
  ⌈⌉-unique g f p = D.≈-trans (D.≈-sym (⌈⌊⌋⌉ f)) (⌈⌉-cong p)

  ⌊⌋-unique : {A : C.Obj} {B : D.Obj} (f : L.F₀ A D.⇒ B) (g : A C.⇒ R.F₀ B) →
              ⌈ g ⌉ D.≈ f → g C.≈ ⌊ f ⌋
  ⌊⌋-unique f g p = C.≈-trans (C.≈-sym (⌊⌈⌉⌋ g)) (⌊⌋-cong p)

  -- naturality of the transposition, in the target (ˡ) and in the source
  -- (ʳ) of the morphism being transposed
  ⌊⌋-naturalˡ : {A : C.Obj} {B B' : D.Obj} (k : B D.⇒ B') (f : L.F₀ A D.⇒ B) →
                ⌊ k D.∘ f ⌋ C.≈ R.F₁ k C.∘ ⌊ f ⌋
  ⌊⌋-naturalˡ k f = C.≈-trans (C.∘-congˡ (R.F-∘ k f)) C.assoc

  ⌊⌋-naturalʳ : {A A' : C.Obj} {B : D.Obj} (f : L.F₀ A D.⇒ B) (h : A' C.⇒ A) →
                ⌊ f D.∘ L.F₁ h ⌋ C.≈ ⌊ f ⌋ C.∘ h
  ⌊⌋-naturalʳ {A} {A'} {B} f h = begin
    R.F₁ (f D.∘ L.F₁ h) C.∘ η A'           ≈⟨ C.∘-congˡ (R.F-∘ f (L.F₁ h)) ⟩
    (R.F₁ f C.∘ R.F₁ (L.F₁ h)) C.∘ η A'    ≈⟨ C.assoc ⟩
    R.F₁ f C.∘ (R.F₁ (L.F₁ h) C.∘ η A')    ≈⟨ C.∘-congʳ (C.≈-sym (η-natural h)) ⟩
    R.F₁ f C.∘ (η A C.∘ h)                 ≈⟨ C.assoc' ⟩
    (R.F₁ f C.∘ η A) C.∘ h                 ∎
    where open CR

  ⌈⌉-naturalˡ : {A : C.Obj} {B B' : D.Obj} (k : B D.⇒ B') (g : A C.⇒ R.F₀ B) →
                ⌈ R.F₁ k C.∘ g ⌉ D.≈ k D.∘ ⌈ g ⌉
  ⌈⌉-naturalˡ {A} {B} {B'} k g = begin
    ε B' D.∘ L.F₁ (R.F₁ k C.∘ g)           ≈⟨ D.∘-congʳ (L.F-∘ (R.F₁ k) g) ⟩
    ε B' D.∘ (L.F₁ (R.F₁ k) D.∘ L.F₁ g)    ≈⟨ D.assoc' ⟩
    (ε B' D.∘ L.F₁ (R.F₁ k)) D.∘ L.F₁ g    ≈⟨ D.∘-congˡ (ε-natural k) ⟩
    (k D.∘ ε B) D.∘ L.F₁ g                 ≈⟨ D.assoc ⟩
    k D.∘ (ε B D.∘ L.F₁ g)                 ∎
    where open DR

  ⌈⌉-naturalʳ : {A A' : C.Obj} {B : D.Obj} (g : A C.⇒ R.F₀ B) (h : A' C.⇒ A) →
                ⌈ g C.∘ h ⌉ D.≈ ⌈ g ⌉ D.∘ L.F₁ h
  ⌈⌉-naturalʳ g h = D.≈-trans (D.∘-congʳ (L.F-∘ g h)) D.assoc'

------------------------------------------------------------------------
-- Notation
------------------------------------------------------------------------

infix 4 _⊣_

_⊣_ : {C : Category o ℓ e} {D : Category o' ℓ' e'} →
      Functor C D → Functor D C → Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e')
L ⊣ R = Adjunction L R

------------------------------------------------------------------------
-- Adjoint equivalences
------------------------------------------------------------------------

-- An equivalence is an adjunction whose unit and counit are natural
-- isomorphisms. Since the two transformations are already at hand, this
-- is stated as their invertibility in the functor categories [ C , C ]
-- and [ D , D ], which is what Category.agda recommends: the equations
-- are then equalities of natural transformations, and invertibility of
-- the components is a consequence (η-invertible/ε-invertible below)
-- rather than the definition.
record Equivalence {C : Category o ℓ e} {D : Category o' ℓ' e'}
       (L : Functor C D) (R : Functor D C) :
       Set (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') where

  private module C = Category C
  private module D = Category D
  private module L = Functor L
  private module R = Functor R
  private module [C,C] = Category [ C , C ]
  private module [D,D] = Category [ D , D ]

  field
    adjunction : L ⊣ R

  -- an equivalence is in particular an adjunction, so η, ε, ⌊_⌋, ⌈_⌉ and
  -- their laws are available here without further qualification
  open Adjunction adjunction public

  field
    unit-invertible   : [C,C].Invertible unit
    counit-invertible : [D,D].Invertible counit

  ----------------------------------------------------------------------
  -- The unit and the counit as natural isomorphisms
  ----------------------------------------------------------------------

  unit-iso : Id ≅N (R ∘F L)
  unit-iso = [C,C].≅-invertible unit-invertible

  counit-iso : (L ∘F R) ≅N Id
  counit-iso = [D,D].≅-invertible counit-invertible

  -- the inverse natural transformations
  unit⁻¹ : NaturalTransformation (R ∘F L) Id
  unit⁻¹ = [C,C].inv unit-invertible

  counit⁻¹ : NaturalTransformation Id (L ∘F R)
  counit⁻¹ = [D,D].inv counit-invertible

  private module u⁻¹ = NaturalTransformation unit⁻¹
  private module c⁻¹ = NaturalTransformation counit⁻¹

  ----------------------------------------------------------------------
  -- Consequences on the components
  ----------------------------------------------------------------------

  -- the components of the inverses, with the composites in the types
  -- unfolded, as for η and ε in Adjunction
  η⁻¹ : (A : C.Obj) → R.F₀ (L.F₀ A) C.⇒ A
  η⁻¹ = u⁻¹.η

  ε⁻¹ : (B : D.Obj) → B D.⇒ L.F₀ (R.F₀ B)
  ε⁻¹ = c⁻¹.η

  -- naturality read through the inverses is nothing but the naturality
  -- of the inverse transformations
  η-natural⇐ : {A B : C.Obj} (f : A C.⇒ B) →
               η⁻¹ B C.∘ R.F₁ (L.F₁ f) C.≈ f C.∘ η⁻¹ A
  η-natural⇐ = u⁻¹.natural

  ε-natural⇐ : {A B : D.Obj} (f : A D.⇒ B) →
               ε⁻¹ B D.∘ f D.≈ L.F₁ (R.F₁ f) D.∘ ε⁻¹ A
  ε-natural⇐ = c⁻¹.natural

  -- a natural isomorphism is in particular a pointwise one
  η-invertible : (A : C.Obj) → C.Invertible (η A)
  η-invertible = ≅N-pointwise unit-iso

  ε-invertible : (B : D.Obj) → D.Invertible (ε B)
  ε-invertible = ≅N-pointwise counit-iso

------------------------------------------------------------------------
-- The identity adjunction and equivalence
------------------------------------------------------------------------

-- as for Id in Bifunctor.agda, this is the sanity check that the
-- orientations of the unit, the counit and the two triangles agree
Id⊣Id : {C : Category o ℓ e} → Id {C = C} ⊣ Id {C = C}
Id⊣Id {C = C} = record
  { unit      = record
      { η       = λ A → C.id
      ; natural = λ f → C.≈-trans C.identityˡ (C.≈-sym C.identityʳ)
      }
  ; counit    = record
      { η       = λ A → C.id
      ; natural = λ f → C.≈-trans C.identityˡ (C.≈-sym C.identityʳ)
      }
  ; triangleˡ = λ A → C.identityˡ
  ; triangleʳ = λ B → C.identityˡ
  }
  where module C = Category C

-- the inverses being again the identity, only the (definitionally equal)
-- types of the four transformations at play differ
Id≃Id : {C : Category o ℓ e} → Equivalence (Id {C = C}) (Id {C = C})
Id≃Id {C = C} = record
  { adjunction        = Id⊣Id
  ; unit-invertible   = [C,C].mkInv unit⁻¹   (λ A → C.identityˡ) (λ A → C.identityˡ)
  ; counit-invertible = [C,C].mkInv counit⁻¹ (λ A → C.identityˡ) (λ A → C.identityˡ)
  }
  where
    module C = Category C
    module [C,C] = Category [ C , C ]

    unit⁻¹ : NaturalTransformation (Id ∘F Id) (Id {C = C})
    unit⁻¹ = record
      { η       = λ A → C.id
      ; natural = λ f → C.≈-trans C.identityˡ (C.≈-sym C.identityʳ)
      }

    counit⁻¹ : NaturalTransformation (Id {C = C}) (Id ∘F Id)
    counit⁻¹ = record
      { η       = λ A → C.id
      ; natural = λ f → C.≈-trans C.identityˡ (C.≈-sym C.identityʳ)
      }
