------------------------------------------------------------------------
-- Natural transformations between functors (in the setoid approach):
-- the naturality squares commute up to the equality _≈_ of morphisms of
-- the target category, and two natural transformations are considered
-- equal when their components are. With that equality, the functors
-- between two categories form a category again, see [_,_] below.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import adjunction.NaturalTransformation as NatTrans
--   open NatTrans using (NaturalTransformation)
--
-- so that "open NaturalTransformation α" unambiguously refers to the
-- record module.

module adjunction.NaturalTransformation where

open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

import Category as Cat
open Cat using (Category)
import Functor as Fun
open Fun using (Functor; F₀; F₁; F-cong; F-∘; _∘F_)

private
  variable
    o ℓ e o' ℓ' e' o'' ℓ'' e'' : Level

record NaturalTransformation {C : Category o ℓ e} {D : Category o' ℓ' e'}
       (F G : Functor C D) : Set (o ⊔ ℓ ⊔ ℓ' ⊔ e') where
  eta-equality

  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G

  field
    -- the components
    η : (A : C.Obj) → F.F₀ A D.⇒ G.F₀ A
    -- naturality: the morphism is taken explicitly, since F₁ is a field
    -- and hence not injective for unification
    natural : {A B : C.Obj} (f : A C.⇒ B) →
              η B D.∘ F.F₁ f D.≈ G.F₁ f D.∘ η A

  -- the naturality square, read in the other direction
  natural' : {A B : C.Obj} (f : A C.⇒ B) →
             G.F₁ f D.∘ η A D.≈ η B D.∘ F.F₁ f
  natural' f = D.≈-sym (natural f)

open NaturalTransformation public

------------------------------------------------------------------------
-- Identity, vertical composition, and the functor category
------------------------------------------------------------------------

module _ {C : Category o ℓ e} {D : Category o' ℓ' e'} where

  private module C = Category C
  private module D = Category D
  private module DR {A B : D.Obj} = SetoidReasoning (D.hom-setoid A B)

  idN : {F : Functor C D} → NaturalTransformation F F
  idN = record
    { η       = λ A → D.id
    ; natural = λ f → D.≈-trans D.identityˡ (D.≈-sym D.identityʳ)
    }

  infixr 9 _∘N_

  _∘N_ : {F G H : Functor C D} →
         NaturalTransformation G H → NaturalTransformation F G →
         NaturalTransformation F H
  _∘N_ {F} {G} {H} β α = record
    { η       = λ A → η β A D.∘ η α A
    ; natural = λ {A} {B} f → begin
        (η β B D.∘ η α B) D.∘ F₁ F f ≈⟨ D.assoc ⟩
        η β B D.∘ (η α B D.∘ F₁ F f) ≈⟨ D.∘-congʳ (natural α f) ⟩
        η β B D.∘ (F₁ G f D.∘ η α A) ≈⟨ D.assoc' ⟩
        (η β B D.∘ F₁ G f) D.∘ η α A ≈⟨ D.∘-congˡ (natural β f) ⟩
        (F₁ H f D.∘ η β A) D.∘ η α A ≈⟨ D.assoc ⟩
        F₁ H f D.∘ (η β A D.∘ η α A) ∎
    }
    where open DR

  infix 4 _≈N_

  -- two natural transformations are equal when their components are
  _≈N_ : {F G : Functor C D} → Rel (NaturalTransformation F G) (o ⊔ e')
  α ≈N β = (A : C.Obj) → η α A D.≈ η β A

  ≈N-equiv : {F G : Functor C D} → IsEquivalence (_≈N_ {F} {G})
  ≈N-equiv = record
    { refl  = λ A → D.≈-refl
    ; sym   = λ p A → D.≈-sym (p A)
    ; trans = λ p q A → D.≈-trans (p A) (q A)
    }

-- the category of functors from C to D: all the laws hold componentwise,
-- so they are those of D
[_,_] : (C : Category o ℓ e) (D : Category o' ℓ' e') →
        Category (o ⊔ ℓ ⊔ e ⊔ o' ⊔ ℓ' ⊔ e') (o ⊔ ℓ ⊔ ℓ' ⊔ e') (o ⊔ e')
[ C , D ] = record
  { Obj       = Functor C D
  ; _⇒_       = NaturalTransformation
  ; _≈_       = _≈N_
  ; id        = idN
  ; _∘_       = _∘N_
  ; ≈-equiv   = ≈N-equiv
  ; ∘-cong    = λ p q A → D.∘-cong (p A) (q A)
  ; assoc     = λ A → D.assoc
  ; identityˡ = λ A → D.identityˡ
  ; identityʳ = λ A → D.identityʳ
  }
  where module D = Category D

------------------------------------------------------------------------
-- Whiskering and horizontal composition
------------------------------------------------------------------------

infixr 11 _◁N_
infixl 11 _▷N_
infixr 10 _∗N_

-- left whiskering: composing on the left with a functor
_◁N_ : {C : Category o ℓ e} {D : Category o' ℓ' e'} {E : Category o'' ℓ'' e''}
       (H : Functor D E) {F G : Functor C D} →
       NaturalTransformation F G → NaturalTransformation (H ∘F F) (H ∘F G)
_◁N_ {D = D} {E = E} H {F} {G} α = record
  { η       = λ A → F₁ H (η α A)
  ; natural = λ {A} {B} f →
      E.≈-trans (E.≈-sym (F-∘ H (η α B) (F₁ F f)))
      (E.≈-trans (F-cong H (natural α f))
                 (F-∘ H (F₁ G f) (η α A)))
  }
  where module E = Category E

-- right whiskering: composing on the right with a functor, which is
-- simply reindexing the components
_▷N_ : {C : Category o ℓ e} {D : Category o' ℓ' e'} {E : Category o'' ℓ'' e''}
       {F G : Functor D E} → NaturalTransformation F G → (H : Functor C D) →
       NaturalTransformation (F ∘F H) (G ∘F H)
α ▷N H = record
  { η       = λ A → η α (F₀ H A)
  ; natural = λ f → natural α (F₁ H f)
  }

-- horizontal composition, defined by whiskering on both sides
_∗N_ : {C : Category o ℓ e} {D : Category o' ℓ' e'} {E : Category o'' ℓ'' e''}
       {F F' : Functor D E} {G G' : Functor C D} →
       NaturalTransformation F F' → NaturalTransformation G G' →
       NaturalTransformation (F ∘F G) (F' ∘F G')
_∗N_ {F = F} {G' = G'} α β = (α ▷N G') ∘N (F ◁N β)

-- the two ways of composing horizontally agree: this is naturality of α
-- at the components of β
exchange : {C : Category o ℓ e} {D : Category o' ℓ' e'} {E : Category o'' ℓ'' e''}
           {F F' : Functor D E} {G G' : Functor C D}
           (α : NaturalTransformation F F') (β : NaturalTransformation G G') →
           ((α ▷N G') ∘N (F ◁N β)) ≈N ((F' ◁N β) ∘N (α ▷N G))
exchange α β A = natural α (η β A)

------------------------------------------------------------------------
-- Natural isomorphisms
------------------------------------------------------------------------

module _ {C : Category o ℓ e} {D : Category o' ℓ' e'} where

  private module C = Category C
  private module D = Category D
  private module [C,D] = Category [ C , D ]

  infix 4 _≅N_

  -- a natural isomorphism is an isomorphism in the functor category
  _≅N_ : Functor C D → Functor C D → Set (o ⊔ ℓ ⊔ ℓ' ⊔ e')
  F ≅N G = F [C,D].≅ G

  -- a natural transformation is invertible as soon as all its components
  -- are: the naturality of the inverse comes for free
  pointwise-invertible : {F G : Functor C D} (α : NaturalTransformation F G) →
                         ((A : C.Obj) → D.Invertible (η α A)) →
                         [C,D].Invertible α
  pointwise-invertible {F} {G} α i = [C,D].mkInv
    (record
      { η       = λ A → D.inv (i A)
      ; natural = λ {A} {B} f →
          D.≅-natural (D.≅-invertible (i A)) (D.≅-invertible (i B))
                      (F₁ F f) (F₁ G f) (natural' α f)
      })
    (λ A → D.invˡ (i A))
    (λ A → D.invʳ (i A))

  -- builder for a natural isomorphism
  mk≅N : {F G : Functor C D} (α : NaturalTransformation F G) →
         ((A : C.Obj) → D.Invertible (η α A)) → F ≅N G
  mk≅N α i = [C,D].≅-invertible (pointwise-invertible α i)

  -- conversely, the components of a natural isomorphism are invertible
  ≅N-pointwise : {F G : Functor C D} (i : F ≅N G) (A : C.Obj) →
                 D.Invertible (η ([C,D].to i) A)
  ≅N-pointwise i A =
    D.mkInv (η ([C,D].from i) A) ([C,D].isoˡ i A) ([C,D].isoʳ i A)
