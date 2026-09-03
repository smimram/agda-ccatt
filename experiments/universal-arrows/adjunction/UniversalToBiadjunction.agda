------------------------------------------------------------------------
-- From universal arrows to a biadjunction: a bifunctor admitting a
-- biuniversal arrow to every object has a right biadjoint, and the two
-- form a Biadjunction in the sense of adjunction.Biadjunction.
------------------------------------------------------------------------

module adjunction.UniversalToBiadjunction where

open import Level using (Level; _⊔_)

import Bicategory as Bicat
open Bicat using (Bicategory)
import Bifunctor as Bifun
open Bifun using (Bifunctor)
import Functor as Fun
open Fun using (Functor; _∘F_)
import Universal as Univ
open Univ using (Universal)
import adjunction.UniversalBiadjunction as UBiadj
open UBiadj using (UniversalBiadjunction)
import adjunction.NaturalTransformation as NatTrans
open NatTrans using (NaturalTransformation; pointwise-invertible; mk≅N; _≅N_; [_,_])
import adjunction.Adjunction as Adj
open Adj using (Adjunction; Equivalence; _⊣_)
import adjunction.Biadjunction as Biadj
open Biadj using (Biadjunction; _⊣₂_)
import adjunction.Pasting as Past
open Past using (module Pasting)

private
  variable
    o ℓ₁ ℓ₂ e o' ℓ₁' ℓ₂' e' : Level

module _ {C : Bicategory o  ℓ₁  ℓ₂  e }
         {D : Bicategory o' ℓ₁' ℓ₂' e'}
         {F : Bifunctor C D}
         (UB : UniversalBiadjunction F)
         where

  private module C = Bicategory C
  private module D = Bicategory D
  private module F = Bifunctor F
  private module D-P = Pasting D

  open UniversalBiadjunction UB

  ----------------------------------------------------------------------
  -- The calculus of ⇑₂
  ----------------------------------------------------------------------

  -- the operation 2-cells are compared through: whiskering by u after
  -- applying F. Everything below is an instance of the fact that ⇑₂ is
  -- inverse to it (⇑₂-β and ⇑₂-unique).
  w : {x : C.Obj} {y : D.Obj} {g g' : x C.⇒₁ R₀ y} → g C.⇒₂ g' →
      (u y D.∘₁ F.F₁ g) D.⇒₂ (u y D.∘₁ F.F₁ g')
  w {y = y} β = u y D.◁ F.F₂ β

  w-cong : {x : C.Obj} {y : D.Obj} {g g' : x C.⇒₁ R₀ y} {β β' : g C.⇒₂ g'} →
           β C.≈ β' → w β D.≈ w β'
  w-cong {y = y} p = D.◁-cong (u y) (F.F₂-cong p)

  w-id : {x : C.Obj} {y : D.Obj} {g : x C.⇒₁ R₀ y} →
         w (C.id₂ {f = g}) D.≈ D.id₂
  w-id {y = y} {g = g} =
    D.≈-trans (D.◁-cong (u y) F.F₂-id₂) (D.◁-id (u y) (F.F₁ g))

  w-• : {x : C.Obj} {y : D.Obj} {g g' g'' : x C.⇒₁ R₀ y}
        (β' : g' C.⇒₂ g'') (β : g C.⇒₂ g') → w (β' C.• β) D.≈ w β' D.• w β
  w-• {y = y} β' β =
    D.≈-trans (D.◁-cong (u y) (F.F₂-• β' β)) (D.◁-• (u y) (F.F₂ β') (F.F₂ β))

  -- the action of the transposition on 2-cells: this is the ⇑₂ of the
  -- algebraic formulation (Universal→UniversalHA in Universal.agda)
  Φ₂ : {x : C.Obj} {y : D.Obj} {f f' : F.F₀ x D.⇒₁ y} → f D.⇒₂ f' →
       ⇑₁ f C.⇒₂ ⇑₁ f'
  Φ₂ {f = f} γ = ⇑₂ (γ D.• ε f)

  -- precomposing a factorization with a 2-cell of C
  ⇑₂-∘ˡ : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g g' : x C.⇒₁ R₀ y}
          (α : (u y D.∘₁ F.F₁ g) D.⇒₂ f) (β : g' C.⇒₂ g) →
          ⇑₂ α C.• β C.≈ ⇑₂ (α D.• w β)
  ⇑₂-∘ˡ {y = y} {f = f} α β = ⇑₂-unique (⇑₂ α C.• β) (begin
    ε f D.• w (⇑₂ α C.• β)        ≈⟨ D.•-congʳ (w-• (⇑₂ α) β) ⟩
    ε f D.• (w (⇑₂ α) D.• w β)    ≈⟨ D.≈-sym D.•-assoc ⟩
    (ε f D.• w (⇑₂ α)) D.• w β    ≈⟨ D.•-congˡ (⇑₂-β α) ⟩
    α D.• w β                     ∎)
    where open D.⇒₂-Reasoning

  -- postcomposing it with the image of a 2-cell of D
  ⇑₂-∘ʳ : {x : C.Obj} {y : D.Obj} {f f' : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
          (γ : f D.⇒₂ f') (α : (u y D.∘₁ F.F₁ g) D.⇒₂ f) →
          Φ₂ γ C.• ⇑₂ α C.≈ ⇑₂ (γ D.• α)
  ⇑₂-∘ʳ {y = y} {f = f} {f' = f'} γ α = ⇑₂-unique (Φ₂ γ C.• ⇑₂ α) (begin
    ε f' D.• w (Φ₂ γ C.• ⇑₂ α)          ≈⟨ D.•-congʳ (w-• (Φ₂ γ) (⇑₂ α)) ⟩
    ε f' D.• (w (Φ₂ γ) D.• w (⇑₂ α))    ≈⟨ D.≈-sym D.•-assoc ⟩
    (ε f' D.• w (Φ₂ γ)) D.• w (⇑₂ α)    ≈⟨ D.•-congˡ (⇑₂-β (γ D.• ε f)) ⟩
    (γ D.• ε f) D.• w (⇑₂ α)            ≈⟨ D.•-assoc ⟩
    γ D.• (ε f D.• w (⇑₂ α))            ≈⟨ D.•-congʳ (⇑₂-β α) ⟩
    γ D.• α                             ∎)
    where open D.⇒₂-Reasoning

  -- the transposition preserves identities and composition of 2-cells
  Φ₂-id : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} →
          Φ₂ (D.id₂ {f = f}) C.≈ C.id₂
  Φ₂-id {f = f} =
    C.≈-sym (⇑₂-unique C.id₂ (D.≈-trans (D.•-congʳ w-id)
                             (D.≈-trans D.•-identityʳ (D.≈-sym D.•-identityˡ))))

  Φ₂-cong : {x : C.Obj} {y : D.Obj} {f f' : F.F₀ x D.⇒₁ y} {γ γ' : f D.⇒₂ f'} →
            γ D.≈ γ' → Φ₂ γ C.≈ Φ₂ γ'
  Φ₂-cong p = ⇑₂-cong (D.•-congˡ p)

  Φ₂-• : {x : C.Obj} {y : D.Obj} {f f' f'' : F.F₀ x D.⇒₁ y}
         (γ' : f' D.⇒₂ f'') (γ : f D.⇒₂ f') →
         Φ₂ (γ' D.• γ) C.≈ Φ₂ γ' C.• Φ₂ γ
  Φ₂-• {f = f} γ' γ =
    C.≈-sym (C.≈-trans (⇑₂-∘ʳ γ' (γ D.• ε f)) (⇑₂-cong (D.≈-sym D.•-assoc)))

  ----------------------------------------------------------------------
  -- The counit ε and the unit η, seen through w
  ----------------------------------------------------------------------

  -- the triangle identity: this is ⇑₂-β at the identity
  η-triangle : {x : C.Obj} {y : D.Obj} (g : x C.⇒₁ R₀ y) →
               ε (u y D.∘₁ F.F₁ g) D.• w (η g) D.≈ D.id₂
  η-triangle {y = y} g = ⇑₂-β (D.id₂ {f = u y D.∘₁ F.F₁ g})

  -- hence w (η g) is the inverse of ε (u ∘ F g), w preserving inverses
  w-invertible : {x : C.Obj} {y : D.Obj} {g g' : x C.⇒₁ R₀ y} {β : g C.⇒₂ g'} →
                 C.Invertible₂ β → D.Invertible₂ (w β)
  w-invertible {y = y} {β = β} i = D.Hom.mkInv (w (C.Hom.inv i))
    (D.≈-trans (D.≈-sym (w-• (C.Hom.inv i) β))
               (D.≈-trans (w-cong (C.Hom.invˡ i)) w-id))
    (D.≈-trans (D.≈-sym (w-• β (C.Hom.inv i)))
               (D.≈-trans (w-cong (C.Hom.invʳ i)) w-id))

  w-η⁻¹ : {x : C.Obj} {y : D.Obj} (g : x C.⇒₁ R₀ y) →
          w (η⁻¹ g) D.≈ ε (u y D.∘₁ F.F₁ g)
  w-η⁻¹ {y = y} g = D.Hom.∘-cancelʳ (w-invertible (η-invertible g)) (begin
    w (η⁻¹ g) D.• w (η g)   ≈⟨ D.≈-sym (w-• (η⁻¹ g) (η g)) ⟩
    w (η⁻¹ g C.• η g)       ≈⟨ w-cong (C.Hom.invˡ (η-invertible g)) ⟩
    w C.id₂                 ≈⟨ w-id ⟩
    D.id₂                   ≈⟨ D.≈-sym (η-triangle g) ⟩
    ε (u y D.∘₁ F.F₁ g) D.• w (η g) ∎)
    where open D.⇒₂-Reasoning

  -- ⇑₂ read as an equation on w: this is the rewriting rule that turns
  -- every factorization back into a 2-cell of D
  w-⇑₂ : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
         (γ : (u y D.∘₁ F.F₁ g) D.⇒₂ f) → w (⇑₂ γ) D.≈ ε⁻¹ f D.• γ
  w-⇑₂ {f = f} γ = D.Hom.∘-cancelˡ (ε-invertible f) (begin
    ε f D.• w (⇑₂ γ)        ≈⟨ ⇑₂-β γ ⟩
    γ                       ≈⟨ D.≈-sym D.•-identityˡ ⟩
    D.id₂ D.• γ             ≈⟨ D.•-congˡ (D.≈-sym (D.Hom.invʳ (ε-invertible f))) ⟩
    (ε f D.• ε⁻¹ f) D.• γ   ≈⟨ D.•-assoc ⟩
    ε f D.• (ε⁻¹ f D.• γ)   ∎)
    where open D.⇒₂-Reasoning

  -- ⇑₂ of the counit is the identity
  ⇑₂-ε : {x : C.Obj} {y : D.Obj} (f : F.F₀ x D.⇒₁ y) → ⇑₂ (ε f) C.≈ C.id₂
  ⇑₂-ε f = C.≈-sym (⇑₂-unique C.id₂
    (D.≈-trans (D.•-congʳ w-id) D.•-identityʳ))

  ----------------------------------------------------------------------
  -- w is faithful
  ----------------------------------------------------------------------

  -- the universal property makes whiskering by u after F faithful on
  -- 2-cells between 1-cells x ⇒₁ R₀ y: this is what lets every equation
  -- below be checked in D. Note that neither g nor g' has to be a ⇑₁,
  -- which is what ⇑₂-cancel would require; the unit is what bridges the
  -- gap, being invertible.
  w-faithful : {x : C.Obj} {y : D.Obj} {g g' : x C.⇒₁ R₀ y} {α β : g C.⇒₂ g'} →
               w α D.≈ w β → α C.≈ β
  w-faithful {y = y} {g' = g'} {α = α} {β = β} p =
    C.Hom.∘-cancelˡ (η-invertible g') (⇑₂-cancel (D.≈-trans (step α) (D.≈-trans p (D.≈-sym (step β)))))
    where
      open D.⇒₂-Reasoning

      -- ε • w (η g' • γ) collapses to w γ, by the triangle identity
      step : (γ : _ C.⇒₂ g') →
             ε (u y D.∘₁ F.F₁ g') D.• w (η g' C.• γ) D.≈ w γ
      step γ = begin
        ε (u y D.∘₁ F.F₁ g') D.• w (η g' C.• γ)
          ≈⟨ D.•-congʳ (w-• (η g') γ) ⟩
        ε (u y D.∘₁ F.F₁ g') D.• (w (η g') D.• w γ)
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (ε (u y D.∘₁ F.F₁ g') D.• w (η g')) D.• w γ
          ≈⟨ D.•-congˡ (η-triangle g') ⟩
        D.id₂ D.• w γ
          ≈⟨ D.•-identityˡ ⟩
        w γ ∎

  ----------------------------------------------------------------------
  -- Factorizations of invertible 2-cells are invertible
  ----------------------------------------------------------------------

  ⇑₂-invertible : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
                  {γ : (u y D.∘₁ F.F₁ g) D.⇒₂ f} →
                  D.Invertible₂ γ → C.Invertible₂ (⇑₂ γ)
  ⇑₂-invertible {y = y} {f = f} {g = g} {γ = γ} i =
    C.Hom.mkInv (η⁻¹ g C.• ⇑₂ (γ⁻¹ D.• ε f)) invˡ' invʳ'
    where
      γ⁻¹ : f D.⇒₂ (u y D.∘₁ F.F₁ g)
      γ⁻¹ = D.Hom.inv i

      -- γ⁻¹ • ε f, factored and then whiskered back, is ε f up to γ
      collapse : (γ D.• w (η⁻¹ g)) D.• w (⇑₂ (γ⁻¹ D.• ε f)) D.≈ ε f
      collapse = begin
        (γ D.• w (η⁻¹ g)) D.• w (⇑₂ (γ⁻¹ D.• ε f))
          ≈⟨ D.•-congʳ (w-⇑₂ (γ⁻¹ D.• ε f)) ⟩
        (γ D.• w (η⁻¹ g)) D.• (ε⁻¹ (u y D.∘₁ F.F₁ g) D.• (γ⁻¹ D.• ε f))
          ≈⟨ D.•-congˡ (D.•-congʳ (w-η⁻¹ g)) ⟩
        (γ D.• ε (u y D.∘₁ F.F₁ g)) D.• (ε⁻¹ (u y D.∘₁ F.F₁ g) D.• (γ⁻¹ D.• ε f))
          ≈⟨ D.•-assoc ⟩
        γ D.• (ε (u y D.∘₁ F.F₁ g) D.• (ε⁻¹ (u y D.∘₁ F.F₁ g) D.• (γ⁻¹ D.• ε f)))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        γ D.• ((ε (u y D.∘₁ F.F₁ g) D.• ε⁻¹ (u y D.∘₁ F.F₁ g)) D.• (γ⁻¹ D.• ε f))
          ≈⟨ D.•-congʳ (D.•-congˡ (D.Hom.invʳ (ε-invertible (u y D.∘₁ F.F₁ g)))) ⟩
        γ D.• (D.id₂ D.• (γ⁻¹ D.• ε f))
          ≈⟨ D.•-congʳ D.•-identityˡ ⟩
        γ D.• (γ⁻¹ D.• ε f)
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (γ D.• γ⁻¹) D.• ε f
          ≈⟨ D.•-congˡ (D.Hom.invʳ i) ⟩
        D.id₂ D.• ε f
          ≈⟨ D.•-identityˡ ⟩
        ε f ∎
        where open D.⇒₂-Reasoning

      invˡ' : (η⁻¹ g C.• ⇑₂ (γ⁻¹ D.• ε f)) C.• ⇑₂ γ C.≈ C.id₂
      invˡ' = begin
        (η⁻¹ g C.• ⇑₂ (γ⁻¹ D.• ε f)) C.• ⇑₂ γ
          ≈⟨ C.•-assoc ⟩
        η⁻¹ g C.• (⇑₂ (γ⁻¹ D.• ε f) C.• ⇑₂ γ)
          ≈⟨ C.•-congʳ (⇑₂-∘ˡ (γ⁻¹ D.• ε f) (⇑₂ γ)) ⟩
        η⁻¹ g C.• ⇑₂ ((γ⁻¹ D.• ε f) D.• w (⇑₂ γ))
          ≈⟨ C.•-congʳ (⇑₂-cong (D.≈-trans D.•-assoc
                       (D.≈-trans (D.•-congʳ (⇑₂-β γ)) (D.Hom.invˡ i)))) ⟩
        η⁻¹ g C.• η g
          ≈⟨ C.Hom.invˡ (η-invertible g) ⟩
        C.id₂ ∎
        where open C.⇒₂-Reasoning

      invʳ' : ⇑₂ γ C.• (η⁻¹ g C.• ⇑₂ (γ⁻¹ D.• ε f)) C.≈ C.id₂
      invʳ' = begin
        ⇑₂ γ C.• (η⁻¹ g C.• ⇑₂ (γ⁻¹ D.• ε f))
          ≈⟨ C.≈-sym C.•-assoc ⟩
        (⇑₂ γ C.• η⁻¹ g) C.• ⇑₂ (γ⁻¹ D.• ε f)
          ≈⟨ C.•-congˡ (⇑₂-∘ˡ γ (η⁻¹ g)) ⟩
        ⇑₂ (γ D.• w (η⁻¹ g)) C.• ⇑₂ (γ⁻¹ D.• ε f)
          ≈⟨ ⇑₂-∘ˡ (γ D.• w (η⁻¹ g)) (⇑₂ (γ⁻¹ D.• ε f)) ⟩
        ⇑₂ ((γ D.• w (η⁻¹ g)) D.• w (⇑₂ (γ⁻¹ D.• ε f)))
          ≈⟨ ⇑₂-cong collapse ⟩
        ⇑₂ (ε f)
          ≈⟨ ⇑₂-ε f ⟩
        C.id₂ ∎
        where open C.⇒₂-Reasoning

  ----------------------------------------------------------------------
  -- The transposition, as an equivalence of hom-categories
  ----------------------------------------------------------------------

  -- the unit is natural, which for the universal property is again just
  -- ⇑₂ read in two ways
  η-natural : {x : C.Obj} {y : D.Obj} {g g' : x C.⇒₁ R₀ y} (α : g C.⇒₂ g') →
              Φ₂ (w α) C.• η g C.≈ η g' C.• α
  η-natural {y = y} {g = g} {g' = g'} α = begin
    Φ₂ (w α) C.• η g       ≈⟨ ⇑₂-∘ʳ (w α) (D.id₂ {f = u y D.∘₁ F.F₁ g}) ⟩
    ⇑₂ (w α D.• D.id₂)     ≈⟨ ⇑₂-cong D.•-identityʳ ⟩
    ⇑₂ (w α)               ≈⟨ ⇑₂-cong (D.≈-sym D.•-identityˡ) ⟩
    ⇑₂ (D.id₂ D.• w α)     ≈⟨ C.≈-sym (⇑₂-∘ˡ (D.id₂ {f = u y D.∘₁ F.F₁ g'}) α) ⟩
    η g' C.• α             ∎
    where open C.⇒₂-Reasoning

  -- the transposition functor
  Φ : (x : C.Obj) (y : D.Obj) → Functor (D.hom (F.F₀ x) y) (C.hom x (R₀ y))
  Φ x y = record
    { F₀     = ⇑₁
    ; F₁     = Φ₂
    ; F-cong = Φ₂-cong
    ; F-id   = Φ₂-id
    ; F-∘    = Φ₂-•
    }

  -- and its pseudoinverse, which is honestly u ∘ F (−)
  Ψ : (x : C.Obj) (y : D.Obj) → Functor (C.hom x (R₀ y)) (D.hom (F.F₀ x) y)
  Ψ x y = record
    { F₀     = λ k → u y D.∘₁ F.F₁ k
    ; F₁     = w
    ; F-cong = w-cong
    ; F-id   = w-id
    ; F-∘    = w-•
    }

  -- the unit of the equivalence is ε⁻¹, its counit is η⁻¹
  Φ-unit : (x : C.Obj) (y : D.Obj) →
           NaturalTransformation Fun.Id (Ψ x y Fun.∘F Φ x y)
  Φ-unit x y = record
    { η       = ε⁻¹
    ; natural = λ {h} {h'} β →
        D.Hom.≅-natural (ε-iso h) (ε-iso h') (w (Φ₂ β)) β
                        (D.≈-sym (⇑₂-β (β D.• ε h)))
    }

  Φ-counit : (x : C.Obj) (y : D.Obj) →
             NaturalTransformation (Φ x y Fun.∘F Ψ x y) Fun.Id
  Φ-counit x y = record
    { η       = η⁻¹
    ; natural = λ {k} {k'} γ →
        C.Hom.≅-natural (η-iso k) (η-iso k') γ (Φ₂ (w γ)) (η-natural γ)
    }

  Φ-adjunction : (x : C.Obj) (y : D.Obj) → Φ x y ⊣ Ψ x y
  Φ-adjunction x y = record
    { unit      = Φ-unit x y
    ; counit    = Φ-counit x y
    ; triangleˡ = λ h → begin
        η⁻¹ (⇑₁ h) C.• Φ₂ (ε⁻¹ h)
          ≈⟨ C.•-congʳ (⇑₂-cong (D.Hom.invˡ (ε-invertible h))) ⟩
        η⁻¹ (⇑₁ h) C.• η (⇑₁ h)
          ≈⟨ C.Hom.invˡ (η-invertible (⇑₁ h)) ⟩
        C.id₂ ∎
    ; triangleʳ = λ k →
        D.≈-trans (D.•-congˡ (w-η⁻¹ k)) (D.Hom.invʳ (ε-invertible (u y D.∘₁ F.F₁ k)))
    }
    where open C.⇒₂-Reasoning

  Φ-equivalence : (x : C.Obj) (y : D.Obj) → Equivalence (Φ x y) (Ψ x y)
  Φ-equivalence x y = record
    { adjunction        = Φ-adjunction x y
    ; unit-invertible   =
        pointwise-invertible (Φ-unit x y) (λ h → D.Hom.inv-invertible (ε-invertible h))
    ; counit-invertible =
        pointwise-invertible (Φ-counit x y) (λ k → C.Hom.inv-invertible (η-invertible k))
    }

  ----------------------------------------------------------------------
  -- Invertibility toolkit
  ----------------------------------------------------------------------

  -- whiskering preserves invertible 2-cells, in either variable
  ◁-inv : {a b c : D.Obj} (f : b D.⇒₁ c) {g g' : a D.⇒₁ b} {β : g D.⇒₂ g'} →
          D.Invertible₂ β → D.Invertible₂ (f D.◁ β)
  ◁-inv f i = D.invertible-≅₂ (f D.◁≅ D.≅₂-invertible i)

  ▷-inv : {a b c : D.Obj} {f f' : b D.⇒₁ c} {α : f D.⇒₂ f'} (g : a D.⇒₁ b) →
          D.Invertible₂ α → D.Invertible₂ (α D.▷ g)
  ▷-inv g i = D.invertible-≅₂ (D.≅₂-invertible i D.▷≅ g)

  -- the structural 2-cells of D, in both directions
  assoc⇒-inv : {a b c d : D.Obj} (f : c D.⇒₁ d) (g : b D.⇒₁ c) (h : a D.⇒₁ b) →
               D.Invertible₂ (D.assoc⇒ f g h)
  assoc⇒-inv f g h = D.invertible-≅₂ (D.associator f g h)

  assoc⇐-inv : {a b c d : D.Obj} (f : c D.⇒₁ d) (g : b D.⇒₁ c) (h : a D.⇒₁ b) →
               D.Invertible₂ (D.assoc⇐ f g h)
  assoc⇐-inv f g h = D.invertible-≅₂ (D.≅₂-sym (D.associator f g h))

  unitˡ⇒-inv : {a b : D.Obj} (f : a D.⇒₁ b) → D.Invertible₂ (D.unitˡ⇒ f)
  unitˡ⇒-inv f = D.invertible-≅₂ (D.unitorˡ f)

  unitˡ⇐-inv : {a b : D.Obj} (f : a D.⇒₁ b) → D.Invertible₂ (D.unitˡ⇐ f)
  unitˡ⇐-inv f = D.invertible-≅₂ (D.≅₂-sym (D.unitorˡ f))

  unitʳ⇒-inv : {a b : D.Obj} (f : a D.⇒₁ b) → D.Invertible₂ (D.unitʳ⇒ f)
  unitʳ⇒-inv f = D.invertible-≅₂ (D.unitorʳ f)

  unitʳ⇐-inv : {a b : D.Obj} (f : a D.⇒₁ b) → D.Invertible₂ (D.unitʳ⇐ f)
  unitʳ⇐-inv f = D.invertible-≅₂ (D.≅₂-sym (D.unitorʳ f))

  -- the comparison 2-cells of F
  F-∘⇐-inv : {a b c : C.Obj} (f : b C.⇒₁ c) (g : a C.⇒₁ b) →
             D.Invertible₂ (F.F-∘⇐ f g)
  F-∘⇐-inv f g = D.invertible-≅₂ (D.≅₂-sym (F.F-∘ f g))

  F-id⇐-inv : {a : C.Obj} → D.Invertible₂ (F.F-id⇐ {a})
  F-id⇐-inv = D.invertible-≅₂ (D.≅₂-sym F.F-id)

  ----------------------------------------------------------------------
  -- The right biadjoint on hom-categories
  ----------------------------------------------------------------------

  -- R₂ is Φ₂ of a whiskering, so its functoriality is that of Φ₂
  R₂-id : {y y' : D.Obj} {g : y D.⇒₁ y'} → R₂ (D.id₂ {f = g}) C.≈ C.id₂
  R₂-id {y} {g = g} = C.≈-trans (Φ₂-cong (D.▷-id g (u y))) Φ₂-id

  R₂-• : {y y' : D.Obj} {g g' g'' : y D.⇒₁ y'} (β' : g' D.⇒₂ g'') (β : g D.⇒₂ g') →
         R₂ (β' D.• β) C.≈ R₂ β' C.• R₂ β
  R₂-• {y} β' β =
    C.≈-trans (Φ₂-cong (D.▷-• β' β (u y))) (Φ₂-• (β' D.▷ u y) (β D.▷ u y))

  Rhom : (y y' : D.Obj) → Functor (D.hom y y') (C.hom (R₀ y) (R₀ y'))
  Rhom y y' = record
    { F₀     = R₁
    ; F₁     = R₂
    ; F-cong = R₂-cong
    ; F-id   = R₂-id
    ; F-∘    = R₂-•
    }

  ----------------------------------------------------------------------
  -- The comparison 2-cells of the right biadjoint
  ----------------------------------------------------------------------

  -- u ∘ F (R g' ∘ R g) ⇒ (g' ∘ g) ∘ u, by peeling off the two ε's
  R-P : {y y' y'' : D.Obj} (g' : y' D.⇒₁ y'') (g : y D.⇒₁ y') →
        (u y'' D.∘₁ F.F₁ (R₁ g' C.∘₁ R₁ g)) D.⇒₂ ((g' D.∘₁ g) D.∘₁ u y)
  R-P {y} {y'} {y''} g' g =
    D.assoc⇐ g' g (u y) D.•
    ((g' D.◁ ε (g D.∘₁ u y)) D.•
     (D.assoc⇒ g' (u y') (F.F₁ (R₁ g)) D.•
      ((ε (g' D.∘₁ u y') D.▷ F.F₁ (R₁ g)) D.•
       (D.assoc⇐ (u y'') (F.F₁ (R₁ g')) (F.F₁ (R₁ g)) D.•
        (u y'' D.◁ F.F-∘⇐ (R₁ g') (R₁ g))))))

  R-P-inv : {y y' y'' : D.Obj} (g' : y' D.⇒₁ y'') (g : y D.⇒₁ y') →
            D.Invertible₂ (R-P g' g)
  R-P-inv {y} {y'} {y''} g' g =
    D.Hom.∘-invertible (assoc⇐-inv g' g (u y))
    (D.Hom.∘-invertible (◁-inv g' (ε-invertible (g D.∘₁ u y)))
    (D.Hom.∘-invertible (assoc⇒-inv g' (u y') (F.F₁ (R₁ g)))
    (D.Hom.∘-invertible (▷-inv (F.F₁ (R₁ g)) (ε-invertible (g' D.∘₁ u y')))
    (D.Hom.∘-invertible (assoc⇐-inv (u y'') (F.F₁ (R₁ g')) (F.F₁ (R₁ g)))
                        (◁-inv (u y'') (F-∘⇐-inv (R₁ g') (R₁ g)))))))

  R-∘⇒ : {y y' y'' : D.Obj} (g' : y' D.⇒₁ y'') (g : y D.⇒₁ y') →
         (R₁ g' C.∘₁ R₁ g) C.⇒₂ R₁ (g' D.∘₁ g)
  R-∘⇒ g' g = ⇑₂ (R-P g' g)

  R-∘ : {y y' y'' : D.Obj} (g' : y' D.⇒₁ y'') (g : y D.⇒₁ y') →
        (R₁ g' C.∘₁ R₁ g) C.≅₂ R₁ (g' D.∘₁ g)
  R-∘ g' g = C.≅₂-invertible (⇑₂-invertible (R-P-inv g' g))

  -- u ∘ F id ⇒ id ∘ u, by the unitors of D
  R-Q : {y : D.Obj} → (u y D.∘₁ F.F₁ (C.id₁ {R₀ y})) D.⇒₂ (D.id₁ {y} D.∘₁ u y)
  R-Q {y} = D.unitˡ⇐ (u y) D.• (D.unitʳ⇒ (u y) D.• (u y D.◁ F.F-id⇐))

  R-Q-inv : {y : D.Obj} → D.Invertible₂ (R-Q {y})
  R-Q-inv {y} =
    D.Hom.∘-invertible (unitˡ⇐-inv (u y))
    (D.Hom.∘-invertible (unitʳ⇒-inv (u y)) (◁-inv (u y) F-id⇐-inv))

  R-id⇒ : {y : D.Obj} → C.id₁ {R₀ y} C.⇒₂ R₁ (D.id₁ {y})
  R-id⇒ = ⇑₂ R-Q

  R-id : {y : D.Obj} → C.id₁ {R₀ y} C.≅₂ R₁ (D.id₁ {y})
  R-id = C.≅₂-invertible (⇑₂-invertible R-Q-inv)

  ----------------------------------------------------------------------
  -- Coherence of the right biadjoint
  ----------------------------------------------------------------------

  -- the defining property of R₂: it is the factorization of β whiskered
  -- by u, so ε turns it back into that whiskering
  R₂-β : {y y' : D.Obj} {g g' : y D.⇒₁ y'} (β : g D.⇒₂ g') →
         ε (g' D.∘₁ u y) D.• w (R₂ β) D.≈ (β D.▷ u y) D.• ε (g D.∘₁ u y)
  R₂-β {y} {g = g} β = ⇑₂-β ((β D.▷ u y) D.• ε (g D.∘₁ u y))

  -- naturality of R-P, which is the naturality of the compositor read
  -- through ε: both sides are the two ways of getting from
  -- u ∘ F (R f ∘ R g) to (f' ∘ g') ∘ u
  R-P-natural : {y y' y'' : D.Obj} {f f' : y' D.⇒₁ y''} {g g' : y D.⇒₁ y'}
                (α : f D.⇒₂ f') (β : g D.⇒₂ g') →
                R-P f' g' D.• (u y'' D.◁ F.F₂ (R₂ α C.∗ R₂ β))
                D.≈ ((α D.∗ β) D.▷ u y) D.• R-P f g
  R-P-natural {y} {y'} {y''} {f} {f'} {g} {g'} α β = begin
    R-P f' g' D.• W
      ≈⟨ shuffle ⟩
    A1 D.• (A2 D.• (A3 D.• (A4 D.• (A5 D.• (A6 D.• W)))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (L6))))) ⟩
    A1 D.• (A2 D.• (A3 D.• (A4 D.• (A5 D.• ((u₂ D.◁ (a D.∗ b)) D.• B6)))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (L5)))) ⟩
    A1 D.• (A2 D.• (A3 D.• (A4 D.• (((u₂ D.◁ a) D.∗ b) D.• (B5 D.• B6)))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (L4))) ⟩
    A1 D.• (A2 D.• (A3 D.• ((((α D.▷ u₁) D.• εf) D.∗ b) D.• (B5 D.• B6))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congˡ L4'))) ⟩
    A1 D.• (A2 D.• (A3 D.• ((((α D.▷ u₁) D.∗ D.id₂) D.• (εf D.∗ b)) D.• (B5 D.• B6))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-assoc))) ⟩
    A1 D.• (A2 D.• (A3 D.• (((α D.▷ u₁) D.∗ D.id₂) D.• ((εf D.∗ b) D.• (B5 D.• B6)))))
      ≈⟨ D.•-congʳ (D.•-congʳ (L3)) ⟩
    A1 D.• (A2 D.• ((α D.▷ (u₁ D.∘₁ B')) D.•
      (B3' D.• ((εf D.∗ b) D.• (B5 D.• B6)))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congˡ (D.∗-decomposeʳ εf b))))) ⟩
    A1 D.• (A2 D.• ((α D.▷ (u₁ D.∘₁ B')) D.•
      (B3' D.• (((((f D.∘₁ u₁) D.◁ b) D.• (εf D.▷ B))) D.• (B5 D.• B6)))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-assoc)))) ⟩
    A1 D.• (A2 D.• ((α D.▷ (u₁ D.∘₁ B')) D.•
      (B3' D.• (((f D.∘₁ u₁) D.◁ b) D.• ((εf D.▷ B) D.• (B5 D.• B6))))))
      ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (L2))) ⟩
    A1 D.• (A2 D.• ((α D.▷ (u₁ D.∘₁ B')) D.•
      ((f D.◁ (u₁ D.◁ b)) D.• (B3 D.• (B4 D.• (B5 D.• B6))))))
      ≈⟨ D.•-congʳ (L1) ⟩
    A1 D.• ((α D.▷ (g' D.∘₁ u₀)) D.•
      ((f D.◁ εg') D.• ((f D.◁ (u₁ D.◁ b)) D.• (B3 D.• (B4 D.• (B5 D.• B6))))))
      ≈⟨ D.•-congʳ (D.•-congʳ (L1')) ⟩
    A1 D.• ((α D.▷ (g' D.∘₁ u₀)) D.•
      ((f D.◁ (β D.▷ u₀)) D.• (B2 D.• (B3 D.• (B4 D.• (B5 D.• B6))))))
      ≈⟨ L0 ⟩
    ((α D.▷ g') D.▷ u₀) D.• (D.assoc⇐ f g' u₀ D.•
      ((f D.◁ (β D.▷ u₀)) D.• (B2 D.• (B3 D.• (B4 D.• (B5 D.• B6))))))
      ≈⟨ D.•-congʳ L0' ⟩
    ((α D.▷ g') D.▷ u₀) D.• (((f D.◁ β) D.▷ u₀) D.• R-P f g)
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (((α D.▷ g') D.▷ u₀) D.• ((f D.◁ β) D.▷ u₀)) D.• R-P f g
      ≈⟨ D.•-congˡ (D.≈-trans (D.≈-sym (D.▷-• (α D.▷ g') (f D.◁ β) u₀))
                              (D.▷-cong u₀ (D.≈-sym (D.∗-decomposeˡ α β)))) ⟩
    ((α D.∗ β) D.▷ u₀) D.• R-P f g ∎
    where
      open D.⇒₂-Reasoning

      u₀ = u y
      u₁ = u y'
      u₂ = u y''
      A  = F.F₁ (R₁ f)
      A' = F.F₁ (R₁ f')
      B  = F.F₁ (R₁ g)
      B' = F.F₁ (R₁ g')
      a  = F.F₂ (R₂ α)
      b  = F.F₂ (R₂ β)
      εf  = ε (f D.∘₁ u₁)
      εf' = ε (f' D.∘₁ u₁)
      εg  = ε (g D.∘₁ u₀)
      εg' = ε (g' D.∘₁ u₀)
      W  = u₂ D.◁ F.F₂ (R₂ α C.∗ R₂ β)

      A1 = D.assoc⇐ f' g' u₀
      A2 = f' D.◁ εg'
      A3 = D.assoc⇒ f' u₁ B'
      A4 = εf' D.▷ B'
      A5 = D.assoc⇐ u₂ A' B'
      A6 = u₂ D.◁ F.F-∘⇐ (R₁ f') (R₁ g')

      B1 = D.assoc⇐ f g u₀
      B2 = f D.◁ εg
      B3 = D.assoc⇒ f u₁ B
      B3' = D.assoc⇒ f u₁ B'
      B4 = εf D.▷ B
      B5 = D.assoc⇐ u₂ A B
      B6 = u₂ D.◁ F.F-∘⇐ (R₁ f) (R₁ g)

      shuffle = D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc)))))))

      L6 : A6 D.• W D.≈ (u₂ D.◁ (a D.∗ b)) D.• B6
      L6 = D.≈-trans (D.≈-sym (D.◁-• u₂ (F.F-∘⇐ (R₁ f') (R₁ g')) (F.F₂ (R₂ α C.∗ R₂ β))))
           (D.≈-trans (D.◁-cong u₂ (F.F-∘-natural⇐ (R₂ α) (R₂ β)))
                      (D.◁-• u₂ (a D.∗ b) (F.F-∘⇐ (R₁ f) (R₁ g))))

      L5 : A5 D.• ((u₂ D.◁ (a D.∗ b)) D.• B6) D.≈ ((u₂ D.◁ a) D.∗ b) D.• (B5 D.• B6)
      L5 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = u₂}) a b)) D.•-assoc)

      L4 : A4 D.• (((u₂ D.◁ a) D.∗ b) D.• (B5 D.• B6))
           D.≈ (((α D.▷ u₁) D.• εf) D.∗ b) D.• (B5 D.• B6)
      L4 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.•-congˡ (D.≈-trans (D.≈-sym (D.∗-• εf' (u₂ D.◁ a) D.id₂ b))
                                 (D.∗-cong (R₂-β α) D.•-identityˡ)))

      L4' : ((α D.▷ u₁) D.• εf) D.∗ b D.≈ ((α D.▷ u₁) D.∗ D.id₂) D.• (εf D.∗ b)
      L4' = D.≈-trans (D.∗-cong D.≈-refl (D.≈-sym D.•-identityˡ))
                      (D.∗-• (α D.▷ u₁) εf D.id₂ b)

      L3 : A3 D.• (((α D.▷ u₁) D.∗ D.id₂) D.• ((εf D.∗ b) D.• (B5 D.• B6)))
           D.≈ (α D.▷ (u₁ D.∘₁ B')) D.• (B3' D.• ((εf D.∗ b) D.• (B5 D.• B6)))
      L3 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.≈-sym (D.assoc-natural α (D.id₂ {f = u₁}) (D.id₂ {f = B'})))
                        (D.•-congˡ (D.∗-cong D.≈-refl (D.∗-id u₁ B')))))
            D.•-assoc)

      L2 : B3' D.• (((f D.∘₁ u₁) D.◁ b) D.• ((εf D.▷ B) D.• (B5 D.• B6)))
           D.≈ (f D.◁ (u₁ D.◁ b)) D.• (B3 D.• (B4 D.• (B5 D.• B6)))
      L2 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.•-congʳ (D.∗-cong (D.≈-sym (D.∗-id f u₁)) D.≈-refl))
                        (D.≈-sym (D.assoc-natural (D.id₂ {f = f}) (D.id₂ {f = u₁}) b))))
            D.•-assoc)

      L1 : A2 D.• ((α D.▷ (u₁ D.∘₁ B')) D.•
             ((f D.◁ (u₁ D.◁ b)) D.• (B3 D.• (B4 D.• (B5 D.• B6)))))
           D.≈ (α D.▷ (g' D.∘₁ u₀)) D.•
             ((f D.◁ εg') D.• ((f D.◁ (u₁ D.◁ b)) D.• (B3 D.• (B4 D.• (B5 D.• B6)))))
      L1 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ (D.≈-sym (D.exchange α εg'))) D.•-assoc)

      L1' : (f D.◁ εg') D.• ((f D.◁ (u₁ D.◁ b)) D.• (B3 D.• (B4 D.• (B5 D.• B6))))
            D.≈ (f D.◁ (β D.▷ u₀)) D.• (B2 D.• (B3 D.• (B4 D.• (B5 D.• B6))))
      L1' = D.≈-trans (D.≈-sym D.•-assoc)
            (D.≈-trans (D.•-congˡ
              (D.≈-trans (D.≈-sym (D.◁-• f εg' (u₁ D.◁ b)))
              (D.≈-trans (D.◁-cong f (R₂-β β)) (D.◁-• f (β D.▷ u₀) εg))))
             D.•-assoc)

      L0 : A1 D.• ((α D.▷ (g' D.∘₁ u₀)) D.•
             ((f D.◁ (β D.▷ u₀)) D.• (B2 D.• (B3 D.• (B4 D.• (B5 D.• B6))))))
           D.≈ ((α D.▷ g') D.▷ u₀) D.• (D.assoc⇐ f g' u₀ D.•
             ((f D.◁ (β D.▷ u₀)) D.• (B2 D.• (B3 D.• (B4 D.• (B5 D.• B6))))))
      L0 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.•-congʳ (D.∗-cong D.≈-refl (D.≈-sym (D.∗-id g' u₀))))
                        (D.assoc-natural⇐ α (D.id₂ {f = g'}) (D.id₂ {f = u₀}))))
            D.•-assoc)

      L0' : D.assoc⇐ f g' u₀ D.•
              ((f D.◁ (β D.▷ u₀)) D.• (B2 D.• (B3 D.• (B4 D.• (B5 D.• B6)))))
            D.≈ ((f D.◁ β) D.▷ u₀) D.• R-P f g
      L0' = D.≈-trans (D.≈-sym D.•-assoc)
            (D.≈-trans (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = f}) β (D.id₂ {f = u₀})))
                       D.•-assoc)

  -- naturality of the compositor of the right biadjoint: since both
  -- sides land in R₁ (f' ∘ g') = ⇑₁ ((f' ∘ g') ∘ u), it is enough to
  -- compare them through ε, which is R-P-natural
  R-∘-natural : {y y' y'' : D.Obj} {f f' : y' D.⇒₁ y''} {g g' : y D.⇒₁ y'}
                (α : f D.⇒₂ f') (β : g D.⇒₂ g') →
                (R₂ (α D.∗ β) C.• R-∘⇒ f g)
                C.≈ (R-∘⇒ f' g' C.• (R₂ α C.∗ R₂ β))
  R-∘-natural {y} {y'} {y''} {f} {f'} {g} {g'} α β = ⇑₂-cancel (begin
    ε ((f' D.∘₁ g') D.∘₁ u y) D.• w (R₂ (α D.∗ β) C.• R-∘⇒ f g)
      ≈⟨ D.•-congʳ (w-• (R₂ (α D.∗ β)) (R-∘⇒ f g)) ⟩
    ε ((f' D.∘₁ g') D.∘₁ u y) D.• (w (R₂ (α D.∗ β)) D.• w (R-∘⇒ f g))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (ε ((f' D.∘₁ g') D.∘₁ u y) D.• w (R₂ (α D.∗ β))) D.• w (R-∘⇒ f g)
      ≈⟨ D.•-congˡ (R₂-β (α D.∗ β)) ⟩
    (((α D.∗ β) D.▷ u y) D.• ε ((f D.∘₁ g) D.∘₁ u y)) D.• w (R-∘⇒ f g)
      ≈⟨ D.•-assoc ⟩
    ((α D.∗ β) D.▷ u y) D.• (ε ((f D.∘₁ g) D.∘₁ u y) D.• w (R-∘⇒ f g))
      ≈⟨ D.•-congʳ (⇑₂-β (R-P f g)) ⟩
    ((α D.∗ β) D.▷ u y) D.• R-P f g
      ≈⟨ D.≈-sym (R-P-natural α β) ⟩
    R-P f' g' D.• (u y'' D.◁ F.F₂ (R₂ α C.∗ R₂ β))
      ≈⟨ D.•-congˡ (D.≈-sym (⇑₂-β (R-P f' g'))) ⟩
    (ε ((f' D.∘₁ g') D.∘₁ u y) D.• w (R-∘⇒ f' g')) D.• w (R₂ α C.∗ R₂ β)
      ≈⟨ D.•-assoc ⟩
    ε ((f' D.∘₁ g') D.∘₁ u y) D.• (w (R-∘⇒ f' g') D.• w (R₂ α C.∗ R₂ β))
      ≈⟨ D.•-congʳ (D.≈-sym (w-• (R-∘⇒ f' g') (R₂ α C.∗ R₂ β))) ⟩
    ε ((f' D.∘₁ g') D.∘₁ u y) D.• w (R-∘⇒ f' g' C.• (R₂ α C.∗ R₂ β)) ∎)
    where open D.⇒₂-Reasoning

  -- F's unit coherence, solved for F₂ of the unitors of C
  F₂-unitˡ : {a b : C.Obj} (h : a C.⇒₁ b) →
             F.F₂ (C.unitˡ⇒ h)
             D.≈ (D.unitˡ⇒ (F.F₁ h) D.•
                   ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h))
  F₂-unitˡ {a} {b} h = D.≈-sym (begin
    D.unitˡ⇒ (F.F₁ h) D.• ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h)
      ≈⟨ D.•-congˡ (D.≈-sym (F.F-unitˡ h)) ⟩
    (F.F₂ (C.unitˡ⇒ h) D.• (F.F-∘⇒ C.id₁ h D.• (F.F-id⇒ D.▷ F.F₁ h)))
      D.• ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h)
      ≈⟨ D.•-assoc ⟩
    F.F₂ (C.unitˡ⇒ h) D.•
      ((F.F-∘⇒ C.id₁ h D.• (F.F-id⇒ D.▷ F.F₁ h))
        D.• ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h))
      ≈⟨ D.•-congʳ collapse ⟩
    F.F₂ (C.unitˡ⇒ h) D.• D.id₂
      ≈⟨ D.•-identityʳ ⟩
    F.F₂ (C.unitˡ⇒ h) ∎)
    where
      open D.⇒₂-Reasoning

      collapse : (F.F-∘⇒ C.id₁ h D.• (F.F-id⇒ D.▷ F.F₁ h))
                 D.• ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h)
                 D.≈ D.id₂
      collapse = begin
        (F.F-∘⇒ C.id₁ h D.• (F.F-id⇒ D.▷ F.F₁ h))
          D.• ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h)
          ≈⟨ D.•-assoc ⟩
        F.F-∘⇒ C.id₁ h D.• ((F.F-id⇒ D.▷ F.F₁ h)
          D.• ((F.F-id⇐ D.▷ F.F₁ h) D.• F.F-∘⇐ C.id₁ h))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        F.F-∘⇒ C.id₁ h D.• (((F.F-id⇒ D.▷ F.F₁ h) D.• (F.F-id⇐ D.▷ F.F₁ h))
          D.• F.F-∘⇐ C.id₁ h)
          ≈⟨ D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.≈-sym (D.▷-• F.F-id⇒ F.F-id⇐ (F.F₁ h)))
               (D.≈-trans (D.▷-cong (F.F₁ h) (D.≅₂isoʳ F.F-id))
                          (D.▷-id (F.F₁ (C.id₁ {b})) (F.F₁ h))))) ⟩
        F.F-∘⇒ C.id₁ h D.• (D.id₂ D.• F.F-∘⇐ C.id₁ h)
          ≈⟨ D.•-congʳ D.•-identityˡ ⟩
        F.F-∘⇒ C.id₁ h D.• F.F-∘⇐ C.id₁ h
          ≈⟨ D.≅₂isoʳ (F.F-∘ C.id₁ h) ⟩
        D.id₂ ∎

  F₂-unitʳ : {a b : C.Obj} (h : a C.⇒₁ b) →
             F.F₂ (C.unitʳ⇒ h)
             D.≈ (D.unitʳ⇒ (F.F₁ h) D.•
                   ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁))
  F₂-unitʳ {a} {b} h = D.≈-sym (begin
    D.unitʳ⇒ (F.F₁ h) D.• ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁)
      ≈⟨ D.•-congˡ (D.≈-sym (F.F-unitʳ h)) ⟩
    (F.F₂ (C.unitʳ⇒ h) D.• (F.F-∘⇒ h C.id₁ D.• (F.F₁ h D.◁ F.F-id⇒)))
      D.• ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁)
      ≈⟨ D.•-assoc ⟩
    F.F₂ (C.unitʳ⇒ h) D.•
      ((F.F-∘⇒ h C.id₁ D.• (F.F₁ h D.◁ F.F-id⇒))
        D.• ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁))
      ≈⟨ D.•-congʳ collapse ⟩
    F.F₂ (C.unitʳ⇒ h) D.• D.id₂
      ≈⟨ D.•-identityʳ ⟩
    F.F₂ (C.unitʳ⇒ h) ∎)
    where
      open D.⇒₂-Reasoning

      collapse : (F.F-∘⇒ h C.id₁ D.• (F.F₁ h D.◁ F.F-id⇒))
                 D.• ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁)
                 D.≈ D.id₂
      collapse = begin
        (F.F-∘⇒ h C.id₁ D.• (F.F₁ h D.◁ F.F-id⇒))
          D.• ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁)
          ≈⟨ D.•-assoc ⟩
        F.F-∘⇒ h C.id₁ D.• ((F.F₁ h D.◁ F.F-id⇒)
          D.• ((F.F₁ h D.◁ F.F-id⇐) D.• F.F-∘⇐ h C.id₁))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        F.F-∘⇒ h C.id₁ D.• (((F.F₁ h D.◁ F.F-id⇒) D.• (F.F₁ h D.◁ F.F-id⇐))
          D.• F.F-∘⇐ h C.id₁)
          ≈⟨ D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.≈-sym (D.◁-• (F.F₁ h) F.F-id⇒ F.F-id⇐))
               (D.≈-trans (D.◁-cong (F.F₁ h) (D.≅₂isoʳ F.F-id))
                          (D.◁-id (F.F₁ h) (F.F₁ (C.id₁ {a})))))) ⟩
        F.F-∘⇒ h C.id₁ D.• (D.id₂ D.• F.F-∘⇐ h C.id₁)
          ≈⟨ D.•-congʳ D.•-identityˡ ⟩
        F.F-∘⇒ h C.id₁ D.• F.F-∘⇐ h C.id₁
          ≈⟨ D.≅₂isoʳ (F.F-∘ h C.id₁) ⟩
        D.id₂ ∎

  -- the unit 2-cell of the right biadjoint, read through ε
  R-Q-β : {y : D.Obj} → ε (D.id₁ D.∘₁ u y) D.• w (R-id⇒ {y}) D.≈ R-Q {y}
  R-Q-β {y} = ⇑₂-β (R-Q {y})

  -- the left unit coherence of the right biadjoint
  R-unitˡ : {y y' : D.Obj} (g : y D.⇒₁ y') →
            (R₂ (D.unitˡ⇒ g) C.• (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ R₁ g)))
            C.≈ C.unitˡ⇒ (R₁ g)
  R-unitˡ {y} {y'} g = ⇑₂-cancel (begin
    εg D.• w (R₂ λg C.• (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ h)))
      ≈⟨ D.•-congʳ (w-• (R₂ λg) (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ h))) ⟩
    εg D.• (w (R₂ λg) D.• w (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ h)))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (εg D.• w (R₂ λg)) D.• w (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ h))
      ≈⟨ D.•-congˡ (R₂-β λg) ⟩
    ((λg D.▷ u₀) D.• ε ((D.id₁ D.∘₁ g) D.∘₁ u₀))
      D.• w (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ h))
      ≈⟨ D.•-assoc ⟩
    (λg D.▷ u₀) D.• (ε ((D.id₁ D.∘₁ g) D.∘₁ u₀)
      D.• w (R-∘⇒ (D.id₁ {y'}) g C.• (R-id⇒ C.▷ h)))
      ≈⟨ D.•-congʳ (D.•-congʳ (w-• (R-∘⇒ (D.id₁ {y'}) g) (R-id⇒ C.▷ h))) ⟩
    (λg D.▷ u₀) D.• (ε ((D.id₁ D.∘₁ g) D.∘₁ u₀)
      D.• (w (R-∘⇒ (D.id₁ {y'}) g) D.• W))
      ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
    (λg D.▷ u₀) D.• ((ε ((D.id₁ D.∘₁ g) D.∘₁ u₀)
      D.• w (R-∘⇒ (D.id₁ {y'}) g)) D.• W)
      ≈⟨ D.•-congʳ (D.•-congˡ (⇑₂-β (R-P (D.id₁ {y'}) g))) ⟩
    (λg D.▷ u₀) D.• (R-P (D.id₁ {y'}) g D.• W)
      ≈⟨ main ⟩
    εg D.• Z
      ≈⟨ D.•-congʳ (D.≈-sym unfoldZ) ⟩
    εg D.• w (C.unitˡ⇒ h) ∎)
    where
      open D.⇒₂-Reasoning

      u₀ = u y
      u₁ = u y'
      h  = R₁ g
      Fh = F.F₁ h
      E  = R₁ (D.id₁ {y'})
      ρ  = R-id⇒ {y'}
      εg = ε (g D.∘₁ u₀)
      εi = ε (D.id₁ D.∘₁ u₁)
      λg = D.unitˡ⇒ g
      W  = u₁ D.◁ F.F₂ (ρ C.▷ h)
      X  = u₁ D.◁ F.F-∘⇐ (C.id₁ {R₀ y'}) h
      V  = (u₁ D.◁ (F.F-id⇐ D.▷ Fh)) D.• X
      Z  = (u₁ D.◁ D.unitˡ⇒ Fh) D.• V

      C1 = D.assoc⇐ (D.id₁ {y'}) g u₀
      C2 = D.id₁ D.◁ εg
      C3 = D.assoc⇒ (D.id₁ {y'}) u₁ Fh
      C4 = εi D.▷ Fh
      C5 = D.assoc⇐ u₁ (F.F₁ E) Fh
      C6 = u₁ D.◁ F.F-∘⇐ E h

      unfoldZ : w (C.unitˡ⇒ h) D.≈ Z
      unfoldZ = D.≈-trans (D.◁-cong u₁ (F₂-unitˡ h))
                (D.≈-trans (D.◁-• u₁ (D.unitˡ⇒ Fh)
                             ((F.F-id⇐ D.▷ Fh) D.• F.F-∘⇐ (C.id₁ {R₀ y'}) h))
                           (D.•-congʳ (D.◁-• u₁ (F.F-id⇐ D.▷ Fh)
                                        (F.F-∘⇐ (C.id₁ {R₀ y'}) h))))

      shuffle : R-P (D.id₁ {y'}) g D.• W
                D.≈ C1 D.• (C2 D.• (C3 D.• (C4 D.• (C5 D.• (C6 D.• W)))))
      shuffle = D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc)))))))

      K6 : C6 D.• W D.≈ (u₁ D.◁ (F.F₂ ρ D.▷ Fh)) D.• X
      K6 = D.≈-trans (D.≈-sym (D.◁-• u₁ (F.F-∘⇐ E h) (F.F₂ (ρ C.▷ h))))
           (D.≈-trans (D.◁-cong u₁ (F.F-∘-natural⇐ ρ (C.id₂ {f = h})))
           (D.≈-trans (D.◁-• u₁ (F.F₂ ρ D.∗ F.F₂ (C.id₂ {f = h}))
                                (F.F-∘⇐ (C.id₁ {R₀ y'}) h))
                      (D.•-congˡ (D.◁-cong u₁ (D.∗-cong D.≈-refl F.F₂-id₂)))))

      K5 : C5 D.• ((u₁ D.◁ (F.F₂ ρ D.▷ Fh)) D.• X)
           D.≈ ((u₁ D.◁ F.F₂ ρ) D.▷ Fh)
                 D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)
      K5 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = u₁})
                                   (F.F₂ ρ) (D.id₂ {f = Fh})))
                      D.•-assoc)

      K4 : C4 D.• (((u₁ D.◁ F.F₂ ρ) D.▷ Fh)
             D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X))
           D.≈ (R-Q D.▷ Fh)
                 D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)
      K4 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.•-congˡ (D.≈-trans (D.≈-sym (D.▷-• εi (u₁ D.◁ F.F₂ ρ) Fh))
                                 (D.▷-cong Fh (R-Q-β {y'}))))

      -- the triangle of D, with the associator moved to the other side
      tri : (D.unitʳ⇒ u₁ D.▷ Fh) D.• D.assoc⇐ u₁ D.id₁ Fh D.≈ u₁ D.◁ D.unitˡ⇒ Fh
      tri = D.≈-trans (D.•-congˡ (D.triangle u₁ Fh))
            (D.≈-trans D.•-assoc
            (D.≈-trans (D.•-congʳ (D.≅₂isoʳ (D.associator u₁ D.id₁ Fh)))
                       D.•-identityʳ))

      K3 : (R-Q D.▷ Fh)
             D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)
           D.≈ (D.unitˡ⇐ u₁ D.▷ Fh) D.• Z
      K3 = begin
        (R-Q D.▷ Fh) D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)
          ≈⟨ D.•-congˡ (D.≈-trans
               (D.▷-• (D.unitˡ⇐ u₁)
                      (D.unitʳ⇒ u₁ D.• (u₁ D.◁ F.F-id⇐)) Fh)
               (D.•-congʳ (D.▷-• (D.unitʳ⇒ u₁) (u₁ D.◁ F.F-id⇐) Fh))) ⟩
        ((D.unitˡ⇐ u₁ D.▷ Fh) D.•
          ((D.unitʳ⇒ u₁ D.▷ Fh) D.• ((u₁ D.◁ F.F-id⇐) D.▷ Fh)))
          D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)
          ≈⟨ D.•-assoc ⟩
        (D.unitˡ⇐ u₁ D.▷ Fh) D.•
          (((D.unitʳ⇒ u₁ D.▷ Fh) D.• ((u₁ D.◁ F.F-id⇐) D.▷ Fh))
            D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (D.unitˡ⇐ u₁ D.▷ Fh) D.•
          ((D.unitʳ⇒ u₁ D.▷ Fh) D.• (((u₁ D.◁ F.F-id⇐) D.▷ Fh)
            D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym (D.assoc-natural⇐ (D.id₂ {f = u₁})
                                       F.F-id⇐ (D.id₂ {f = Fh}))))
                          D.•-assoc))) ⟩
        (D.unitˡ⇐ u₁ D.▷ Fh) D.•
          ((D.unitʳ⇒ u₁ D.▷ Fh) D.• (D.assoc⇐ u₁ D.id₁ Fh D.• V))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc) (D.•-congˡ tri)) ⟩
        (D.unitˡ⇐ u₁ D.▷ Fh) D.• Z ∎

      K2 : C3 D.• ((D.unitˡ⇐ u₁ D.▷ Fh) D.• Z)
           D.≈ D.unitˡ⇐ (u₁ D.∘₁ Fh) D.• Z
      K2 = D.≈-trans (D.≈-sym D.•-assoc) (D.•-congˡ (D.unitˡ⇐-∘ u₁ Fh))

      K1 : C2 D.• (D.unitˡ⇐ (u₁ D.∘₁ Fh) D.• Z)
           D.≈ D.unitˡ⇐ (g D.∘₁ u₀) D.• (εg D.• Z)
      K1 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ (D.≈-sym (D.unitˡ-natural⇐ εg))) D.•-assoc)

      K0 : (λg D.▷ u₀) D.• (C1 D.• (D.unitˡ⇐ (g D.∘₁ u₀) D.• (εg D.• Z)))
           D.≈ εg D.• Z
      K0 = D.≈-trans (D.•-congʳ (D.≈-sym D.•-assoc))
           (D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ (D.≈-trans (D.≈-sym D.•-assoc)
                                            (D.•-congˡ (D.unitˡ-∘' g u₀))))
           (D.≈-trans (D.•-congˡ (D.≅₂isoʳ (D.unitorˡ (g D.∘₁ u₀))))
                      D.•-identityˡ)))

      main : (λg D.▷ u₀) D.• (R-P (D.id₁ {y'}) g D.• W) D.≈ εg D.• Z
      main = begin
        (λg D.▷ u₀) D.• (R-P (D.id₁ {y'}) g D.• W)
          ≈⟨ D.•-congʳ shuffle ⟩
        (λg D.▷ u₀) D.• (C1 D.• (C2 D.• (C3 D.• (C4 D.• (C5 D.• (C6 D.• W))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ K6))))) ⟩
        (λg D.▷ u₀) D.• (C1 D.• (C2 D.• (C3 D.• (C4 D.• (C5 D.•
          ((u₁ D.◁ (F.F₂ ρ D.▷ Fh)) D.• X))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ K5)))) ⟩
        (λg D.▷ u₀) D.• (C1 D.• (C2 D.• (C3 D.• (C4 D.•
          (((u₁ D.◁ F.F₂ ρ) D.▷ Fh)
            D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ K4))) ⟩
        (λg D.▷ u₀) D.• (C1 D.• (C2 D.• (C3 D.•
          ((R-Q D.▷ Fh) D.• (D.assoc⇐ u₁ (F.F₁ (C.id₁ {R₀ y'})) Fh D.• X)))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ K3))) ⟩
        (λg D.▷ u₀) D.• (C1 D.• (C2 D.• (C3 D.• ((D.unitˡ⇐ u₁ D.▷ Fh) D.• Z))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ K2)) ⟩
        (λg D.▷ u₀) D.• (C1 D.• (C2 D.• (D.unitˡ⇐ (u₁ D.∘₁ Fh) D.• Z)))
          ≈⟨ D.•-congʳ (D.•-congʳ K1) ⟩
        (λg D.▷ u₀) D.• (C1 D.• (D.unitˡ⇐ (g D.∘₁ u₀) D.• (εg D.• Z)))
          ≈⟨ K0 ⟩
        εg D.• Z ∎

  -- the right unit coherence of the right biadjoint
  R-unitʳ : {y y' : D.Obj} (g : y D.⇒₁ y') →
            (R₂ (D.unitʳ⇒ g) C.• (R-∘⇒ g (D.id₁ {y}) C.• (R₁ g C.◁ R-id⇒)))
            C.≈ C.unitʳ⇒ (R₁ g)
  R-unitʳ {y} {y'} g = ⇑₂-cancel (begin
    εg D.• w (R₂ rg C.• (R-∘⇒ g (D.id₁ {y}) C.• (h C.◁ R-id⇒)))
      ≈⟨ D.•-congʳ (w-• (R₂ rg) (R-∘⇒ g (D.id₁ {y}) C.• (h C.◁ R-id⇒))) ⟩
    εg D.• (w (R₂ rg) D.• w (R-∘⇒ g (D.id₁ {y}) C.• (h C.◁ R-id⇒)))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (εg D.• w (R₂ rg)) D.• w (R-∘⇒ g (D.id₁ {y}) C.• (h C.◁ R-id⇒))
      ≈⟨ D.•-congˡ (R₂-β rg) ⟩
    ((rg D.▷ u₀) D.• ε ((g D.∘₁ D.id₁) D.∘₁ u₀))
      D.• w (R-∘⇒ g (D.id₁ {y}) C.• (h C.◁ R-id⇒))
      ≈⟨ D.•-assoc ⟩
    (rg D.▷ u₀) D.• (ε ((g D.∘₁ D.id₁) D.∘₁ u₀)
      D.• w (R-∘⇒ g (D.id₁ {y}) C.• (h C.◁ R-id⇒)))
      ≈⟨ D.•-congʳ (D.•-congʳ (w-• (R-∘⇒ g (D.id₁ {y})) (h C.◁ R-id⇒))) ⟩
    (rg D.▷ u₀) D.• (ε ((g D.∘₁ D.id₁) D.∘₁ u₀)
      D.• (w (R-∘⇒ g (D.id₁ {y})) D.• W'))
      ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
    (rg D.▷ u₀) D.• ((ε ((g D.∘₁ D.id₁) D.∘₁ u₀)
      D.• w (R-∘⇒ g (D.id₁ {y}))) D.• W')
      ≈⟨ D.•-congʳ (D.•-congˡ (⇑₂-β (R-P g (D.id₁ {y})))) ⟩
    (rg D.▷ u₀) D.• (R-P g (D.id₁ {y}) D.• W')
      ≈⟨ main ⟩
    εg D.• Z'
      ≈⟨ D.•-congʳ (D.≈-sym unfoldZ') ⟩
    εg D.• w (C.unitʳ⇒ h) ∎)
    where
      open D.⇒₂-Reasoning

      u₀ = u y
      u₁ = u y'
      h  = R₁ g
      Fh = F.F₁ h
      E  = R₁ (D.id₁ {y})
      FE = F.F₁ E
      K  = F.F₁ (C.id₁ {R₀ y})
      ρ  = R-id⇒ {y}
      δ  = F.F-id⇐ {R₀ y}
      εg = ε (g D.∘₁ u₀)
      εi = ε (D.id₁ D.∘₁ u₀)
      rg = D.unitʳ⇒ g
      W' = u₁ D.◁ F.F₂ (h C.◁ ρ)
      X' = u₁ D.◁ F.F-∘⇐ h (C.id₁ {R₀ y})
      Z' = (u₁ D.◁ D.unitʳ⇒ Fh) D.• ((u₁ D.◁ (Fh D.◁ δ)) D.• X')
      S  = (εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')
      T  = D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))

      P1 = D.assoc⇐ g (D.id₁ {y}) u₀
      P2 = g D.◁ εi
      P3 = D.assoc⇒ g u₀ FE
      P4 = εg D.▷ FE
      P5 = D.assoc⇐ u₁ Fh FE
      P6 = u₁ D.◁ F.F-∘⇐ h E

      unfoldZ' : w (C.unitʳ⇒ h) D.≈ Z'
      unfoldZ' = D.≈-trans (D.◁-cong u₁ (F₂-unitʳ h))
                 (D.≈-trans (D.◁-• u₁ (D.unitʳ⇒ Fh)
                              ((Fh D.◁ δ) D.• F.F-∘⇐ h (C.id₁ {R₀ y})))
                            (D.•-congʳ (D.◁-• u₁ (Fh D.◁ δ)
                                         (F.F-∘⇐ h (C.id₁ {R₀ y})))))

      shuffle : R-P g (D.id₁ {y}) D.• W'
                D.≈ P1 D.• (P2 D.• (P3 D.• (P4 D.• (P5 D.• (P6 D.• W')))))
      shuffle = D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc)))))))

      M6 : P6 D.• W' D.≈ (u₁ D.◁ (Fh D.◁ F.F₂ ρ)) D.• X'
      M6 = D.≈-trans (D.≈-sym (D.◁-• u₁ (F.F-∘⇐ h E) (F.F₂ (h C.◁ ρ))))
           (D.≈-trans (D.◁-cong u₁ (F.F-∘-natural⇐ (C.id₂ {f = h}) ρ))
           (D.≈-trans (D.◁-• u₁ (F.F₂ (C.id₂ {f = h}) D.∗ F.F₂ ρ)
                                (F.F-∘⇐ h (C.id₁ {R₀ y})))
                      (D.•-congˡ (D.◁-cong u₁ (D.∗-cong F.F₂-id₂ D.≈-refl)))))

      M5 : P5 D.• ((u₁ D.◁ (Fh D.◁ F.F₂ ρ)) D.• X')
           D.≈ ((u₁ D.∘₁ Fh) D.◁ F.F₂ ρ) D.• (D.assoc⇐ u₁ Fh K D.• X')
      M5 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = u₁}) (D.id₂ {f = Fh}) (F.F₂ ρ))
                        (D.•-congˡ (D.∗-cong (D.∗-id u₁ Fh) D.≈-refl))))
                      D.•-assoc)

      M4 : P4 D.• (((u₁ D.∘₁ Fh) D.◁ F.F₂ ρ) D.• (D.assoc⇐ u₁ Fh K D.• X'))
           D.≈ ((g D.∘₁ u₀) D.◁ F.F₂ ρ)
                 D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))
      M4 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.≈-sym (D.∗-• εg (D.id₂ {f = u₁ D.∘₁ Fh})
                                           (D.id₂ {f = FE}) (F.F₂ ρ)))
             (D.≈-trans (D.∗-cong D.•-identityʳ D.•-identityˡ)
                        (D.∗-decomposeʳ εg (F.F₂ ρ)))))
                      D.•-assoc)

      M3 : P3 D.• (((g D.∘₁ u₀) D.◁ F.F₂ ρ) D.• S)
           D.≈ (g D.◁ (u₀ D.◁ F.F₂ ρ)) D.• (D.assoc⇒ g u₀ K D.• S)
      M3 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-sym (D.≈-trans (D.assoc-natural (D.id₂ {f = g}) (D.id₂ {f = u₀}) (F.F₂ ρ))
                                 (D.•-congʳ (D.∗-cong (D.∗-id g u₀) D.≈-refl)))))
                      D.•-assoc)

      M2 : P2 D.• ((g D.◁ (u₀ D.◁ F.F₂ ρ)) D.• T) D.≈ (g D.◁ R-Q) D.• T
      M2 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.•-congˡ (D.≈-trans (D.≈-sym (D.◁-• g εi (u₀ D.◁ F.F₂ ρ)))
                                 (D.◁-cong g (R-Q-β {y}))))

      -- the last stretch: ε is moved to the front past the unitors
      final : (g D.◁ D.unitʳ⇒ u₀) D.•
                ((g D.◁ (u₀ D.◁ δ)) D.•
                  (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))
              D.≈ εg D.• Z'
      final = begin
        (g D.◁ D.unitʳ⇒ u₀) D.•
          ((g D.◁ (u₀ D.◁ δ)) D.•
            (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        (g D.◁ D.unitʳ⇒ u₀) D.•
          (((g D.◁ (u₀ D.◁ δ)) D.• D.assoc⇒ g u₀ K)
            D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.assoc-natural (D.id₂ {f = g}) (D.id₂ {f = u₀}) δ)
                          (D.•-congʳ (D.∗-cong (D.∗-id g u₀) D.≈-refl)))) ⟩
        (g D.◁ D.unitʳ⇒ u₀) D.•
          ((D.assoc⇒ g u₀ D.id₁ D.• ((g D.∘₁ u₀) D.◁ δ))
            D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (g D.◁ D.unitʳ⇒ u₀) D.•
          (D.assoc⇒ g u₀ D.id₁ D.• (((g D.∘₁ u₀) D.◁ δ)
            D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((g D.◁ D.unitʳ⇒ u₀) D.• D.assoc⇒ g u₀ D.id₁) D.•
          (((g D.∘₁ u₀) D.◁ δ) D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.•-congˡ (D.≈-sym (D.unitʳ-∘ g u₀)) ⟩
        D.unitʳ⇒ (g D.∘₁ u₀) D.•
          (((g D.∘₁ u₀) D.◁ δ) D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        D.unitʳ⇒ (g D.∘₁ u₀) D.•
          ((((g D.∘₁ u₀) D.◁ δ) D.• (εg D.▷ K)) D.• (D.assoc⇐ u₁ Fh K D.• X'))
          ≈⟨ D.•-congʳ (D.•-congˡ (D.≈-sym (D.exchange εg δ))) ⟩
        D.unitʳ⇒ (g D.∘₁ u₀) D.•
          (((εg D.▷ D.id₁) D.• ((u₁ D.∘₁ Fh) D.◁ δ)) D.• (D.assoc⇐ u₁ Fh K D.• X'))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        D.unitʳ⇒ (g D.∘₁ u₀) D.•
          ((εg D.▷ D.id₁) D.• (((u₁ D.∘₁ Fh) D.◁ δ) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D.unitʳ⇒ (g D.∘₁ u₀) D.• (εg D.▷ D.id₁)) D.•
          (((u₁ D.∘₁ Fh) D.◁ δ) D.• (D.assoc⇐ u₁ Fh K D.• X'))
          ≈⟨ D.•-congˡ (D.≈-sym (D.unitʳ-natural εg)) ⟩
        (εg D.• D.unitʳ⇒ (u₁ D.∘₁ Fh)) D.•
          (((u₁ D.∘₁ Fh) D.◁ δ) D.• (D.assoc⇐ u₁ Fh K D.• X'))
          ≈⟨ D.•-assoc ⟩
        εg D.• (D.unitʳ⇒ (u₁ D.∘₁ Fh) D.•
          (((u₁ D.∘₁ Fh) D.◁ δ) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-sym D.•-assoc)) ⟩
        εg D.• (D.unitʳ⇒ (u₁ D.∘₁ Fh) D.•
          ((((u₁ D.∘₁ Fh) D.◁ δ) D.• D.assoc⇐ u₁ Fh K) D.• X'))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congˡ
               (D.≈-sym (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = u₁}) (D.id₂ {f = Fh}) δ)
                                   (D.•-congˡ (D.∗-cong (D.∗-id u₁ Fh) D.≈-refl)))))) ⟩
        εg D.• (D.unitʳ⇒ (u₁ D.∘₁ Fh) D.•
          ((D.assoc⇐ u₁ Fh D.id₁ D.• (u₁ D.◁ (Fh D.◁ δ))) D.• X'))
          ≈⟨ D.•-congʳ (D.•-congʳ D.•-assoc) ⟩
        εg D.• (D.unitʳ⇒ (u₁ D.∘₁ Fh) D.•
          (D.assoc⇐ u₁ Fh D.id₁ D.• ((u₁ D.◁ (Fh D.◁ δ)) D.• X')))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        εg D.• ((D.unitʳ⇒ (u₁ D.∘₁ Fh) D.• D.assoc⇐ u₁ Fh D.id₁)
          D.• ((u₁ D.◁ (Fh D.◁ δ)) D.• X'))
          ≈⟨ D.•-congʳ (D.•-congˡ unitʳ-slide) ⟩
        εg D.• Z' ∎
        where
          unitʳ-slide : D.unitʳ⇒ (u₁ D.∘₁ Fh) D.• D.assoc⇐ u₁ Fh D.id₁
                        D.≈ u₁ D.◁ D.unitʳ⇒ Fh
          unitʳ-slide =
            D.≈-trans (D.•-congˡ (D.unitʳ-∘ u₁ Fh))
            (D.≈-trans D.•-assoc
            (D.≈-trans (D.•-congʳ (D.≅₂isoʳ (D.associator u₁ Fh D.id₁)))
                       D.•-identityʳ))

      main : (rg D.▷ u₀) D.• (R-P g (D.id₁ {y}) D.• W') D.≈ εg D.• Z'
      main = begin
        (rg D.▷ u₀) D.• (R-P g (D.id₁ {y}) D.• W')
          ≈⟨ D.•-congʳ shuffle ⟩
        (rg D.▷ u₀) D.• (P1 D.• (P2 D.• (P3 D.• (P4 D.• (P5 D.• (P6 D.• W'))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ M6))))) ⟩
        (rg D.▷ u₀) D.• (P1 D.• (P2 D.• (P3 D.• (P4 D.• (P5 D.•
          ((u₁ D.◁ (Fh D.◁ F.F₂ ρ)) D.• X'))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ M5)))) ⟩
        (rg D.▷ u₀) D.• (P1 D.• (P2 D.• (P3 D.• (P4 D.•
          (((u₁ D.∘₁ Fh) D.◁ F.F₂ ρ) D.• (D.assoc⇐ u₁ Fh K D.• X'))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ M4))) ⟩
        (rg D.▷ u₀) D.• (P1 D.• (P2 D.• (P3 D.•
          (((g D.∘₁ u₀) D.◁ F.F₂ ρ)
            D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ M3)) ⟩
        (rg D.▷ u₀) D.• (P1 D.• (P2 D.•
          ((g D.◁ (u₀ D.◁ F.F₂ ρ)) D.•
            (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))))
          ≈⟨ D.•-congʳ (D.•-congʳ M2) ⟩
        (rg D.▷ u₀) D.• (P1 D.• ((g D.◁ R-Q) D.•
          (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.◁-• g (D.unitˡ⇐ u₀) (D.unitʳ⇒ u₀ D.• (u₀ D.◁ δ)))
                          (D.•-congʳ (D.◁-• g (D.unitʳ⇒ u₀) (u₀ D.◁ δ)))))) ⟩
        (rg D.▷ u₀) D.• (P1 D.•
          (((g D.◁ D.unitˡ⇐ u₀) D.• ((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ))))
            D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))))
          ≈⟨ D.•-congʳ (D.•-congʳ D.•-assoc) ⟩
        (rg D.▷ u₀) D.• (P1 D.•
          ((g D.◁ D.unitˡ⇐ u₀) D.•
            (((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ)))
              D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        (rg D.▷ u₀) D.• ((P1 D.• (g D.◁ D.unitˡ⇐ u₀)) D.•
          (((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ)))
            D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))))
          ≈⟨ D.•-congʳ (D.•-congˡ (D.triangle⇐ g u₀)) ⟩
        (rg D.▷ u₀) D.• ((D.unitʳ⇐ g D.▷ u₀) D.•
          (((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ)))
            D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((rg D.▷ u₀) D.• (D.unitʳ⇐ g D.▷ u₀)) D.•
          (((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ)))
            D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))
          ≈⟨ D.•-congˡ (D.≈-trans (D.≈-sym (D.▷-• rg (D.unitʳ⇐ g) u₀))
                       (D.≈-trans (D.▷-cong u₀ (D.≅₂isoʳ (D.unitorʳ g)))
                                  (D.▷-id g u₀))) ⟩
        D.id₂ D.•
          (((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ)))
            D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))
          ≈⟨ D.•-identityˡ ⟩
        ((g D.◁ D.unitʳ⇒ u₀) D.• (g D.◁ (u₀ D.◁ δ)))
          D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X')))
          ≈⟨ D.•-assoc ⟩
        (g D.◁ D.unitʳ⇒ u₀) D.• ((g D.◁ (u₀ D.◁ δ))
          D.• (D.assoc⇒ g u₀ K D.• ((εg D.▷ K) D.• (D.assoc⇐ u₁ Fh K D.• X'))))
          ≈⟨ final ⟩
        εg D.• Z' ∎

  ----------------------------------------------------------------------
  -- Associativity coherence of the right biadjoint
  ----------------------------------------------------------------------

  -- R-P is the pasting of two ε-squares, followed by the comparison of F
  R-P-paste : {y y' y'' : D.Obj} (g' : y' D.⇒₁ y'') (g : y D.⇒₁ y') →
              R-P g' g
              D.≈ D-P.paste (u y) (u y') (u y'') (F.F₁ (R₁ g)) (F.F₁ (R₁ g')) g g'
                    (ε (g' D.∘₁ u y')) (ε (g D.∘₁ u y))
                  D.• (u y'' D.◁ F.F-∘⇐ (R₁ g') (R₁ g))
  R-P-paste g' g =
    D.≈-sym (D.≈-trans D.•-assoc (D.•-congʳ
            (D.≈-trans D.•-assoc (D.•-congʳ
            (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc))))))

  -- F's associativity coherence, solved for F₂ of the associator of C
  F₂-assoc : {a b c d : C.Obj} (x : c C.⇒₁ d) (y : b C.⇒₁ c) (z : a C.⇒₁ b) →
             D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z)
               D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z)
             D.≈ (F.F₁ x D.◁ F.F-∘⇐ y z)
                   D.• (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z))
  F₂-assoc x y z = D.Hom.∘-cancelˡ
    (D.Hom.∘-invertible (D.invertible-≅₂ (F.F-∘ x (y C.∘₁ z)))
                        (D.invertible-≅₂ (F.F₁ x D.◁≅ F.F-∘ y z)))
    (begin
      (F.F-∘⇒ x (y C.∘₁ z) D.• (F.F₁ x D.◁ F.F-∘⇒ y z))
        D.• (D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z)
              D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z))
        ≈⟨ D.≈-sym D.•-assoc ⟩
      ((F.F-∘⇒ x (y C.∘₁ z) D.• (F.F₁ x D.◁ F.F-∘⇒ y z))
        D.• D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z))
        D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z)
        ≈⟨ D.•-congˡ (D.≈-trans D.•-assoc (D.≈-sym (F.F-assoc x y z))) ⟩
      (F.F₂ (C.assoc⇒ x y z)
        D.• (F.F-∘⇒ (x C.∘₁ y) z D.• (F.F-∘⇒ x y D.▷ F.F₁ z)))
        D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z)
        ≈⟨ D.•-assoc ⟩
      F.F₂ (C.assoc⇒ x y z) D.•
        ((F.F-∘⇒ (x C.∘₁ y) z D.• (F.F-∘⇒ x y D.▷ F.F₁ z))
          D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z))
        ≈⟨ D.•-congʳ collapse ⟩
      F.F₂ (C.assoc⇒ x y z) D.• D.id₂
        ≈⟨ D.•-identityʳ ⟩
      F.F₂ (C.assoc⇒ x y z)
        ≈⟨ D.≈-sym D.•-identityˡ ⟩
      D.id₂ D.• F.F₂ (C.assoc⇒ x y z)
        ≈⟨ D.•-congˡ (D.≈-sym (D.≅₂isoʳ (F.F-∘ x (y C.∘₁ z)))) ⟩
      (F.F-∘⇒ x (y C.∘₁ z) D.• F.F-∘⇐ x (y C.∘₁ z)) D.• F.F₂ (C.assoc⇒ x y z)
        ≈⟨ D.•-assoc ⟩
      F.F-∘⇒ x (y C.∘₁ z) D.• (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z))
        ≈⟨ D.•-congʳ (D.≈-sym D.•-identityˡ) ⟩
      F.F-∘⇒ x (y C.∘₁ z) D.•
        (D.id₂ D.• (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z)))
        ≈⟨ D.•-congʳ (D.•-congˡ (D.≈-sym
             (D.≈-trans (D.≈-sym (D.◁-• (F.F₁ x) (F.F-∘⇒ y z) (F.F-∘⇐ y z)))
             (D.≈-trans (D.◁-cong (F.F₁ x) (D.≅₂isoʳ (F.F-∘ y z)))
                        (D.◁-id (F.F₁ x) (F.F₁ (y C.∘₁ z))))))) ⟩
      F.F-∘⇒ x (y C.∘₁ z) D.•
        (((F.F₁ x D.◁ F.F-∘⇒ y z) D.• (F.F₁ x D.◁ F.F-∘⇐ y z))
          D.• (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z)))
        ≈⟨ D.•-congʳ D.•-assoc ⟩
      F.F-∘⇒ x (y C.∘₁ z) D.•
        ((F.F₁ x D.◁ F.F-∘⇒ y z) D.• ((F.F₁ x D.◁ F.F-∘⇐ y z)
          D.• (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z))))
        ≈⟨ D.≈-sym D.•-assoc ⟩
      (F.F-∘⇒ x (y C.∘₁ z) D.• (F.F₁ x D.◁ F.F-∘⇒ y z))
        D.• ((F.F₁ x D.◁ F.F-∘⇐ y z)
              D.• (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z))) ∎)
    where
      open D.⇒₂-Reasoning

      collapse : (F.F-∘⇒ (x C.∘₁ y) z D.• (F.F-∘⇒ x y D.▷ F.F₁ z))
                 D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z)
                 D.≈ D.id₂
      collapse = begin
        (F.F-∘⇒ (x C.∘₁ y) z D.• (F.F-∘⇒ x y D.▷ F.F₁ z))
          D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z)
          ≈⟨ D.•-assoc ⟩
        F.F-∘⇒ (x C.∘₁ y) z D.• ((F.F-∘⇒ x y D.▷ F.F₁ z)
          D.• ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        F.F-∘⇒ (x C.∘₁ y) z D.• (((F.F-∘⇒ x y D.▷ F.F₁ z)
          D.• (F.F-∘⇐ x y D.▷ F.F₁ z)) D.• F.F-∘⇐ (x C.∘₁ y) z)
          ≈⟨ D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.≈-sym (D.▷-• (F.F-∘⇒ x y) (F.F-∘⇐ x y) (F.F₁ z)))
               (D.≈-trans (D.▷-cong (F.F₁ z) (D.≅₂isoʳ (F.F-∘ x y)))
                          (D.▷-id (F.F₁ (x C.∘₁ y)) (F.F₁ z))))) ⟩
        F.F-∘⇒ (x C.∘₁ y) z D.• (D.id₂ D.• F.F-∘⇐ (x C.∘₁ y) z)
          ≈⟨ D.•-congʳ D.•-identityˡ ⟩
        F.F-∘⇒ (x C.∘₁ y) z D.• F.F-∘⇐ (x C.∘₁ y) z
          ≈⟨ D.≅₂isoʳ (F.F-∘ (x C.∘₁ y) z) ⟩
        D.id₂ ∎

  -- the associativity coherence of the right biadjoint: both sides are
  -- pastings of the three ε-squares, so paste-assoc applies once the
  -- comparison 2-cells of F have been peeled off
  R-assoc : {y y' y'' y3 : D.Obj}
            (f : y'' D.⇒₁ y3) (g : y' D.⇒₁ y'') (h : y D.⇒₁ y') →
            (R₂ (D.assoc⇒ f g h) C.• (R-∘⇒ (f D.∘₁ g) h C.• (R-∘⇒ f g C.▷ R₁ h)))
            C.≈ (R-∘⇒ f (g D.∘₁ h) C.•
                  ((R₁ f C.◁ R-∘⇒ g h) C.• C.assoc⇒ (R₁ f) (R₁ g) (R₁ h)))
  R-assoc {y} {y'} {y''} {y3} f g h = ⇑₂-cancel (begin
    ε₀ D.• w (R₂ (D.assoc⇒ f g h) C.• (R-∘⇒ (f D.∘₁ g) h C.• (R-∘⇒ f g C.▷ H)))
      ≈⟨ peelL ⟩
    (D.assoc⇒ f g h D.▷ u₀) D.• (R-P (f D.∘₁ g) h D.• WL)
      ≈⟨ mainL ⟩
    Q D.• tailL
      ≈⟨ D.•-congʳ tails ⟩
    Q D.• tailR
      ≈⟨ D.≈-sym mainR ⟩
    R-P f (g D.∘₁ h) D.• (WR D.• WA)
      ≈⟨ D.≈-sym peelR ⟩
    ε₀ D.• w (R-∘⇒ f (g D.∘₁ h) C.• ((A C.◁ R-∘⇒ g h) C.• C.assoc⇒ A B H)) ∎)
    where
      open D.⇒₂-Reasoning

      u₀ = u y
      u₁ = u y'
      u₂ = u y''
      u₃ = u y3
      A  = R₁ f
      B  = R₁ g
      H  = R₁ h
      FA = F.F₁ A
      FB = F.F₁ B
      FH = F.F₁ H
      εf  = ε (f D.∘₁ u₂)
      εg  = ε (g D.∘₁ u₁)
      εh  = ε (h D.∘₁ u₀)
      εfg = ε ((f D.∘₁ g) D.∘₁ u₁)
      εgh = ε ((g D.∘₁ h) D.∘₁ u₀)
      ε₀  = ε ((f D.∘₁ (g D.∘₁ h)) D.∘₁ u₀)

      WL = w (R-∘⇒ f g C.▷ H)
      WR = w (A C.◁ R-∘⇒ g h)
      WA = w (C.assoc⇒ A B H)

      Y  = u₃ D.◁ F.F-∘⇐ (A C.∘₁ B) H
      pfg = D-P.paste u₁ u₂ u₃ FB FA g f εf εg
      pgh = D-P.paste u₀ u₁ u₂ FH FB h g εg εh
      Q   = D-P.paste u₀ u₂ u₃ (FB D.∘₁ FH) FA (g D.∘₁ h) f εf pgh

      tailL = (u₃ D.◁ D.assoc⇒ FA FB FH) D.•
                ((u₃ D.◁ (F.F-∘⇐ A B D.▷ FH)) D.• Y)
      tailR = (u₃ D.◁ (FA D.◁ F.F-∘⇐ B H)) D.•
                ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA)

      peelL : ε₀ D.• w (R₂ (D.assoc⇒ f g h)
                C.• (R-∘⇒ (f D.∘₁ g) h C.• (R-∘⇒ f g C.▷ H)))
              D.≈ (D.assoc⇒ f g h D.▷ u₀) D.• (R-P (f D.∘₁ g) h D.• WL)
      peelL =
        D.≈-trans (D.•-congʳ (w-• (R₂ (D.assoc⇒ f g h))
                                  (R-∘⇒ (f D.∘₁ g) h C.• (R-∘⇒ f g C.▷ H))))
        (D.≈-trans (D.≈-sym D.•-assoc)
        (D.≈-trans (D.•-congˡ (R₂-β (D.assoc⇒ f g h)))
        (D.≈-trans D.•-assoc
        (D.≈-trans (D.•-congʳ (D.•-congʳ (w-• (R-∘⇒ (f D.∘₁ g) h)
                                              (R-∘⇒ f g C.▷ H))))
        (D.≈-trans (D.•-congʳ (D.≈-sym D.•-assoc))
                   (D.•-congʳ (D.•-congˡ (⇑₂-β (R-P (f D.∘₁ g) h)))))))))

      peelR : ε₀ D.• w (R-∘⇒ f (g D.∘₁ h)
                C.• ((A C.◁ R-∘⇒ g h) C.• C.assoc⇒ A B H))
              D.≈ R-P f (g D.∘₁ h) D.• (WR D.• WA)
      peelR =
        D.≈-trans (D.•-congʳ (w-• (R-∘⇒ f (g D.∘₁ h))
                                  ((A C.◁ R-∘⇒ g h) C.• C.assoc⇒ A B H)))
        (D.≈-trans (D.≈-sym D.•-assoc)
        (D.≈-trans (D.•-congˡ (⇑₂-β (R-P f (g D.∘₁ h))))
                   (D.•-congʳ (w-• (A C.◁ R-∘⇒ g h) (C.assoc⇒ A B H)))))

      LA : (u₃ D.◁ F.F-∘⇐ (R₁ (f D.∘₁ g)) H) D.• WL
           D.≈ (u₃ D.◁ (F.F₂ (R-∘⇒ f g) D.▷ FH)) D.• Y
      LA = D.≈-trans (D.≈-sym (D.◁-• u₃ (F.F-∘⇐ (R₁ (f D.∘₁ g)) H)
                                        (F.F₂ (R-∘⇒ f g C.▷ H))))
           (D.≈-trans (D.◁-cong u₃ (F.F-∘-natural⇐ (R-∘⇒ f g) (C.id₂ {f = H})))
           (D.≈-trans (D.◁-• u₃ (F.F₂ (R-∘⇒ f g) D.∗ F.F₂ (C.id₂ {f = H}))
                                (F.F-∘⇐ (A C.∘₁ B) H))
                      (D.•-congˡ (D.◁-cong u₃ (D.∗-cong D.≈-refl F.F₂-id₂)))))

      RA : (u₃ D.◁ F.F-∘⇐ A (R₁ (g D.∘₁ h))) D.• WR
           D.≈ (u₃ D.◁ (FA D.◁ F.F₂ (R-∘⇒ g h)))
                 D.• (u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H))
      RA = D.≈-trans (D.≈-sym (D.◁-• u₃ (F.F-∘⇐ A (R₁ (g D.∘₁ h)))
                                        (F.F₂ (A C.◁ R-∘⇒ g h))))
           (D.≈-trans (D.◁-cong u₃ (F.F-∘-natural⇐ (C.id₂ {f = A}) (R-∘⇒ g h)))
           (D.≈-trans (D.◁-• u₃ (F.F₂ (C.id₂ {f = A}) D.∗ F.F₂ (R-∘⇒ g h))
                                (F.F-∘⇐ A (B C.∘₁ H)))
                      (D.•-congˡ (D.◁-cong u₃ (D.∗-cong F.F₂-id₂ D.≈-refl)))))

      mainL : (D.assoc⇒ f g h D.▷ u₀) D.• (R-P (f D.∘₁ g) h D.• WL)
              D.≈ Q D.• tailL
      mainL = begin
        (D.assoc⇒ f g h D.▷ u₀) D.• (R-P (f D.∘₁ g) h D.• WL)
          ≈⟨ D.•-congʳ (D.•-congˡ (R-P-paste (f D.∘₁ g) h)) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          ((D-P.paste u₀ u₁ u₃ FH (F.F₁ (R₁ (f D.∘₁ g))) h (f D.∘₁ g) εfg εh
            D.• (u₃ D.◁ F.F-∘⇐ (R₁ (f D.∘₁ g)) H)) D.• WL)
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          (D-P.paste u₀ u₁ u₃ FH (F.F₁ (R₁ (f D.∘₁ g))) h (f D.∘₁ g) εfg εh
            D.• ((u₃ D.◁ F.F-∘⇐ (R₁ (f D.∘₁ g)) H) D.• WL))
          ≈⟨ D.•-congʳ (D.•-congʳ LA) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          (D-P.paste u₀ u₁ u₃ FH (F.F₁ (R₁ (f D.∘₁ g))) h (f D.∘₁ g) εfg εh
            D.• ((u₃ D.◁ (F.F₂ (R-∘⇒ f g) D.▷ FH)) D.• Y))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          ((D-P.paste u₀ u₁ u₃ FH (F.F₁ (R₁ (f D.∘₁ g))) h (f D.∘₁ g) εfg εh
            D.• (u₃ D.◁ (F.F₂ (R-∘⇒ f g) D.▷ FH))) D.• Y)
          ≈⟨ D.•-congʳ (D.•-congˡ (D-P.paste-▷ u₀ u₁ u₃ FH
                (F.F₁ (R₁ (f D.∘₁ g))) (F.F₁ (A C.∘₁ B)) h (f D.∘₁ g)
                εfg εh (F.F₂ (R-∘⇒ f g)))) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          ((D-P.paste u₀ u₁ u₃ FH (F.F₁ (A C.∘₁ B)) h (f D.∘₁ g)
             (εfg D.• (u₃ D.◁ F.F₂ (R-∘⇒ f g))) εh) D.• Y)
          ≈⟨ D.•-congʳ (D.•-congˡ (D-P.paste-cong u₀ u₁ u₃ FH (F.F₁ (A C.∘₁ B))
                h (f D.∘₁ g) (⇑₂-β (R-P f g)) D.≈-refl)) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          ((D-P.paste u₀ u₁ u₃ FH (F.F₁ (A C.∘₁ B)) h (f D.∘₁ g) (R-P f g) εh) D.• Y)
          ≈⟨ D.•-congʳ (D.•-congˡ (D-P.paste-cong u₀ u₁ u₃ FH (F.F₁ (A C.∘₁ B))
                h (f D.∘₁ g) (R-P-paste f g) D.≈-refl)) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          ((D-P.paste u₀ u₁ u₃ FH (F.F₁ (A C.∘₁ B)) h (f D.∘₁ g)
             (pfg D.• (u₃ D.◁ F.F-∘⇐ A B)) εh) D.• Y)
          ≈⟨ D.•-congʳ (D.•-congˡ (D.≈-sym (D-P.paste-▷ u₀ u₁ u₃ FH
                (FA D.∘₁ FB) (F.F₁ (A C.∘₁ B)) h (f D.∘₁ g)
                pfg εh (F.F-∘⇐ A B)))) ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          ((D-P.paste u₀ u₁ u₃ FH (FA D.∘₁ FB) h (f D.∘₁ g) pfg εh
            D.• (u₃ D.◁ (F.F-∘⇐ A B D.▷ FH))) D.• Y)
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (D.assoc⇒ f g h D.▷ u₀) D.•
          (D-P.paste u₀ u₁ u₃ FH (FA D.∘₁ FB) h (f D.∘₁ g) pfg εh
            D.• ((u₃ D.◁ (F.F-∘⇐ A B D.▷ FH)) D.• Y))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((D.assoc⇒ f g h D.▷ u₀) D.•
          D-P.paste u₀ u₁ u₃ FH (FA D.∘₁ FB) h (f D.∘₁ g) pfg εh)
          D.• ((u₃ D.◁ (F.F-∘⇐ A B D.▷ FH)) D.• Y)
          ≈⟨ D.•-congˡ (D-P.paste-assoc u₀ u₁ u₂ u₃ FH FB FA h g f εf εg εh) ⟩
        (Q D.• (u₃ D.◁ D.assoc⇒ FA FB FH))
          D.• ((u₃ D.◁ (F.F-∘⇐ A B D.▷ FH)) D.• Y)
          ≈⟨ D.•-assoc ⟩
        Q D.• tailL ∎

      mainR : R-P f (g D.∘₁ h) D.• (WR D.• WA) D.≈ Q D.• tailR
      mainR = begin
        R-P f (g D.∘₁ h) D.• (WR D.• WA)
          ≈⟨ D.•-congˡ (R-P-paste f (g D.∘₁ h)) ⟩
        (D-P.paste u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h))) FA (g D.∘₁ h) f εf εgh
          D.• (u₃ D.◁ F.F-∘⇐ A (R₁ (g D.∘₁ h)))) D.• (WR D.• WA)
          ≈⟨ D.•-assoc ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h))) FA (g D.∘₁ h) f εf εgh
          D.• ((u₃ D.◁ F.F-∘⇐ A (R₁ (g D.∘₁ h))) D.• (WR D.• WA))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h))) FA (g D.∘₁ h) f εf εgh
          D.• (((u₃ D.◁ F.F-∘⇐ A (R₁ (g D.∘₁ h))) D.• WR) D.• WA)
          ≈⟨ D.•-congʳ (D.•-congˡ RA) ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h))) FA (g D.∘₁ h) f εf εgh
          D.• (((u₃ D.◁ (FA D.◁ F.F₂ (R-∘⇒ g h)))
                D.• (u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H))) D.• WA)
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h))) FA (g D.∘₁ h) f εf εgh
          D.• ((u₃ D.◁ (FA D.◁ F.F₂ (R-∘⇒ g h)))
                D.• ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D-P.paste u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h))) FA (g D.∘₁ h) f εf εgh
          D.• (u₃ D.◁ (FA D.◁ F.F₂ (R-∘⇒ g h))))
          D.• ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA)
          ≈⟨ D.•-congˡ (D-P.paste-◁ u₀ u₂ u₃ (F.F₁ (R₁ (g D.∘₁ h)))
                (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f εf εgh (F.F₂ (R-∘⇒ g h))) ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f εf
          (εgh D.• (u₂ D.◁ F.F₂ (R-∘⇒ g h)))
          D.• ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA)
          ≈⟨ D.•-congˡ (D-P.paste-cong u₀ u₂ u₃ (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f
                D.≈-refl (⇑₂-β (R-P g h))) ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f εf (R-P g h)
          D.• ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA)
          ≈⟨ D.•-congˡ (D-P.paste-cong u₀ u₂ u₃ (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f
                D.≈-refl (R-P-paste g h)) ⟩
        D-P.paste u₀ u₂ u₃ (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f εf
          (pgh D.• (u₂ D.◁ F.F-∘⇐ B H))
          D.• ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA)
          ≈⟨ D.•-congˡ (D.≈-sym (D-P.paste-◁ u₀ u₂ u₃ (FB D.∘₁ FH)
                (F.F₁ (B C.∘₁ H)) FA (g D.∘₁ h) f εf pgh (F.F-∘⇐ B H))) ⟩
        (Q D.• (u₃ D.◁ (FA D.◁ F.F-∘⇐ B H)))
          D.• ((u₃ D.◁ F.F-∘⇐ A (B C.∘₁ H)) D.• WA)
          ≈⟨ D.•-assoc ⟩
        Q D.• tailR ∎

      tails : tailL D.≈ tailR
      tails = begin
        tailL
          ≈⟨ D.•-congʳ (D.≈-sym (D.◁-• u₃ (F.F-∘⇐ A B D.▷ FH)
                                          (F.F-∘⇐ (A C.∘₁ B) H))) ⟩
        (u₃ D.◁ D.assoc⇒ FA FB FH)
          D.• (u₃ D.◁ ((F.F-∘⇐ A B D.▷ FH) D.• F.F-∘⇐ (A C.∘₁ B) H))
          ≈⟨ D.≈-sym (D.◁-• u₃ (D.assoc⇒ FA FB FH)
                               ((F.F-∘⇐ A B D.▷ FH) D.• F.F-∘⇐ (A C.∘₁ B) H)) ⟩
        u₃ D.◁ (D.assoc⇒ FA FB FH
                 D.• ((F.F-∘⇐ A B D.▷ FH) D.• F.F-∘⇐ (A C.∘₁ B) H))
          ≈⟨ D.◁-cong u₃ (F₂-assoc A B H) ⟩
        u₃ D.◁ ((FA D.◁ F.F-∘⇐ B H)
                 D.• (F.F-∘⇐ A (B C.∘₁ H) D.• F.F₂ (C.assoc⇒ A B H)))
          ≈⟨ D.◁-• u₃ (FA D.◁ F.F-∘⇐ B H)
                      (F.F-∘⇐ A (B C.∘₁ H) D.• F.F₂ (C.assoc⇒ A B H)) ⟩
        (u₃ D.◁ (FA D.◁ F.F-∘⇐ B H))
          D.• (u₃ D.◁ (F.F-∘⇐ A (B C.∘₁ H) D.• F.F₂ (C.assoc⇒ A B H)))
          ≈⟨ D.•-congʳ (D.◁-• u₃ (F.F-∘⇐ A (B C.∘₁ H))
                                 (F.F₂ (C.assoc⇒ A B H))) ⟩
        tailR ∎

  ----------------------------------------------------------------------
  -- The right biadjoint
  ----------------------------------------------------------------------

  -- R is a bifunctor: its data is the universal one, and each of the
  -- four coherence axioms is the corresponding coherence of F, read
  -- through the universal property
  R : Bifunctor D C
  R = record
    { F₀          = R₀
    ; Fhom        = Rhom
    ; F-∘         = R-∘
    ; F-id        = R-id
    ; F-∘-natural = R-∘-natural
    ; F-assoc     = R-assoc
    ; F-unitˡ     = R-unitˡ
    ; F-unitʳ     = R-unitʳ
    }

  ----------------------------------------------------------------------
  -- Naturality of the transposition in each variable
  ----------------------------------------------------------------------

  -- ε read through the action of the transposition on 2-cells
  Φ₂-β : {x : C.Obj} {y : D.Obj} {f f' : F.F₀ x D.⇒₁ y} (γ : f D.⇒₂ f') →
         ε f' D.• w (Φ₂ γ) D.≈ γ D.• ε f
  Φ₂-β {f = f} γ = ⇑₂-β (γ D.• ε f)

  -- the comparison for precomposition, ⇑₁ (k ∘ F f) ≅ ⇑₁ k ∘ f
  Pˡ : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj} (k : F.F₀ x D.⇒₁ y) →
       (u y D.∘₁ F.F₁ (⇑₁ k C.∘₁ f)) D.⇒₂ (k D.∘₁ F.F₁ f)
  Pˡ f {y} k = (ε k D.▷ F.F₁ f) D.•
               (D.assoc⇐ (u y) (F.F₁ (⇑₁ k)) (F.F₁ f) D.•
                 (u y D.◁ F.F-∘⇐ (⇑₁ k) f))

  Pˡ-inv : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj} (k : F.F₀ x D.⇒₁ y) →
           D.Invertible₂ (Pˡ f k)
  Pˡ-inv f {y} k =
    D.Hom.∘-invertible (▷-inv (F.F₁ f) (ε-invertible k))
    (D.Hom.∘-invertible (assoc⇐-inv (u y) (F.F₁ (⇑₁ k)) (F.F₁ f))
                        (◁-inv (u y) (F-∘⇐-inv (⇑₁ k) f)))

  Φ-natˡ⇐ : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj} (k : F.F₀ x D.⇒₁ y) →
            (⇑₁ k C.∘₁ f) C.⇒₂ ⇑₁ (k D.∘₁ F.F₁ f)
  Φ-natˡ⇐ f k = ⇑₂ (Pˡ f k)

  Φ-natˡ-inv : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj} (k : F.F₀ x D.⇒₁ y) →
               C.Invertible₂ (Φ-natˡ⇐ f k)
  Φ-natˡ-inv f k = ⇑₂-invertible (Pˡ-inv f k)

  Φ-natˡ⇒ : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj} (k : F.F₀ x D.⇒₁ y) →
            ⇑₁ (k D.∘₁ F.F₁ f) C.⇒₂ (⇑₁ k C.∘₁ f)
  Φ-natˡ⇒ f k = C.Hom.inv (Φ-natˡ-inv f k)

  -- the comparison for postcomposition, ⇑₁ (g ∘ k) ≅ R g ∘ ⇑₁ k
  Pʳ : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y') (k : F.F₀ x D.⇒₁ y) →
       (u y' D.∘₁ F.F₁ (R₁ g C.∘₁ ⇑₁ k)) D.⇒₂ (g D.∘₁ k)
  Pʳ {y = y} {y' = y'} g k =
    (g D.◁ ε k) D.•
    (D.assoc⇒ g (u y) (F.F₁ (⇑₁ k)) D.•
      ((ε (g D.∘₁ u y) D.▷ F.F₁ (⇑₁ k)) D.•
        (D.assoc⇐ (u y') (F.F₁ (R₁ g)) (F.F₁ (⇑₁ k)) D.•
          (u y' D.◁ F.F-∘⇐ (R₁ g) (⇑₁ k)))))

  Pʳ-inv : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y') (k : F.F₀ x D.⇒₁ y) →
           D.Invertible₂ (Pʳ g k)
  Pʳ-inv {y = y} {y' = y'} g k =
    D.Hom.∘-invertible (◁-inv g (ε-invertible k))
    (D.Hom.∘-invertible (assoc⇒-inv g (u y) (F.F₁ (⇑₁ k)))
    (D.Hom.∘-invertible (▷-inv (F.F₁ (⇑₁ k)) (ε-invertible (g D.∘₁ u y)))
    (D.Hom.∘-invertible (assoc⇐-inv (u y') (F.F₁ (R₁ g)) (F.F₁ (⇑₁ k)))
                        (◁-inv (u y') (F-∘⇐-inv (R₁ g) (⇑₁ k))))))

  Φ-natʳ⇐ : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y') (k : F.F₀ x D.⇒₁ y) →
            (R₁ g C.∘₁ ⇑₁ k) C.⇒₂ ⇑₁ (g D.∘₁ k)
  Φ-natʳ⇐ g k = ⇑₂ (Pʳ g k)

  Φ-natʳ-inv : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y') (k : F.F₀ x D.⇒₁ y) →
               C.Invertible₂ (Φ-natʳ⇐ g k)
  Φ-natʳ-inv g k = ⇑₂-invertible (Pʳ-inv g k)

  Φ-natʳ⇒ : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y') (k : F.F₀ x D.⇒₁ y) →
            ⇑₁ (g D.∘₁ k) C.⇒₂ (R₁ g C.∘₁ ⇑₁ k)
  Φ-natʳ⇒ g k = C.Hom.inv (Φ-natʳ-inv g k)

  ----------------------------------------------------------------------
  -- …is natural in the 2-cells of the hom-categories
  ----------------------------------------------------------------------

  Φ-natˡ-natural : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj}
                   {k k' : F.F₀ x D.⇒₁ y} (β : k D.⇒₂ k') →
                   Φ-natˡ⇐ f k' C.• (Φ₂ β C.▷ f)
                   C.≈ Φ₂ (β D.▷ F.F₁ f) C.• Φ-natˡ⇐ f k
  Φ-natˡ-natural {x} {x'} f {y} {k} {k'} β = ⇑₂-cancel (begin
    ε (k' D.∘₁ F.F₁ f) D.• w (Φ-natˡ⇐ f k' C.• (Φ₂ β C.▷ f))
      ≈⟨ D.•-congʳ (w-• (Φ-natˡ⇐ f k') (Φ₂ β C.▷ f)) ⟩
    ε (k' D.∘₁ F.F₁ f) D.• (w (Φ-natˡ⇐ f k') D.• w (Φ₂ β C.▷ f))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (ε (k' D.∘₁ F.F₁ f) D.• w (Φ-natˡ⇐ f k')) D.• w (Φ₂ β C.▷ f)
      ≈⟨ D.•-congˡ (⇑₂-β (Pˡ f k')) ⟩
    Pˡ f k' D.• w (Φ₂ β C.▷ f)
      ≈⟨ mid ⟩
    (β D.▷ F.F₁ f) D.• Pˡ f k
      ≈⟨ D.•-congʳ (D.≈-sym (⇑₂-β (Pˡ f k))) ⟩
    (β D.▷ F.F₁ f) D.• (ε (k D.∘₁ F.F₁ f) D.• w (Φ-natˡ⇐ f k))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    ((β D.▷ F.F₁ f) D.• ε (k D.∘₁ F.F₁ f)) D.• w (Φ-natˡ⇐ f k)
      ≈⟨ D.•-congˡ (D.≈-sym (Φ₂-β (β D.▷ F.F₁ f))) ⟩
    (ε (k' D.∘₁ F.F₁ f) D.• w (Φ₂ (β D.▷ F.F₁ f))) D.• w (Φ-natˡ⇐ f k)
      ≈⟨ D.•-assoc ⟩
    ε (k' D.∘₁ F.F₁ f) D.• (w (Φ₂ (β D.▷ F.F₁ f)) D.• w (Φ-natˡ⇐ f k))
      ≈⟨ D.•-congʳ (D.≈-sym (w-• (Φ₂ (β D.▷ F.F₁ f)) (Φ-natˡ⇐ f k))) ⟩
    ε (k' D.∘₁ F.F₁ f) D.• w (Φ₂ (β D.▷ F.F₁ f) C.• Φ-natˡ⇐ f k) ∎)
    where
      open D.⇒₂-Reasoning

      mid : Pˡ f k' D.• w (Φ₂ β C.▷ f) D.≈ (β D.▷ F.F₁ f) D.• Pˡ f k
      mid = begin
        Pˡ f k' D.• w (Φ₂ β C.▷ f)
          ≈⟨ D.•-assoc ⟩
        (ε k' D.▷ F.F₁ f) D.•
          ((D.assoc⇐ (u y) (F.F₁ (⇑₁ k')) (F.F₁ f) D.•
            (u y D.◁ F.F-∘⇐ (⇑₁ k') f)) D.• w (Φ₂ β C.▷ f))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (ε k' D.▷ F.F₁ f) D.•
          (D.assoc⇐ (u y) (F.F₁ (⇑₁ k')) (F.F₁ f) D.•
            ((u y D.◁ F.F-∘⇐ (⇑₁ k') f) D.• w (Φ₂ β C.▷ f)))
          ≈⟨ D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym (D.◁-• (u y) (F.F-∘⇐ (⇑₁ k') f)
                                          (F.F₂ (Φ₂ β C.▷ f))))
               (D.≈-trans (D.◁-cong (u y)
                            (F.F-∘-natural⇐ (Φ₂ β) (C.id₂ {f = f})))
               (D.≈-trans (D.◁-• (u y) (F.F₂ (Φ₂ β) D.∗ F.F₂ (C.id₂ {f = f}))
                                 (F.F-∘⇐ (⇑₁ k) f))
                          (D.•-congˡ (D.◁-cong (u y)
                            (D.∗-cong D.≈-refl F.F₂-id₂))))))) ⟩
        (ε k' D.▷ F.F₁ f) D.•
          (D.assoc⇐ (u y) (F.F₁ (⇑₁ k')) (F.F₁ f) D.•
            ((u y D.◁ (F.F₂ (Φ₂ β) D.▷ F.F₁ f)) D.•
              (u y D.◁ F.F-∘⇐ (⇑₁ k) f)))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        (ε k' D.▷ F.F₁ f) D.•
          ((D.assoc⇐ (u y) (F.F₁ (⇑₁ k')) (F.F₁ f) D.•
            (u y D.◁ (F.F₂ (Φ₂ β) D.▷ F.F₁ f))) D.•
              (u y D.◁ F.F-∘⇐ (⇑₁ k) f))
          ≈⟨ D.•-congʳ (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = u y})
                                    (F.F₂ (Φ₂ β)) (D.id₂ {f = F.F₁ f}))) ⟩
        (ε k' D.▷ F.F₁ f) D.•
          ((((u y D.◁ F.F₂ (Φ₂ β)) D.▷ F.F₁ f) D.•
            D.assoc⇐ (u y) (F.F₁ (⇑₁ k)) (F.F₁ f)) D.•
              (u y D.◁ F.F-∘⇐ (⇑₁ k) f))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (ε k' D.▷ F.F₁ f) D.•
          (((u y D.◁ F.F₂ (Φ₂ β)) D.▷ F.F₁ f) D.•
            (D.assoc⇐ (u y) (F.F₁ (⇑₁ k)) (F.F₁ f) D.•
              (u y D.◁ F.F-∘⇐ (⇑₁ k) f)))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((ε k' D.▷ F.F₁ f) D.• ((u y D.◁ F.F₂ (Φ₂ β)) D.▷ F.F₁ f)) D.•
          (D.assoc⇐ (u y) (F.F₁ (⇑₁ k)) (F.F₁ f) D.•
            (u y D.◁ F.F-∘⇐ (⇑₁ k) f))
          ≈⟨ D.•-congˡ (D.≈-trans (D.≈-sym (D.▷-• (ε k') (w (Φ₂ β)) (F.F₁ f)))
                       (D.≈-trans (D.▷-cong (F.F₁ f) (Φ₂-β β))
                                  (D.▷-• β (ε k) (F.F₁ f)))) ⟩
        ((β D.▷ F.F₁ f) D.• (ε k D.▷ F.F₁ f)) D.•
          (D.assoc⇐ (u y) (F.F₁ (⇑₁ k)) (F.F₁ f) D.•
            (u y D.◁ F.F-∘⇐ (⇑₁ k) f))
          ≈⟨ D.•-assoc ⟩
        (β D.▷ F.F₁ f) D.• Pˡ f k ∎

  Φ-natʳ-natural : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y')
                   {k k' : F.F₀ x D.⇒₁ y} (β : k D.⇒₂ k') →
                   Φ-natʳ⇐ g k' C.• (R₁ g C.◁ Φ₂ β)
                   C.≈ Φ₂ (g D.◁ β) C.• Φ-natʳ⇐ g k
  Φ-natʳ-natural {x} {y} {y'} g {k} {k'} β = ⇑₂-cancel (begin
    ε (g D.∘₁ k') D.• w (Φ-natʳ⇐ g k' C.• (R₁ g C.◁ Φ₂ β))
      ≈⟨ D.•-congʳ (w-• (Φ-natʳ⇐ g k') (R₁ g C.◁ Φ₂ β)) ⟩
    ε (g D.∘₁ k') D.• (w (Φ-natʳ⇐ g k') D.• W)
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (ε (g D.∘₁ k') D.• w (Φ-natʳ⇐ g k')) D.• W
      ≈⟨ D.•-congˡ (⇑₂-β (Pʳ g k')) ⟩
    Pʳ g k' D.• W
      ≈⟨ mid ⟩
    (g D.◁ β) D.• Pʳ g k
      ≈⟨ D.•-congʳ (D.≈-sym (⇑₂-β (Pʳ g k))) ⟩
    (g D.◁ β) D.• (ε (g D.∘₁ k) D.• w (Φ-natʳ⇐ g k))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    ((g D.◁ β) D.• ε (g D.∘₁ k)) D.• w (Φ-natʳ⇐ g k)
      ≈⟨ D.•-congˡ (D.≈-sym (Φ₂-β (g D.◁ β))) ⟩
    (ε (g D.∘₁ k') D.• w (Φ₂ (g D.◁ β))) D.• w (Φ-natʳ⇐ g k)
      ≈⟨ D.•-assoc ⟩
    ε (g D.∘₁ k') D.• (w (Φ₂ (g D.◁ β)) D.• w (Φ-natʳ⇐ g k))
      ≈⟨ D.•-congʳ (D.≈-sym (w-• (Φ₂ (g D.◁ β)) (Φ-natʳ⇐ g k))) ⟩
    ε (g D.∘₁ k') D.• w (Φ₂ (g D.◁ β) C.• Φ-natʳ⇐ g k) ∎)
    where
      open D.⇒₂-Reasoning

      uy  = u y
      uy' = u y'
      Rg  = R₁ g
      FRg = F.F₁ (R₁ g)
      K   = F.F₁ (⇑₁ k)
      K'  = F.F₁ (⇑₁ k')
      b   = F.F₂ (Φ₂ β)
      εgu = ε (g D.∘₁ uy)
      W   = w (Rg C.◁ Φ₂ β)
      X'  = uy' D.◁ F.F-∘⇐ Rg (⇑₁ k)

      shuffle : Pʳ g k' D.• W
                D.≈ (g D.◁ ε k') D.• (D.assoc⇒ g uy K' D.• ((εgu D.▷ K') D.•
                      (D.assoc⇐ uy' FRg K' D.•
                        ((uy' D.◁ F.F-∘⇐ Rg (⇑₁ k')) D.• W))))
      shuffle = D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ
                (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc)))))

      N6 : (uy' D.◁ F.F-∘⇐ Rg (⇑₁ k')) D.• W D.≈ (uy' D.◁ (FRg D.◁ b)) D.• X'
      N6 = D.≈-trans (D.≈-sym (D.◁-• uy' (F.F-∘⇐ Rg (⇑₁ k'))
                                         (F.F₂ (Rg C.◁ Φ₂ β))))
           (D.≈-trans (D.◁-cong uy' (F.F-∘-natural⇐ (C.id₂ {f = Rg}) (Φ₂ β)))
           (D.≈-trans (D.◁-• uy' (F.F₂ (C.id₂ {f = Rg}) D.∗ b)
                                 (F.F-∘⇐ Rg (⇑₁ k)))
                      (D.•-congˡ (D.◁-cong uy' (D.∗-cong F.F₂-id₂ D.≈-refl)))))

      N5 : D.assoc⇐ uy' FRg K' D.• ((uy' D.◁ (FRg D.◁ b)) D.• X')
           D.≈ ((uy' D.∘₁ FRg) D.◁ b) D.• (D.assoc⇐ uy' FRg K D.• X')
      N5 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = uy'}) (D.id₂ {f = FRg}) b)
                        (D.•-congˡ (D.∗-cong (D.∗-id uy' FRg) D.≈-refl))))
                      D.•-assoc)

      N4 : (εgu D.▷ K') D.• (((uy' D.∘₁ FRg) D.◁ b) D.• (D.assoc⇐ uy' FRg K D.• X'))
           D.≈ ((g D.∘₁ uy) D.◁ b) D.• ((εgu D.▷ K) D.• (D.assoc⇐ uy' FRg K D.• X'))
      N4 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.≈-sym (D.∗-• εgu (D.id₂ {f = uy' D.∘₁ FRg})
                                            (D.id₂ {f = K'}) b))
             (D.≈-trans (D.∗-cong D.•-identityʳ D.•-identityˡ)
                        (D.∗-decomposeʳ εgu b))))
                      D.•-assoc)

      N3 : D.assoc⇒ g uy K' D.• (((g D.∘₁ uy) D.◁ b) D.•
             ((εgu D.▷ K) D.• (D.assoc⇐ uy' FRg K D.• X')))
           D.≈ (g D.◁ (uy D.◁ b)) D.• (D.assoc⇒ g uy K D.•
             ((εgu D.▷ K) D.• (D.assoc⇐ uy' FRg K D.• X')))
      N3 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-sym (D.≈-trans (D.assoc-natural (D.id₂ {f = g}) (D.id₂ {f = uy}) b)
                                 (D.•-congʳ (D.∗-cong (D.∗-id g uy) D.≈-refl)))))
                      D.•-assoc)

      N2 : (g D.◁ ε k') D.• ((g D.◁ (uy D.◁ b)) D.• (D.assoc⇒ g uy K D.•
             ((εgu D.▷ K) D.• (D.assoc⇐ uy' FRg K D.• X'))))
           D.≈ (g D.◁ β) D.• Pʳ g k
      N2 = D.≈-trans (D.≈-sym D.•-assoc)
           (D.≈-trans (D.•-congˡ
             (D.≈-trans (D.≈-sym (D.◁-• g (ε k') (uy D.◁ b)))
             (D.≈-trans (D.◁-cong g (Φ₂-β β)) (D.◁-• g β (ε k)))))
                      D.•-assoc)

      mid : Pʳ g k' D.• W D.≈ (g D.◁ β) D.• Pʳ g k
      mid = D.≈-trans shuffle
            (D.≈-trans (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ N6))))
            (D.≈-trans (D.•-congʳ (D.•-congʳ (D.•-congʳ N5)))
            (D.≈-trans (D.•-congʳ (D.•-congʳ N4))
            (D.≈-trans (D.•-congʳ N3) N2))))

  -- naturality of the comparisons in the ⇒ direction, read off from
  -- the ⇐ direction through Hom.≅-natural
  Φ-natˡ-natural⇒ : {x x' : C.Obj} (f : x' C.⇒₁ x) {y : D.Obj}
                    {k k' : F.F₀ x D.⇒₁ y} (β : k D.⇒₂ k') →
                    Φ-natˡ⇒ f k' C.• Φ₂ (β D.▷ F.F₁ f)
                    C.≈ (Φ₂ β C.▷ f) C.• Φ-natˡ⇒ f k
  Φ-natˡ-natural⇒ f {k = k} {k' = k'} β =
    C.Hom.≅-natural (C.Hom.≅-invertible (Φ-natˡ-inv f k))
                    (C.Hom.≅-invertible (Φ-natˡ-inv f k'))
                    (Φ₂ β C.▷ f) (Φ₂ (β D.▷ F.F₁ f))
                    (C.≈-sym (Φ-natˡ-natural f β))

  Φ-natʳ-natural⇒ : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y')
                    {k k' : F.F₀ x D.⇒₁ y} (β : k D.⇒₂ k') →
                    Φ-natʳ⇒ g k' C.• Φ₂ (g D.◁ β)
                    C.≈ (R₁ g C.◁ Φ₂ β) C.• Φ-natʳ⇒ g k
  Φ-natʳ-natural⇒ g {k = k} {k' = k'} β =
    C.Hom.≅-natural (C.Hom.≅-invertible (Φ-natʳ-inv g k))
                    (C.Hom.≅-invertible (Φ-natʳ-inv g k'))
                    (R₁ g C.◁ Φ₂ β) (Φ₂ (g D.◁ β))
                    (C.≈-sym (Φ-natʳ-natural g β))

  -- the two comparisons, as natural isomorphisms in the functor

  -- categories, in the direction the biadjunction expects
  Φ-naturalˡ : {x x' : C.Obj} (f : x' C.⇒₁ x) (y : D.Obj) →
               (Φ x' y ∘F D.precomp (F.F₁ f)) ≅N (C.precomp f ∘F Φ x y)
  Φ-naturalˡ f y =
    mk≅N (record { η = Φ-natˡ⇒ f ; natural = Φ-natˡ-natural⇒ f })
         (λ k → C.Hom.inv-invertible (Φ-natˡ-inv f k))

  Φ-naturalʳ : (x : C.Obj) {y y' : D.Obj} (g : y D.⇒₁ y') →
               (Φ x y' ∘F D.postcomp g) ≅N (C.postcomp (R₁ g) ∘F Φ x y)
  Φ-naturalʳ x g =
    mk≅N (record { η = Φ-natʳ⇒ g ; natural = Φ-natʳ-natural⇒ g })
         (λ k → C.Hom.inv-invertible (Φ-natʳ-inv g k))

  ----------------------------------------------------------------------
  -- Coherence of the two comparisons
  ----------------------------------------------------------------------

  -- Φ₂ preserves invertible 2-cells, with the inverse on the nose
  Φ₂-inv : {x : C.Obj} {y : D.Obj} {k k' : F.F₀ x D.⇒₁ y} {γ : k D.⇒₂ k'} →
           D.Invertible₂ γ → C.Invertible₂ (Φ₂ γ)
  Φ₂-inv {γ = γ} i = C.Hom.mkInv (Φ₂ (D.Hom.inv i))
    (C.≈-trans (C.≈-sym (Φ₂-• (D.Hom.inv i) γ))
    (C.≈-trans (Φ₂-cong (D.Hom.invˡ i)) Φ₂-id))
    (C.≈-trans (C.≈-sym (Φ₂-• γ (D.Hom.inv i)))
    (C.≈-trans (Φ₂-cong (D.Hom.invʳ i)) Φ₂-id))

  -- whiskering in C preserves invertible 2-cells
  C◁-inv : {a b c : C.Obj} (f : b C.⇒₁ c) {g g' : a C.⇒₁ b} {β : g C.⇒₂ g'} →
           C.Invertible₂ β → C.Invertible₂ (f C.◁ β)
  C◁-inv f i = C.invertible-≅₂ (f C.◁≅ C.≅₂-invertible i)

  C▷-inv : {a b c : C.Obj} {f f' : b C.⇒₁ c} {α : f C.⇒₂ f'} (g : a C.⇒₁ b) →
           C.Invertible₂ α → C.Invertible₂ (α C.▷ g)
  C▷-inv g i = C.invertible-≅₂ (C.≅₂-invertible i C.▷≅ g)

  Cassoc⇒-inv : {a b c d : C.Obj} (f : c C.⇒₁ d) (g : b C.⇒₁ c) (h : a C.⇒₁ b) →
                C.Invertible₂ (C.assoc⇒ f g h)
  Cassoc⇒-inv f g h = C.invertible-≅₂ (C.associator f g h)

  -- the two comparisons commute with each other
  Φ-exchange : {x x' : C.Obj} (f : x' C.⇒₁ x) {y y' : D.Obj} (g : y D.⇒₁ y')
               (h : F.F₀ x D.⇒₁ y) →
               ((R₁ g C.◁ Φ-natˡ⇒ f h) C.• Φ-natʳ⇒ g (h D.∘₁ F.F₁ f))
               C.≈ (C.assoc⇒ (R₁ g) (⇑₁ h) f C.•
                     ((Φ-natʳ⇒ g h C.▷ f) C.•
                       (Φ-natˡ⇒ f (g D.∘₁ h) C.• Φ₂ (D.assoc⇐ g h (F.F₁ f)))))
  Φ-exchange {x} {x'} f {y} {y'} g h = C.Hom.inv-cong iL iR core
    where
      open D.⇒₂-Reasoning

      uy  = u y
      uy' = u y'
      Ff  = F.F₁ f
      H   = ⇑₁ h
      FH  = F.F₁ H
      Rg  = R₁ g
      FRg = F.F₁ Rg
      εgu = ε (g D.∘₁ uy)
      κ   = F.F-∘⇐ H f
      φ   = F.F₂ (Φ-natˡ⇐ f h)
      ψ   = F.F₂ (Φ-natʳ⇐ g h)

      iL : C.Invertible₂ ((R₁ g C.◁ Φ-natˡ⇒ f h) C.• Φ-natʳ⇒ g (h D.∘₁ Ff))
      iL = C.Hom.∘-invertible
             (C◁-inv Rg (C.Hom.inv-invertible (Φ-natˡ-inv f h)))
             (C.Hom.inv-invertible (Φ-natʳ-inv g (h D.∘₁ Ff)))

      iR : C.Invertible₂ (C.assoc⇒ Rg H f C.•
             ((Φ-natʳ⇒ g h C.▷ f) C.•
               (Φ-natˡ⇒ f (g D.∘₁ h) C.• Φ₂ (D.assoc⇐ g h Ff))))
      iR = C.Hom.∘-invertible (Cassoc⇒-inv Rg H f)
           (C.Hom.∘-invertible (C▷-inv f (C.Hom.inv-invertible (Φ-natʳ-inv g h)))
           (C.Hom.∘-invertible (C.Hom.inv-invertible (Φ-natˡ-inv f (g D.∘₁ h)))
                               (Φ₂-inv (assoc⇐-inv g h Ff))))

      -- the left-hand side, with the factorizations peeled off
      leftReduce : Pʳ g (h D.∘₁ Ff) D.• w (Rg C.◁ Φ-natˡ⇐ f h)
                   D.≈ (g D.◁ Pˡ f h) D.•
                         (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
                           ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
                             (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                               (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))
      leftReduce = begin
        Pʳ g (h D.∘₁ Ff) D.• w (Rg C.◁ Φ-natˡ⇐ f h)
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ
             (D.≈-trans D.•-assoc (D.•-congʳ
             (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc))))) ⟩
        (g D.◁ ε (h D.∘₁ Ff)) D.•
          (D.assoc⇒ g uy (F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
            ((εgu D.▷ F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
              (D.assoc⇐ uy' FRg (F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
                ((uy' D.◁ F.F-∘⇐ Rg (⇑₁ (h D.∘₁ Ff))) D.•
                  w (Rg C.◁ Φ-natˡ⇐ f h)))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym (D.◁-• uy' (F.F-∘⇐ Rg (⇑₁ (h D.∘₁ Ff)))
                                              (F.F₂ (Rg C.◁ Φ-natˡ⇐ f h))))
               (D.≈-trans (D.◁-cong uy' (F.F-∘-natural⇐ (C.id₂ {f = Rg})
                                          (Φ-natˡ⇐ f h)))
               (D.≈-trans (D.◁-• uy' (F.F₂ (C.id₂ {f = Rg}) D.∗ φ)
                                     (F.F-∘⇐ Rg (H C.∘₁ f)))
                          (D.•-congˡ (D.◁-cong uy'
                            (D.∗-cong F.F₂-id₂ D.≈-refl))))))))) ⟩
        (g D.◁ ε (h D.∘₁ Ff)) D.•
          (D.assoc⇒ g uy (F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
            ((εgu D.▷ F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
              (D.assoc⇐ uy' FRg (F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
                ((uy' D.◁ (FRg D.◁ φ)) D.• (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ
                 (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = uy'}) (D.id₂ {f = FRg}) φ)
                            (D.•-congˡ (D.∗-cong (D.∗-id uy' FRg) D.≈-refl))))
                          D.•-assoc)))) ⟩
        (g D.◁ ε (h D.∘₁ Ff)) D.•
          (D.assoc⇒ g uy (F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
            ((εgu D.▷ F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
              (((uy' D.∘₁ FRg) D.◁ φ) D.•
                (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                  (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f))))))
          ≈⟨ D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ
                 (D.≈-trans (D.≈-sym (D.∗-• εgu (D.id₂ {f = uy' D.∘₁ FRg})
                                        (D.id₂ {f = F.F₁ (⇑₁ (h D.∘₁ Ff))}) φ))
                 (D.≈-trans (D.∗-cong D.•-identityʳ D.•-identityˡ)
                            (D.∗-decomposeʳ εgu φ))))
                          D.•-assoc))) ⟩
        (g D.◁ ε (h D.∘₁ Ff)) D.•
          (D.assoc⇒ g uy (F.F₁ (⇑₁ (h D.∘₁ Ff))) D.•
            (((g D.∘₁ uy) D.◁ φ) D.•
              ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
                (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                  (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f))))))
          ≈⟨ D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ
                 (D.≈-sym (D.≈-trans (D.assoc-natural (D.id₂ {f = g})
                                       (D.id₂ {f = uy}) φ)
                          (D.•-congʳ (D.∗-cong (D.∗-id g uy) D.≈-refl)))))
                          D.•-assoc)) ⟩
        (g D.◁ ε (h D.∘₁ Ff)) D.•
          ((g D.◁ (uy D.◁ φ)) D.•
            (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
              ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
                (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                  (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f))))))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.•-congˡ (D.≈-trans (D.≈-sym (D.◁-• g (ε (h D.∘₁ Ff)) (uy D.◁ φ)))
                                   (D.◁-cong g (⇑₂-β (Pˡ f h))))) ⟩
        (g D.◁ Pˡ f h) D.•
          (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
            ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
              (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f))))) ∎

      rightReduce : D.assoc⇒ g h Ff D.•
                      (Pˡ f (g D.∘₁ h) D.•
                        (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f)))
                    D.≈ D.assoc⇒ g h Ff D.•
                      ((Pʳ g h D.▷ Ff) D.•
                        (D.assoc⇐ uy' (F.F₁ (Rg C.∘₁ H)) Ff D.•
                          ((uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f) D.•
                            (uy' D.◁ F.F₂ (C.assoc⇐ Rg H f)))))
      rightReduce = D.•-congʳ (begin
        Pˡ f (g D.∘₁ h) D.• (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        (ε (g D.∘₁ h) D.▷ Ff) D.•
          (D.assoc⇐ uy' (F.F₁ (⇑₁ (g D.∘₁ h))) Ff D.•
            ((uy' D.◁ F.F-∘⇐ (⇑₁ (g D.∘₁ h)) f) D.•
              (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ
                 (D.≈-trans (D.≈-sym (D.◁-• uy' (F.F-∘⇐ (⇑₁ (g D.∘₁ h)) f)
                                                (F.F₂ (Φ-natʳ⇐ g h C.▷ f))))
                 (D.≈-trans (D.◁-cong uy' (F.F-∘-natural⇐ (Φ-natʳ⇐ g h)
                                            (C.id₂ {f = f})))
                 (D.≈-trans (D.◁-• uy' (ψ D.∗ F.F₂ (C.id₂ {f = f}))
                                       (F.F-∘⇐ (Rg C.∘₁ H) f))
                            (D.•-congˡ (D.◁-cong uy'
                              (D.∗-cong D.≈-refl F.F₂-id₂))))))))) ⟩
        (ε (g D.∘₁ h) D.▷ Ff) D.•
          (D.assoc⇐ uy' (F.F₁ (⇑₁ (g D.∘₁ h))) Ff D.•
            (((uy' D.◁ (ψ D.▷ Ff)) D.• (uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f)) D.•
              w (C.assoc⇐ Rg H f)))
          ≈⟨ D.•-congʳ (D.•-congʳ D.•-assoc) ⟩
        (ε (g D.∘₁ h) D.▷ Ff) D.•
          (D.assoc⇐ uy' (F.F₁ (⇑₁ (g D.∘₁ h))) Ff D.•
            ((uy' D.◁ (ψ D.▷ Ff)) D.•
              ((uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f) D.• w (C.assoc⇐ Rg H f))))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = uy'}) ψ
                                       (D.id₂ {f = Ff})))
                          D.•-assoc)) ⟩
        (ε (g D.∘₁ h) D.▷ Ff) D.•
          (((uy' D.◁ ψ) D.▷ Ff) D.•
            (D.assoc⇐ uy' (F.F₁ (Rg C.∘₁ H)) Ff D.•
              ((uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f) D.• w (C.assoc⇐ Rg H f))))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.•-congˡ (D.≈-trans (D.≈-sym (D.▷-• (ε (g D.∘₁ h))
                                                   (w (Φ-natʳ⇐ g h)) Ff))
                                   (D.▷-cong Ff (⇑₂-β (Pʳ g h))))) ⟩
        (Pʳ g h D.▷ Ff) D.•
          (D.assoc⇐ uy' (F.F₁ (Rg C.∘₁ H)) Ff D.•
            ((uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f) D.•
              (uy' D.◁ F.F₂ (C.assoc⇐ Rg H f)))) ∎)

      -- the coherence of F, in the shape the exchange needs
      Fcoh : (FRg D.◁ κ) D.• F.F-∘⇐ Rg (H C.∘₁ f)
             D.≈ D.assoc⇒ FRg FH Ff D.•
                   ((F.F-∘⇐ Rg H D.▷ Ff) D.•
                     (F.F-∘⇐ (Rg C.∘₁ H) f D.• F.F₂ (C.assoc⇐ Rg H f)))
      Fcoh = D.≈-sym (begin
        D.assoc⇒ FRg FH Ff D.•
          ((F.F-∘⇐ Rg H D.▷ Ff) D.•
            (F.F-∘⇐ (Rg C.∘₁ H) f D.• F.F₂ (C.assoc⇐ Rg H f)))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        D.assoc⇒ FRg FH Ff D.•
          (((F.F-∘⇐ Rg H D.▷ Ff) D.• F.F-∘⇐ (Rg C.∘₁ H) f)
            D.• F.F₂ (C.assoc⇐ Rg H f))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D.assoc⇒ FRg FH Ff D.•
          ((F.F-∘⇐ Rg H D.▷ Ff) D.• F.F-∘⇐ (Rg C.∘₁ H) f))
          D.• F.F₂ (C.assoc⇐ Rg H f)
          ≈⟨ D.•-congˡ (F₂-assoc Rg H f) ⟩
        ((FRg D.◁ F.F-∘⇐ H f) D.•
          (F.F-∘⇐ Rg (H C.∘₁ f) D.• F.F₂ (C.assoc⇒ Rg H f)))
          D.• F.F₂ (C.assoc⇐ Rg H f)
          ≈⟨ D.•-assoc ⟩
        (FRg D.◁ F.F-∘⇐ H f) D.•
          ((F.F-∘⇐ Rg (H C.∘₁ f) D.• F.F₂ (C.assoc⇒ Rg H f))
            D.• F.F₂ (C.assoc⇐ Rg H f))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (FRg D.◁ F.F-∘⇐ H f) D.•
          (F.F-∘⇐ Rg (H C.∘₁ f) D.•
            (F.F₂ (C.assoc⇒ Rg H f) D.• F.F₂ (C.assoc⇐ Rg H f)))
          ≈⟨ D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym (F.F₂-• (C.assoc⇒ Rg H f) (C.assoc⇐ Rg H f)))
               (D.≈-trans (F.F₂-cong (C.≅₂isoʳ (C.associator Rg H f)))
                          F.F₂-id₂))) ⟩
        (FRg D.◁ F.F-∘⇐ H f) D.• (F.F-∘⇐ Rg (H C.∘₁ f) D.• D.id₂)
          ≈⟨ D.•-congʳ D.•-identityʳ ⟩
        (FRg D.◁ κ) D.• F.F-∘⇐ Rg (H C.∘₁ f) ∎)

      M = (g D.◁ (ε h D.▷ Ff)) D.•
            ((g D.◁ D.assoc⇐ uy FH Ff) D.•
              (D.assoc⇒ g uy (FH D.∘₁ Ff) D.•
                ((εgu D.▷ (FH D.∘₁ Ff)) D.•
                  (D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
                    ((uy' D.◁ D.assoc⇒ FRg FH Ff) D.•
                      ((uy' D.◁ (F.F-∘⇐ Rg H D.▷ Ff)) D.•
                        ((uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f) D.•
                          (uy' D.◁ F.F₂ (C.assoc⇐ Rg H f)))))))))

      leftM : (g D.◁ Pˡ f h) D.•
                (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
                  ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
                    (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                      (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))
              D.≈ M
      leftM = begin
        (g D.◁ Pˡ f h) D.•
          (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
            ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
              (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))
          ≈⟨ D.•-congˡ (D.≈-trans (D.◁-• g (ε h D.▷ Ff)
                                       (D.assoc⇐ uy FH Ff D.• (uy D.◁ κ)))
                       (D.•-congʳ (D.◁-• g (D.assoc⇐ uy FH Ff) (uy D.◁ κ)))) ⟩
        ((g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.• (g D.◁ (uy D.◁ κ)))) D.•
          (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
            ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
              (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            ((g D.◁ (uy D.◁ κ)) D.•
              (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
                ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
                  (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                    (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ
                 (D.≈-trans (D.assoc-natural (D.id₂ {f = g}) (D.id₂ {f = uy}) κ)
                            (D.•-congʳ (D.∗-cong (D.∗-id g uy) D.≈-refl))))
                          D.•-assoc))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (D.assoc⇒ g uy (FH D.∘₁ Ff) D.•
              (((g D.∘₁ uy) D.◁ κ) D.•
                ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
                  (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                    (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym (D.exchange εgu κ))) D.•-assoc)))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (D.assoc⇒ g uy (FH D.∘₁ Ff) D.•
              ((εgu D.▷ (FH D.∘₁ Ff)) D.•
                (((uy' D.∘₁ FRg) D.◁ κ) D.•
                  (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                    (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym
                 (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = uy'}) (D.id₂ {f = FRg}) κ)
                            (D.•-congˡ (D.∗-cong (D.∗-id uy' FRg) D.≈-refl)))))
                          D.•-assoc))))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (D.assoc⇒ g uy (FH D.∘₁ Ff) D.•
              ((εgu D.▷ (FH D.∘₁ Ff)) D.•
                (D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
                  ((uy' D.◁ (FRg D.◁ κ)) D.• (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym (D.◁-• uy' (FRg D.◁ κ) (F.F-∘⇐ Rg (H C.∘₁ f))))
               (D.≈-trans (D.◁-cong uy' Fcoh)
               (D.≈-trans (D.◁-• uy' (D.assoc⇒ FRg FH Ff)
                             ((F.F-∘⇐ Rg H D.▷ Ff) D.•
                               (F.F-∘⇐ (Rg C.∘₁ H) f D.• F.F₂ (C.assoc⇐ Rg H f))))
                          (D.•-congʳ
                            (D.≈-trans (D.◁-• uy' (F.F-∘⇐ Rg H D.▷ Ff)
                                          (F.F-∘⇐ (Rg C.∘₁ H) f D.•
                                            F.F₂ (C.assoc⇐ Rg H f)))
                                       (D.•-congʳ (D.◁-• uy' (F.F-∘⇐ (Rg C.∘₁ H) f)
                                          (F.F₂ (C.assoc⇐ Rg H f))))))))))))) ⟩
        M ∎

      a₁ = D.assoc⇒ FRg FH Ff
      a₂ = D.assoc⇒ uy' (FRg D.∘₁ FH) Ff
      a₃ = D.assoc⇒ uy' FRg FH
      a₄ = D.assoc⇒ uy' FRg (FH D.∘₁ Ff)
      a₅ = D.assoc⇒ (uy' D.∘₁ FRg) FH Ff
      b₂ = D.assoc⇒ g (uy D.∘₁ FH) Ff
      b₃ = D.assoc⇒ g uy FH
      b₄ = D.assoc⇒ g uy (FH D.∘₁ Ff)
      b₅ = D.assoc⇒ (g D.∘₁ uy) FH Ff

      X₁ = (g D.◁ ε h) D.▷ Ff
      X₃ = (εgu D.▷ FH) D.▷ Ff
      X₄ = D.assoc⇐ uy' FRg FH D.▷ Ff
      X₅ = (uy' D.◁ F.F-∘⇐ Rg H) D.▷ Ff
      Z  = D.assoc⇐ uy' (F.F₁ (Rg C.∘₁ H)) Ff
      Tl = (uy' D.◁ F.F-∘⇐ (Rg C.∘₁ H) f) D.• (uy' D.◁ F.F₂ (C.assoc⇐ Rg H f))

      stepA : D.assoc⇒ g h Ff D.• X₁ D.≈ (g D.◁ (ε h D.▷ Ff)) D.• b₂
      stepA = D.≈-sym (D.assoc-natural (D.id₂ {f = g}) (ε h) (D.id₂ {f = Ff}))

      stepB : b₂ D.• (b₃ D.▷ Ff) D.≈ (g D.◁ D.assoc⇐ uy FH Ff) D.• (b₄ D.• b₅)
      stepB = D.≈-sym (begin
        (g D.◁ D.assoc⇐ uy FH Ff) D.• (b₄ D.• b₅)
          ≈⟨ D.•-congʳ (D.pentagon g uy FH Ff) ⟩
        (g D.◁ D.assoc⇐ uy FH Ff) D.•
          ((g D.◁ D.assoc⇒ uy FH Ff) D.• (b₂ D.• (b₃ D.▷ Ff)))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((g D.◁ D.assoc⇐ uy FH Ff) D.• (g D.◁ D.assoc⇒ uy FH Ff))
          D.• (b₂ D.• (b₃ D.▷ Ff))
          ≈⟨ D.•-congˡ (D.≈-trans (D.≈-sym (D.◁-• g (D.assoc⇐ uy FH Ff)
                                                    (D.assoc⇒ uy FH Ff)))
                       (D.≈-trans (D.◁-cong g (D.≅₂isoˡ (D.associator uy FH Ff)))
                                  (D.◁-id g ((uy D.∘₁ FH) D.∘₁ Ff)))) ⟩
        D.id₂ D.• (b₂ D.• (b₃ D.▷ Ff))
          ≈⟨ D.•-identityˡ ⟩
        b₂ D.• (b₃ D.▷ Ff) ∎)

      stepD : b₅ D.• X₃ D.≈ (εgu D.▷ (FH D.∘₁ Ff)) D.• a₅
      stepD = D.≈-sym (D.≈-trans
                (D.•-congˡ (D.∗-cong D.≈-refl (D.≈-sym (D.∗-id FH Ff))))
                (D.assoc-natural εgu (D.id₂ {f = FH}) (D.id₂ {f = Ff})))

      stepE : a₅ D.• X₄ D.≈ D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.• ((uy' D.◁ a₁) D.• a₂)
      stepE = D.≈-sym (begin
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.• ((uy' D.◁ a₁) D.• a₂)
          ≈⟨ D.•-congʳ (D.≈-sym D.•-identityʳ) ⟩
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.• (((uy' D.◁ a₁) D.• a₂) D.• D.id₂)
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-sym
               (D.≈-trans (D.≈-sym (D.▷-• a₃ (D.assoc⇐ uy' FRg FH) Ff))
               (D.≈-trans (D.▷-cong Ff (D.≅₂isoʳ (D.associator uy' FRg FH)))
                          (D.▷-id (uy' D.∘₁ (FRg D.∘₁ FH)) Ff))))) ⟩
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
          (((uy' D.◁ a₁) D.• a₂) D.• ((a₃ D.▷ Ff) D.• X₄))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
          ((((uy' D.◁ a₁) D.• a₂) D.• (a₃ D.▷ Ff)) D.• X₄)
          ≈⟨ D.•-congʳ (D.•-congˡ D.•-assoc) ⟩
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
          (((uy' D.◁ a₁) D.• (a₂ D.• (a₃ D.▷ Ff))) D.• X₄)
          ≈⟨ D.•-congʳ (D.•-congˡ (D.≈-sym (D.pentagon uy' FRg FH Ff))) ⟩
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.• ((a₄ D.• a₅) D.• X₄)
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.• (a₄ D.• (a₅ D.• X₄))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.• a₄) D.• (a₅ D.• X₄)
          ≈⟨ D.•-congˡ (D.≅₂isoˡ (D.associator uy' FRg (FH D.∘₁ Ff))) ⟩
        D.id₂ D.• (a₅ D.• X₄)
          ≈⟨ D.•-identityˡ ⟩
        a₅ D.• X₄ ∎)

      stepF : a₂ D.• X₅
              D.≈ (uy' D.◁ (F.F-∘⇐ Rg H D.▷ Ff))
                    D.• D.assoc⇒ uy' (F.F₁ (Rg C.∘₁ H)) Ff
      stepF = D.≈-sym (D.assoc-natural (D.id₂ {f = uy'}) (F.F-∘⇐ Rg H)
                                       (D.id₂ {f = Ff}))

      stepG : D.assoc⇒ uy' (F.F₁ (Rg C.∘₁ H)) Ff D.• (Z D.• Tl) D.≈ Tl
      stepG = D.≈-trans (D.≈-sym D.•-assoc)
              (D.≈-trans (D.•-congˡ
                (D.≅₂isoʳ (D.associator uy' (F.F₁ (Rg C.∘₁ H)) Ff)))
                         D.•-identityˡ)

      rightM : D.assoc⇒ g h Ff D.• ((Pʳ g h D.▷ Ff) D.• (Z D.• Tl)) D.≈ M
      rightM = begin
        D.assoc⇒ g h Ff D.• ((Pʳ g h D.▷ Ff) D.• (Z D.• Tl))
          ≈⟨ D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.▷-• (g D.◁ ε h) _ Ff)
               (D.•-congʳ (D.≈-trans (D.▷-• b₃ _ Ff)
               (D.•-congʳ (D.≈-trans (D.▷-• (εgu D.▷ FH) _ Ff)
               (D.•-congʳ (D.▷-• (D.assoc⇐ uy' FRg FH)
                                 (uy' D.◁ F.F-∘⇐ Rg H) Ff)))))))) ⟩
        D.assoc⇒ g h Ff D.•
          ((X₁ D.• ((b₃ D.▷ Ff) D.• (X₃ D.• (X₄ D.• X₅)))) D.• (Z D.• Tl))
          ≈⟨ D.•-congʳ (D.≈-trans D.•-assoc (D.•-congʳ
             (D.≈-trans D.•-assoc (D.•-congʳ
             (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc)))))) ⟩
        D.assoc⇒ g h Ff D.•
          (X₁ D.• ((b₃ D.▷ Ff) D.• (X₃ D.• (X₄ D.• (X₅ D.• (Z D.• Tl))))))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ stepA) D.•-assoc) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          (b₂ D.• ((b₃ D.▷ Ff) D.• (X₃ D.• (X₄ D.• (X₅ D.• (Z D.• Tl))))))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ stepB)
             (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc)))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (b₄ D.• (b₅ D.• (X₃ D.• (X₄ D.• (X₅ D.• (Z D.• Tl)))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ stepD) D.•-assoc)))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (b₄ D.• ((εgu D.▷ (FH D.∘₁ Ff)) D.•
              (a₅ D.• (X₄ D.• (X₅ D.• (Z D.• Tl)))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
             (D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ stepE)
             (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc))))))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (b₄ D.• ((εgu D.▷ (FH D.∘₁ Ff)) D.•
              (D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
                ((uy' D.◁ a₁) D.• (a₂ D.• (X₅ D.• (Z D.• Tl))))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
             (D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ stepF) D.•-assoc))))))) ⟩
        (g D.◁ (ε h D.▷ Ff)) D.•
          ((g D.◁ D.assoc⇐ uy FH Ff) D.•
            (b₄ D.• ((εgu D.▷ (FH D.∘₁ Ff)) D.•
              (D.assoc⇐ uy' FRg (FH D.∘₁ Ff) D.•
                ((uy' D.◁ a₁) D.•
                  ((uy' D.◁ (F.F-∘⇐ Rg H D.▷ Ff)) D.•
                    (D.assoc⇒ uy' (F.F₁ (Rg C.∘₁ H)) Ff D.• (Z D.• Tl))))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
             (D.•-congʳ stepG)))))) ⟩
        M ∎

      ε₀ = ε (g D.∘₁ (h D.∘₁ Ff))

      peelL2 : ε₀ D.• w (Φ-natʳ⇐ g (h D.∘₁ Ff) C.• (Rg C.◁ Φ-natˡ⇐ f h))
               D.≈ Pʳ g (h D.∘₁ Ff) D.• w (Rg C.◁ Φ-natˡ⇐ f h)
      peelL2 = D.≈-trans
        (D.•-congʳ (w-• (Φ-natʳ⇐ g (h D.∘₁ Ff)) (Rg C.◁ Φ-natˡ⇐ f h)))
        (D.≈-trans (D.≈-sym D.•-assoc)
                   (D.•-congˡ (⇑₂-β (Pʳ g (h D.∘₁ Ff)))))

      peelR2 : ε₀ D.• w (((Φ₂ (D.assoc⇒ g h Ff) C.• Φ-natˡ⇐ f (g D.∘₁ h))
                 C.• (Φ-natʳ⇐ g h C.▷ f)) C.• C.assoc⇐ Rg H f)
               D.≈ D.assoc⇒ g h Ff D.•
                     (Pˡ f (g D.∘₁ h) D.•
                       (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f)))
      peelR2 = begin
        ε₀ D.• w (((Φ₂ (D.assoc⇒ g h Ff) C.• Φ-natˡ⇐ f (g D.∘₁ h))
          C.• (Φ-natʳ⇐ g h C.▷ f)) C.• C.assoc⇐ Rg H f)
          ≈⟨ D.•-congʳ (w-• ((Φ₂ (D.assoc⇒ g h Ff) C.• Φ-natˡ⇐ f (g D.∘₁ h))
                              C.• (Φ-natʳ⇐ g h C.▷ f)) (C.assoc⇐ Rg H f)) ⟩
        ε₀ D.• (w ((Φ₂ (D.assoc⇒ g h Ff) C.• Φ-natˡ⇐ f (g D.∘₁ h))
          C.• (Φ-natʳ⇐ g h C.▷ f)) D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.•-congʳ (D.•-congˡ (w-• (Φ₂ (D.assoc⇒ g h Ff)
               C.• Φ-natˡ⇐ f (g D.∘₁ h)) (Φ-natʳ⇐ g h C.▷ f))) ⟩
        ε₀ D.• ((w (Φ₂ (D.assoc⇒ g h Ff) C.• Φ-natˡ⇐ f (g D.∘₁ h))
          D.• w (Φ-natʳ⇐ g h C.▷ f)) D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.•-congʳ (D.•-congˡ (D.•-congˡ (w-• (Φ₂ (D.assoc⇒ g h Ff))
               (Φ-natˡ⇐ f (g D.∘₁ h))))) ⟩
        ε₀ D.• (((w (Φ₂ (D.assoc⇒ g h Ff)) D.• w (Φ-natˡ⇐ f (g D.∘₁ h)))
          D.• w (Φ-natʳ⇐ g h C.▷ f)) D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.•-congʳ (D.•-congˡ D.•-assoc) ⟩
        ε₀ D.• ((w (Φ₂ (D.assoc⇒ g h Ff)) D.•
          (w (Φ-natˡ⇐ f (g D.∘₁ h)) D.• w (Φ-natʳ⇐ g h C.▷ f)))
            D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        ε₀ D.• (w (Φ₂ (D.assoc⇒ g h Ff)) D.•
          ((w (Φ-natˡ⇐ f (g D.∘₁ h)) D.• w (Φ-natʳ⇐ g h C.▷ f))
            D.• w (C.assoc⇐ Rg H f)))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (ε₀ D.• w (Φ₂ (D.assoc⇒ g h Ff))) D.•
          ((w (Φ-natˡ⇐ f (g D.∘₁ h)) D.• w (Φ-natʳ⇐ g h C.▷ f))
            D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.•-congˡ (Φ₂-β (D.assoc⇒ g h Ff)) ⟩
        (D.assoc⇒ g h Ff D.• ε ((g D.∘₁ h) D.∘₁ Ff)) D.•
          ((w (Φ-natˡ⇐ f (g D.∘₁ h)) D.• w (Φ-natʳ⇐ g h C.▷ f))
            D.• w (C.assoc⇐ Rg H f))
          ≈⟨ D.•-assoc ⟩
        D.assoc⇒ g h Ff D.• (ε ((g D.∘₁ h) D.∘₁ Ff) D.•
          ((w (Φ-natˡ⇐ f (g D.∘₁ h)) D.• w (Φ-natʳ⇐ g h C.▷ f))
            D.• w (C.assoc⇐ Rg H f)))
          ≈⟨ D.•-congʳ (D.•-congʳ D.•-assoc) ⟩
        D.assoc⇒ g h Ff D.• (ε ((g D.∘₁ h) D.∘₁ Ff) D.•
          (w (Φ-natˡ⇐ f (g D.∘₁ h)) D.•
            (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f))))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        D.assoc⇒ g h Ff D.• ((ε ((g D.∘₁ h) D.∘₁ Ff) D.•
          w (Φ-natˡ⇐ f (g D.∘₁ h))) D.•
            (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f)))
          ≈⟨ D.•-congʳ (D.•-congˡ (⇑₂-β (Pˡ f (g D.∘₁ h)))) ⟩
        D.assoc⇒ g h Ff D.•
          (Pˡ f (g D.∘₁ h) D.•
            (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f))) ∎

      core : C.Hom.inv iL C.≈ C.Hom.inv iR
      core = ⇑₂-cancel (begin
        ε₀ D.• w (Φ-natʳ⇐ g (h D.∘₁ Ff) C.• (Rg C.◁ Φ-natˡ⇐ f h))
          ≈⟨ peelL2 ⟩
        Pʳ g (h D.∘₁ Ff) D.• w (Rg C.◁ Φ-natˡ⇐ f h)
          ≈⟨ leftReduce ⟩
        (g D.◁ Pˡ f h) D.•
          (D.assoc⇒ g uy (F.F₁ (H C.∘₁ f)) D.•
            ((εgu D.▷ F.F₁ (H C.∘₁ f)) D.•
              (D.assoc⇐ uy' FRg (F.F₁ (H C.∘₁ f)) D.•
                (uy' D.◁ F.F-∘⇐ Rg (H C.∘₁ f)))))
          ≈⟨ leftM ⟩
        M
          ≈⟨ D.≈-sym rightM ⟩
        D.assoc⇒ g h Ff D.• ((Pʳ g h D.▷ Ff) D.• (Z D.• Tl))
          ≈⟨ D.≈-sym rightReduce ⟩
        D.assoc⇒ g h Ff D.•
          (Pˡ f (g D.∘₁ h) D.•
            (w (Φ-natʳ⇐ g h C.▷ f) D.• w (C.assoc⇐ Rg H f)))
          ≈⟨ D.≈-sym peelR2 ⟩
        ε₀ D.• w (((Φ₂ (D.assoc⇒ g h Ff) C.• Φ-natˡ⇐ f (g D.∘₁ h))
          C.• (Φ-natʳ⇐ g h C.▷ f)) C.• C.assoc⇐ Rg H f) ∎)


  -- the comparison for precomposition is compatible with identities
  Φ-naturalˡ-id : {x : C.Obj} {y : D.Obj} (h : F.F₀ x D.⇒₁ y) →
                  (Φ-natˡ⇒ (C.id₁ {x}) h C.• Φ₂ (h D.◁ F.F-id⇒))
                  C.≈ (C.unitʳ⇐ (⇑₁ h) C.• Φ₂ (D.unitʳ⇒ h))
  Φ-naturalˡ-id {x} {y} h = C.Hom.inv-cong iL iR core
    where
      open D.⇒₂-Reasoning

      uy = u y
      H  = ⇑₁ h
      FH = F.F₁ H
      δ  = F.F-id⇐ {x}

      iL : C.Invertible₂ (Φ-natˡ⇒ (C.id₁ {x}) h C.• Φ₂ (h D.◁ F.F-id⇒))
      iL = C.Hom.∘-invertible
             (C.Hom.inv-invertible (Φ-natˡ-inv (C.id₁ {x}) h))
             (Φ₂-inv (◁-inv h (D.invertible-≅₂ F.F-id)))

      iR : C.Invertible₂ (C.unitʳ⇐ (⇑₁ h) C.• Φ₂ (D.unitʳ⇒ h))
      iR = C.Hom.∘-invertible
             (C.invertible-≅₂ (C.≅₂-sym (C.unitorʳ (⇑₁ h))))
             (Φ₂-inv (D.invertible-≅₂ (D.unitorʳ h)))

      unfold : w (C.unitʳ⇒ (⇑₁ h))
               D.≈ (uy D.◁ D.unitʳ⇒ FH) D.•
                     ((uy D.◁ (FH D.◁ δ)) D.• (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
      unfold = D.≈-trans (D.◁-cong uy (F₂-unitʳ H))
               (D.≈-trans (D.◁-• uy (D.unitʳ⇒ FH)
                            ((FH D.◁ δ) D.• F.F-∘⇐ H (C.id₁ {x})))
                          (D.•-congʳ (D.◁-• uy (FH D.◁ δ)
                                       (F.F-∘⇐ H (C.id₁ {x})))))

      slide : D.unitʳ⇒ (uy D.∘₁ FH) D.• D.assoc⇐ uy FH D.id₁
              D.≈ uy D.◁ D.unitʳ⇒ FH
      slide = D.≈-trans (D.•-congˡ (D.unitʳ-∘ uy FH))
              (D.≈-trans D.•-assoc
              (D.≈-trans (D.•-congʳ (D.≅₂isoʳ (D.associator uy FH D.id₁)))
                         D.•-identityʳ))

      prefix : (ε h D.▷ D.id₁) D.• D.assoc⇐ uy FH D.id₁
               D.≈ D.unitʳ⇐ h D.• (ε h D.• (uy D.◁ D.unitʳ⇒ FH))
      prefix = D.≈-sym (begin
        D.unitʳ⇐ h D.• (ε h D.• (uy D.◁ D.unitʳ⇒ FH))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-sym slide)) ⟩
        D.unitʳ⇐ h D.•
          (ε h D.• (D.unitʳ⇒ (uy D.∘₁ FH) D.• D.assoc⇐ uy FH D.id₁))
          ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
        D.unitʳ⇐ h D.•
          ((ε h D.• D.unitʳ⇒ (uy D.∘₁ FH)) D.• D.assoc⇐ uy FH D.id₁)
          ≈⟨ D.•-congʳ (D.•-congˡ (D.unitʳ-natural (ε h))) ⟩
        D.unitʳ⇐ h D.•
          ((D.unitʳ⇒ h D.• (ε h D.▷ D.id₁)) D.• D.assoc⇐ uy FH D.id₁)
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        D.unitʳ⇐ h D.•
          (D.unitʳ⇒ h D.• ((ε h D.▷ D.id₁) D.• D.assoc⇐ uy FH D.id₁))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D.unitʳ⇐ h D.• D.unitʳ⇒ h) D.•
          ((ε h D.▷ D.id₁) D.• D.assoc⇐ uy FH D.id₁)
          ≈⟨ D.•-congˡ (D.≅₂isoˡ (D.unitorʳ h)) ⟩
        D.id₂ D.• ((ε h D.▷ D.id₁) D.• D.assoc⇐ uy FH D.id₁)
          ≈⟨ D.•-identityˡ ⟩
        (ε h D.▷ D.id₁) D.• D.assoc⇐ uy FH D.id₁ ∎)

      -- the two ways of turning uy ∘ (FH ∘ F id) into h ∘ id
      middle : (h D.◁ δ) D.• Pˡ (C.id₁ {x}) h
               D.≈ D.unitʳ⇐ h D.• (ε h D.• w (C.unitʳ⇒ (⇑₁ h)))
      middle = begin
        (h D.◁ δ) D.• Pˡ (C.id₁ {x}) h
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((h D.◁ δ) D.• (ε h D.▷ F.F₁ (C.id₁ {x}))) D.•
          (D.assoc⇐ uy FH (F.F₁ (C.id₁ {x})) D.•
            (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
          ≈⟨ D.•-congˡ (D.≈-sym (D.exchange (ε h) δ)) ⟩
        ((ε h D.▷ D.id₁) D.• ((uy D.∘₁ FH) D.◁ δ)) D.•
          (D.assoc⇐ uy FH (F.F₁ (C.id₁ {x})) D.•
            (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ (D.≈-sym D.•-assoc)) ⟩
        (ε h D.▷ D.id₁) D.•
          ((((uy D.∘₁ FH) D.◁ δ) D.• D.assoc⇐ uy FH (F.F₁ (C.id₁ {x}))) D.•
            (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
          ≈⟨ D.•-congʳ (D.•-congˡ (D.≈-sym
               (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = uy}) (D.id₂ {f = FH}) δ)
                          (D.•-congˡ (D.∗-cong (D.∗-id uy FH) D.≈-refl))))) ⟩
        (ε h D.▷ D.id₁) D.•
          ((D.assoc⇐ uy FH D.id₁ D.• (uy D.◁ (FH D.◁ δ))) D.•
            (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        (ε h D.▷ D.id₁) D.•
          (D.assoc⇐ uy FH D.id₁ D.•
            ((uy D.◁ (FH D.◁ δ)) D.• (uy D.◁ F.F-∘⇐ H (C.id₁ {x}))))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        ((ε h D.▷ D.id₁) D.• D.assoc⇐ uy FH D.id₁) D.•
          ((uy D.◁ (FH D.◁ δ)) D.• (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
          ≈⟨ D.•-congˡ prefix ⟩
        (D.unitʳ⇐ h D.• (ε h D.• (uy D.◁ D.unitʳ⇒ FH))) D.•
          ((uy D.◁ (FH D.◁ δ)) D.• (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        D.unitʳ⇐ h D.• (ε h D.•
          ((uy D.◁ D.unitʳ⇒ FH) D.•
            ((uy D.◁ (FH D.◁ δ)) D.• (uy D.◁ F.F-∘⇐ H (C.id₁ {x})))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-sym unfold)) ⟩
        D.unitʳ⇐ h D.• (ε h D.• w (C.unitʳ⇒ (⇑₁ h))) ∎

      core : C.Hom.inv iL C.≈ C.Hom.inv iR
      core = ⇑₂-cancel (begin
        ε (h D.∘₁ D.id₁) D.• w (Φ₂ (h D.◁ δ) C.• Φ-natˡ⇐ (C.id₁ {x}) h)
          ≈⟨ D.•-congʳ (w-• (Φ₂ (h D.◁ δ)) (Φ-natˡ⇐ (C.id₁ {x}) h)) ⟩
        ε (h D.∘₁ D.id₁) D.•
          (w (Φ₂ (h D.◁ δ)) D.• w (Φ-natˡ⇐ (C.id₁ {x}) h))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (ε (h D.∘₁ D.id₁) D.• w (Φ₂ (h D.◁ δ))) D.•
          w (Φ-natˡ⇐ (C.id₁ {x}) h)
          ≈⟨ D.•-congˡ (Φ₂-β (h D.◁ δ)) ⟩
        ((h D.◁ δ) D.• ε (h D.∘₁ F.F₁ (C.id₁ {x}))) D.•
          w (Φ-natˡ⇐ (C.id₁ {x}) h)
          ≈⟨ D.•-assoc ⟩
        (h D.◁ δ) D.•
          (ε (h D.∘₁ F.F₁ (C.id₁ {x})) D.• w (Φ-natˡ⇐ (C.id₁ {x}) h))
          ≈⟨ D.•-congʳ (⇑₂-β (Pˡ (C.id₁ {x}) h)) ⟩
        (h D.◁ δ) D.• Pˡ (C.id₁ {x}) h
          ≈⟨ middle ⟩
        D.unitʳ⇐ h D.• (ε h D.• w (C.unitʳ⇒ (⇑₁ h)))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D.unitʳ⇐ h D.• ε h) D.• w (C.unitʳ⇒ (⇑₁ h))
          ≈⟨ D.•-congˡ (D.≈-sym (Φ₂-β (D.unitʳ⇐ h))) ⟩
        (ε (h D.∘₁ D.id₁) D.• w (Φ₂ (D.unitʳ⇐ h))) D.• w (C.unitʳ⇒ (⇑₁ h))
          ≈⟨ D.•-assoc ⟩
        ε (h D.∘₁ D.id₁) D.• (w (Φ₂ (D.unitʳ⇐ h)) D.• w (C.unitʳ⇒ (⇑₁ h)))
          ≈⟨ D.•-congʳ (D.≈-sym (w-• (Φ₂ (D.unitʳ⇐ h)) (C.unitʳ⇒ (⇑₁ h)))) ⟩
        ε (h D.∘₁ D.id₁) D.• w (Φ₂ (D.unitʳ⇐ h) C.• C.unitʳ⇒ (⇑₁ h)) ∎)

  -- the comparison for postcomposition is compatible with identities
  Φ-naturalʳ-id : {x : C.Obj} {y : D.Obj} (h : F.F₀ x D.⇒₁ y) →
                  Φ-natʳ⇒ (D.id₁ {y}) h
                  C.≈ ((R-id⇒ C.▷ ⇑₁ h) C.•
                        (C.unitˡ⇐ (⇑₁ h) C.• Φ₂ (D.unitˡ⇒ h)))
  Φ-naturalʳ-id {x} {y} h =
    C.Hom.∘-cancelˡ (Φ-natʳ-inv (D.id₁ {y}) h)
      (C.≈-trans (C.Hom.invʳ (Φ-natʳ-inv (D.id₁ {y}) h)) (C.≈-sym G))
    where
      open D.⇒₂-Reasoning

      uy = u y
      H  = ⇑₁ h
      FH = F.F₁ H
      E  = R₁ (D.id₁ {y})
      ρ  = R-id⇒ {y}
      δ  = F.F-id⇐ {R₀ y}
      X  = uy D.◁ F.F-∘⇐ (C.id₁ {R₀ y}) H
      rest = (ρ C.▷ H) C.• (C.unitˡ⇐ H C.• Φ₂ (D.unitˡ⇒ h))

      -- w (C.unitˡ⇒ H), unfolded through the coherence of F
      unfold : w (C.unitˡ⇒ H)
               D.≈ (uy D.◁ D.unitˡ⇒ FH) D.• ((uy D.◁ (δ D.▷ FH)) D.• X)
      unfold = D.≈-trans (D.◁-cong uy (F₂-unitˡ H))
               (D.≈-trans (D.◁-• uy (D.unitˡ⇒ FH)
                            ((δ D.▷ FH) D.• F.F-∘⇐ (C.id₁ {R₀ y}) H))
                          (D.•-congʳ (D.◁-• uy (δ D.▷ FH)
                                       (F.F-∘⇐ (C.id₁ {R₀ y}) H))))

      tri : (D.unitʳ⇒ uy D.▷ FH) D.• D.assoc⇐ uy D.id₁ FH D.≈ uy D.◁ D.unitˡ⇒ FH
      tri = D.≈-trans (D.•-congˡ (D.triangle uy FH))
            (D.≈-trans D.•-assoc
            (D.≈-trans (D.•-congʳ (D.≅₂isoʳ (D.associator uy D.id₁ FH)))
                       D.•-identityʳ))

      reduceP : Pʳ (D.id₁ {y}) h D.• w (ρ C.▷ H)
                D.≈ D.unitˡ⇐ h D.• (ε h D.• w (C.unitˡ⇒ H))
      reduceP = begin
        Pʳ (D.id₁ {y}) h D.• w (ρ C.▷ H)
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ
             (D.≈-trans D.•-assoc (D.•-congʳ
             (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc))))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((ε (D.id₁ D.∘₁ uy) D.▷ FH) D.•
              (D.assoc⇐ uy (F.F₁ E) FH D.•
                ((uy D.◁ F.F-∘⇐ E H) D.• w (ρ C.▷ H)))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym (D.◁-• uy (F.F-∘⇐ E H) (F.F₂ (ρ C.▷ H))))
               (D.≈-trans (D.◁-cong uy (F.F-∘-natural⇐ ρ (C.id₂ {f = H})))
               (D.≈-trans (D.◁-• uy (F.F₂ ρ D.∗ F.F₂ (C.id₂ {f = H}))
                                    (F.F-∘⇐ (C.id₁ {R₀ y}) H))
                          (D.•-congˡ (D.◁-cong uy
                            (D.∗-cong D.≈-refl F.F₂-id₂))))))))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((ε (D.id₁ D.∘₁ uy) D.▷ FH) D.•
              (D.assoc⇐ uy (F.F₁ E) FH D.•
                ((uy D.◁ (F.F₂ ρ D.▷ FH)) D.• X))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = uy})
                                       (F.F₂ ρ) (D.id₂ {f = FH})))
                          D.•-assoc)))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((ε (D.id₁ D.∘₁ uy) D.▷ FH) D.•
              (((uy D.◁ F.F₂ ρ) D.▷ FH) D.•
                (D.assoc⇐ uy (F.F₁ (C.id₁ {R₀ y})) FH D.• X))))
          ≈⟨ D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ
                 (D.≈-trans (D.≈-sym (D.▷-• (ε (D.id₁ D.∘₁ uy))
                                            (uy D.◁ F.F₂ ρ) FH))
                            (D.▷-cong FH (R-Q-β {y})))))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((R-Q D.▷ FH) D.•
              (D.assoc⇐ uy (F.F₁ (C.id₁ {R₀ y})) FH D.• X)))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congˡ
               (D.≈-trans (D.▷-• (D.unitˡ⇐ uy)
                            (D.unitʳ⇒ uy D.• (uy D.◁ δ)) FH)
                          (D.•-congʳ (D.▷-• (D.unitʳ⇒ uy) (uy D.◁ δ) FH))))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            (((D.unitˡ⇐ uy D.▷ FH) D.•
              ((D.unitʳ⇒ uy D.▷ FH) D.• ((uy D.◁ δ) D.▷ FH))) D.•
              (D.assoc⇐ uy (F.F₁ (C.id₁ {R₀ y})) FH D.• X)))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((D.unitˡ⇐ uy D.▷ FH) D.•
              ((D.unitʳ⇒ uy D.▷ FH) D.•
                (((uy D.◁ δ) D.▷ FH) D.•
                  (D.assoc⇐ uy (F.F₁ (C.id₁ {R₀ y})) FH D.• X)))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym
                 (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = uy}) δ (D.id₂ {f = FH}))
                            D.≈-refl)))
                          D.•-assoc))))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((D.unitˡ⇐ uy D.▷ FH) D.•
              ((D.unitʳ⇒ uy D.▷ FH) D.•
                (D.assoc⇐ uy D.id₁ FH D.• ((uy D.◁ (δ D.▷ FH)) D.• X)))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym D.•-assoc) (D.•-congˡ tri)))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.assoc⇒ D.id₁ uy FH D.•
            ((D.unitˡ⇐ uy D.▷ FH) D.•
              ((uy D.◁ D.unitˡ⇒ FH) D.• ((uy D.◁ (δ D.▷ FH)) D.• X))))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ (D.unitˡ⇐-∘ uy FH))) ⟩
        (D.id₁ D.◁ ε h) D.•
          (D.unitˡ⇐ (uy D.∘₁ FH) D.•
            ((uy D.◁ D.unitˡ⇒ FH) D.• ((uy D.◁ (δ D.▷ FH)) D.• X)))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ (D.≈-sym (D.unitˡ-natural⇐ (ε h))))
                        D.•-assoc) ⟩
        D.unitˡ⇐ h D.•
          (ε h D.• ((uy D.◁ D.unitˡ⇒ FH) D.• ((uy D.◁ (δ D.▷ FH)) D.• X)))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-sym unfold)) ⟩
        D.unitˡ⇐ h D.• (ε h D.• w (C.unitˡ⇒ H)) ∎

      G : Φ-natʳ⇐ (D.id₁ {y}) h C.• rest C.≈ C.id₂
      G = ⇑₂-cancel (begin
        ε (D.id₁ D.∘₁ h) D.• w (Φ-natʳ⇐ (D.id₁ {y}) h C.• rest)
          ≈⟨ D.•-congʳ (w-• (Φ-natʳ⇐ (D.id₁ {y}) h) rest) ⟩
        ε (D.id₁ D.∘₁ h) D.• (w (Φ-natʳ⇐ (D.id₁ {y}) h) D.• w rest)
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (ε (D.id₁ D.∘₁ h) D.• w (Φ-natʳ⇐ (D.id₁ {y}) h)) D.• w rest
          ≈⟨ D.•-congˡ (⇑₂-β (Pʳ (D.id₁ {y}) h)) ⟩
        Pʳ (D.id₁ {y}) h D.• w rest
          ≈⟨ D.•-congʳ (D.≈-trans (w-• (ρ C.▷ H) (C.unitˡ⇐ H C.• Φ₂ (D.unitˡ⇒ h)))
                       (D.•-congʳ (w-• (C.unitˡ⇐ H) (Φ₂ (D.unitˡ⇒ h))))) ⟩
        Pʳ (D.id₁ {y}) h D.•
          (w (ρ C.▷ H) D.• (w (C.unitˡ⇐ H) D.• w (Φ₂ (D.unitˡ⇒ h))))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc) (D.•-congˡ reduceP) ⟩
        (D.unitˡ⇐ h D.• (ε h D.• w (C.unitˡ⇒ H))) D.•
          (w (C.unitˡ⇐ H) D.• w (Φ₂ (D.unitˡ⇒ h)))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        D.unitˡ⇐ h D.•
          (ε h D.• (w (C.unitˡ⇒ H) D.•
            (w (C.unitˡ⇐ H) D.• w (Φ₂ (D.unitˡ⇒ h)))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ (D.≈-trans (D.≈-sym (w-• (C.unitˡ⇒ H) (C.unitˡ⇐ H)))
                          (D.≈-trans (w-cong (C.≅₂isoʳ (C.unitorˡ H))) w-id))))) ⟩
        D.unitˡ⇐ h D.• (ε h D.• (D.id₂ D.• w (Φ₂ (D.unitˡ⇒ h))))
          ≈⟨ D.•-congʳ (D.•-congʳ D.•-identityˡ) ⟩
        D.unitˡ⇐ h D.• (ε h D.• w (Φ₂ (D.unitˡ⇒ h)))
          ≈⟨ D.•-congʳ (Φ₂-β (D.unitˡ⇒ h)) ⟩
        D.unitˡ⇐ h D.• (D.unitˡ⇒ h D.• ε (D.id₁ D.∘₁ h))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (D.unitˡ⇐ h D.• D.unitˡ⇒ h) D.• ε (D.id₁ D.∘₁ h)
          ≈⟨ D.•-congˡ (D.≅₂isoˡ (D.unitorˡ h)) ⟩
        D.id₂ D.• ε (D.id₁ D.∘₁ h)
          ≈⟨ D.•-identityˡ ⟩
        ε (D.id₁ D.∘₁ h)
          ≈⟨ D.≈-sym D.•-identityʳ ⟩
        ε (D.id₁ D.∘₁ h) D.• D.id₂
          ≈⟨ D.•-congʳ (D.≈-sym w-id) ⟩
        ε (D.id₁ D.∘₁ h) D.• w C.id₂ ∎)

  -- the coherence of F, solved for the comparison in the ⇐ direction
  F-∘⇐-assoc : {a b c d : C.Obj} (x : c C.⇒₁ d) (y : b C.⇒₁ c) (z : a C.⇒₁ b) →
               (F.F₁ x D.◁ F.F-∘⇐ y z) D.• F.F-∘⇐ x (y C.∘₁ z)
               D.≈ D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z) D.•
                     ((F.F-∘⇐ x y D.▷ F.F₁ z) D.•
                       (F.F-∘⇐ (x C.∘₁ y) z D.• F.F₂ (C.assoc⇐ x y z)))
  F-∘⇐-assoc x y z = D.≈-sym (begin
    D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z) D.•
      ((F.F-∘⇐ x y D.▷ F.F₁ z) D.•
        (F.F-∘⇐ (x C.∘₁ y) z D.• F.F₂ (C.assoc⇐ x y z)))
      ≈⟨ D.•-congʳ (D.≈-sym D.•-assoc) ⟩
    D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z) D.•
      (((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z)
        D.• F.F₂ (C.assoc⇐ x y z))
      ≈⟨ D.≈-sym D.•-assoc ⟩
    (D.assoc⇒ (F.F₁ x) (F.F₁ y) (F.F₁ z) D.•
      ((F.F-∘⇐ x y D.▷ F.F₁ z) D.• F.F-∘⇐ (x C.∘₁ y) z))
      D.• F.F₂ (C.assoc⇐ x y z)
      ≈⟨ D.•-congˡ (F₂-assoc x y z) ⟩
    ((F.F₁ x D.◁ F.F-∘⇐ y z) D.•
      (F.F-∘⇐ x (y C.∘₁ z) D.• F.F₂ (C.assoc⇒ x y z)))
      D.• F.F₂ (C.assoc⇐ x y z)
      ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
    (F.F₁ x D.◁ F.F-∘⇐ y z) D.•
      (F.F-∘⇐ x (y C.∘₁ z) D.•
        (F.F₂ (C.assoc⇒ x y z) D.• F.F₂ (C.assoc⇐ x y z)))
      ≈⟨ D.•-congʳ (D.•-congʳ
           (D.≈-trans (D.≈-sym (F.F₂-• (C.assoc⇒ x y z) (C.assoc⇐ x y z)))
           (D.≈-trans (F.F₂-cong (C.≅₂isoʳ (C.associator x y z))) F.F₂-id₂))) ⟩
    (F.F₁ x D.◁ F.F-∘⇐ y z) D.• (F.F-∘⇐ x (y C.∘₁ z) D.• D.id₂)
      ≈⟨ D.•-congʳ D.•-identityʳ ⟩
    (F.F₁ x D.◁ F.F-∘⇐ y z) D.• F.F-∘⇐ x (y C.∘₁ z) ∎)
    where open D.⇒₂-Reasoning

  -- the comparison for precomposition is compatible with composition
  Φ-naturalˡ-∘ : {x x' x'' : C.Obj} (f : x' C.⇒₁ x) (f' : x'' C.⇒₁ x')
                 {y : D.Obj} (h : F.F₀ x D.⇒₁ y) →
                 (Φ-natˡ⇒ (f C.∘₁ f') h C.•
                   (Φ₂ (h D.◁ F.F-∘⇒ f f') C.•
                     Φ₂ (D.assoc⇒ h (F.F₁ f) (F.F₁ f'))))
                 C.≈ (C.assoc⇒ (⇑₁ h) f f' C.•
                       ((Φ-natˡ⇒ f h C.▷ f') C.• Φ-natˡ⇒ f' (h D.∘₁ F.F₁ f)))
  Φ-naturalˡ-∘ {x} {x'} {x''} f f' {y} h = C.Hom.inv-cong iL iR core
    where
      open D.⇒₂-Reasoning

      uy = u y
      H  = ⇑₁ h
      FH = F.F₁ H
      Ff = F.F₁ f
      Ff' = F.F₁ f'
      A₁ = h D.◁ F.F-∘⇐ f f'
      A₂ = D.assoc⇐ h Ff Ff'
      φ  = F.F₂ (Φ-natˡ⇐ f h)

      iL : C.Invertible₂ (Φ-natˡ⇒ (f C.∘₁ f') h C.•
             (Φ₂ (h D.◁ F.F-∘⇒ f f') C.• Φ₂ (D.assoc⇒ h Ff Ff')))
      iL = C.Hom.∘-invertible
             (C.Hom.inv-invertible (Φ-natˡ-inv (f C.∘₁ f') h))
             (C.Hom.∘-invertible
               (Φ₂-inv (◁-inv h (D.invertible-≅₂ (F.F-∘ f f'))))
               (Φ₂-inv (assoc⇒-inv h Ff Ff')))

      iR : C.Invertible₂ (C.assoc⇒ (⇑₁ h) f f' C.•
             ((Φ-natˡ⇒ f h C.▷ f') C.• Φ-natˡ⇒ f' (h D.∘₁ Ff)))
      iR = C.Hom.∘-invertible (Cassoc⇒-inv (⇑₁ h) f f')
             (C.Hom.∘-invertible
               (C▷-inv f' (C.Hom.inv-invertible (Φ-natˡ-inv f h)))
               (C.Hom.inv-invertible (Φ-natˡ-inv f' (h D.∘₁ Ff))))

      -- the right-hand side, with the factorizations peeled off
      rightReduce : Pˡ f' (h D.∘₁ Ff) D.• w (Φ-natˡ⇐ f h C.▷ f')
                    D.≈ (Pˡ f h D.▷ Ff') D.•
                          (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
                            (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f'))
      rightReduce = begin
        Pˡ f' (h D.∘₁ Ff) D.• w (Φ-natˡ⇐ f h C.▷ f')
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        (ε (h D.∘₁ Ff) D.▷ Ff') D.•
          (D.assoc⇐ uy (F.F₁ (⇑₁ (h D.∘₁ Ff))) Ff' D.•
            ((uy D.◁ F.F-∘⇐ (⇑₁ (h D.∘₁ Ff)) f') D.• w (Φ-natˡ⇐ f h C.▷ f')))
          ≈⟨ D.•-congʳ (D.•-congʳ
               (D.≈-trans (D.≈-sym (D.◁-• uy (F.F-∘⇐ (⇑₁ (h D.∘₁ Ff)) f')
                                             (F.F₂ (Φ-natˡ⇐ f h C.▷ f'))))
               (D.≈-trans (D.◁-cong uy (F.F-∘-natural⇐ (Φ-natˡ⇐ f h)
                                         (C.id₂ {f = f'})))
               (D.≈-trans (D.◁-• uy (φ D.∗ F.F₂ (C.id₂ {f = f'}))
                                    (F.F-∘⇐ (H C.∘₁ f) f'))
                          (D.•-congˡ (D.◁-cong uy
                            (D.∗-cong D.≈-refl F.F₂-id₂))))))) ⟩
        (ε (h D.∘₁ Ff) D.▷ Ff') D.•
          (D.assoc⇐ uy (F.F₁ (⇑₁ (h D.∘₁ Ff))) Ff' D.•
            ((uy D.◁ (φ D.▷ Ff')) D.• (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f')))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.assoc-natural⇐ (D.id₂ {f = uy}) φ
                                       (D.id₂ {f = Ff'})))
                          D.•-assoc)) ⟩
        (ε (h D.∘₁ Ff) D.▷ Ff') D.•
          (((uy D.◁ φ) D.▷ Ff') D.•
            (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
              (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f')))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.•-congˡ (D.≈-trans (D.≈-sym (D.▷-• (ε (h D.∘₁ Ff))
                                                   (w (Φ-natˡ⇐ f h)) Ff'))
                                   (D.▷-cong Ff' (⇑₂-β (Pˡ f h))))) ⟩
        (Pˡ f h D.▷ Ff') D.•
          (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
            (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f')) ∎

      N = ((ε h D.▷ Ff) D.▷ Ff') D.•
            ((D.assoc⇐ uy FH Ff D.▷ Ff') D.•
              (D.assoc⇐ uy (FH D.∘₁ Ff) Ff' D.•
                ((uy D.◁ (F.F-∘⇐ H f D.▷ Ff')) D.•
                  ((uy D.◁ F.F-∘⇐ (H C.∘₁ f) f') D.•
                    (uy D.◁ F.F₂ (C.assoc⇐ H f f'))))))

      leftN : A₂ D.• (A₁ D.• Pˡ (f C.∘₁ f') h) D.≈ N
      leftN = begin
        A₂ D.• (A₁ D.• Pˡ (f C.∘₁ f') h)
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym (D.exchange (ε h) (F.F-∘⇐ f f'))))
                          D.•-assoc)) ⟩
        A₂ D.• ((ε h D.▷ (Ff D.∘₁ Ff')) D.•
          (((uy D.∘₁ FH) D.◁ F.F-∘⇐ f f') D.•
            (D.assoc⇐ uy FH (F.F₁ (f C.∘₁ f')) D.•
              (uy D.◁ F.F-∘⇐ H (f C.∘₁ f')))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym
                 (D.≈-trans (D.assoc-natural⇐ (D.id₂ {f = uy}) (D.id₂ {f = FH})
                              (F.F-∘⇐ f f'))
                            (D.•-congˡ (D.∗-cong (D.∗-id uy FH) D.≈-refl)))))
                          D.•-assoc))) ⟩
        A₂ D.• ((ε h D.▷ (Ff D.∘₁ Ff')) D.•
          (D.assoc⇐ uy FH (Ff D.∘₁ Ff') D.•
            ((uy D.◁ (FH D.◁ F.F-∘⇐ f f')) D.• (uy D.◁ F.F-∘⇐ H (f C.∘₁ f')))))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.≈-trans (D.•-congˡ
               (D.≈-trans (D.•-congʳ (D.∗-cong D.≈-refl
                            (D.≈-sym (D.∗-id Ff Ff'))))
                          (D.assoc-natural⇐ (ε h) (D.id₂ {f = Ff})
                                            (D.id₂ {f = Ff'}))))
                        D.•-assoc) ⟩
        ((ε h D.▷ Ff) D.▷ Ff') D.•
          (D.assoc⇐ (uy D.∘₁ FH) Ff Ff' D.•
            (D.assoc⇐ uy FH (Ff D.∘₁ Ff') D.•
              ((uy D.◁ (FH D.◁ F.F-∘⇐ f f')) D.•
                (uy D.◁ F.F-∘⇐ H (f C.∘₁ f')))))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ (D.pentagon⇐ uy FH Ff Ff'))) ⟩
        ((ε h D.▷ Ff) D.▷ Ff') D.•
          ((((D.assoc⇐ uy FH Ff D.▷ Ff') D.• D.assoc⇐ uy (FH D.∘₁ Ff) Ff')
            D.• (uy D.◁ D.assoc⇐ FH Ff Ff')) D.•
            ((uy D.◁ (FH D.◁ F.F-∘⇐ f f')) D.• (uy D.◁ F.F-∘⇐ H (f C.∘₁ f'))))
          ≈⟨ D.•-congʳ (D.≈-trans D.•-assoc (D.≈-trans D.•-assoc
               (D.•-congʳ (D.•-congʳ (D.≈-sym D.•-assoc))))) ⟩
        ((ε h D.▷ Ff) D.▷ Ff') D.•
          ((D.assoc⇐ uy FH Ff D.▷ Ff') D.•
            (D.assoc⇐ uy (FH D.∘₁ Ff) Ff' D.•
              (((uy D.◁ D.assoc⇐ FH Ff Ff') D.• (uy D.◁ (FH D.◁ F.F-∘⇐ f f')))
                D.• (uy D.◁ F.F-∘⇐ H (f C.∘₁ f')))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.•-congʳ tailN)) ⟩
        N ∎
        where
          tailN : ((uy D.◁ D.assoc⇐ FH Ff Ff') D.•
                    (uy D.◁ (FH D.◁ F.F-∘⇐ f f'))) D.•
                    (uy D.◁ F.F-∘⇐ H (f C.∘₁ f'))
                  D.≈ (uy D.◁ (F.F-∘⇐ H f D.▷ Ff')) D.•
                        ((uy D.◁ F.F-∘⇐ (H C.∘₁ f) f') D.•
                          (uy D.◁ F.F₂ (C.assoc⇐ H f f')))
          tailN = begin
            ((uy D.◁ D.assoc⇐ FH Ff Ff') D.• (uy D.◁ (FH D.◁ F.F-∘⇐ f f')))
              D.• (uy D.◁ F.F-∘⇐ H (f C.∘₁ f'))
              ≈⟨ D.•-congˡ (D.≈-sym (D.◁-• uy (D.assoc⇐ FH Ff Ff')
                                              (FH D.◁ F.F-∘⇐ f f'))) ⟩
            (uy D.◁ (D.assoc⇐ FH Ff Ff' D.• (FH D.◁ F.F-∘⇐ f f')))
              D.• (uy D.◁ F.F-∘⇐ H (f C.∘₁ f'))
              ≈⟨ D.≈-sym (D.◁-• uy (D.assoc⇐ FH Ff Ff' D.• (FH D.◁ F.F-∘⇐ f f'))
                                   (F.F-∘⇐ H (f C.∘₁ f'))) ⟩
            uy D.◁ ((D.assoc⇐ FH Ff Ff' D.• (FH D.◁ F.F-∘⇐ f f'))
              D.• F.F-∘⇐ H (f C.∘₁ f'))
              ≈⟨ D.◁-cong uy (D.≈-trans D.•-assoc
                   (D.≈-trans (D.•-congʳ (F-∘⇐-assoc H f f'))
                   (D.≈-trans (D.≈-sym D.•-assoc)
                   (D.≈-trans (D.•-congˡ
                     (D.≅₂isoˡ (D.associator FH Ff Ff'))) D.•-identityˡ)))) ⟩
            uy D.◁ ((F.F-∘⇐ H f D.▷ Ff') D.•
              (F.F-∘⇐ (H C.∘₁ f) f' D.• F.F₂ (C.assoc⇐ H f f')))
              ≈⟨ D.≈-trans (D.◁-• uy (F.F-∘⇐ H f D.▷ Ff')
                             (F.F-∘⇐ (H C.∘₁ f) f' D.• F.F₂ (C.assoc⇐ H f f')))
                           (D.•-congʳ (D.◁-• uy (F.F-∘⇐ (H C.∘₁ f) f')
                                        (F.F₂ (C.assoc⇐ H f f')))) ⟩
            (uy D.◁ (F.F-∘⇐ H f D.▷ Ff')) D.•
              ((uy D.◁ F.F-∘⇐ (H C.∘₁ f) f') D.•
                (uy D.◁ F.F₂ (C.assoc⇐ H f f'))) ∎

      rightN : ((Pˡ f h D.▷ Ff') D.•
                 (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
                   (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f'))) D.• w (C.assoc⇐ H f f')
               D.≈ N
      rightN = begin
        ((Pˡ f h D.▷ Ff') D.•
          (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
            (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f'))) D.• w (C.assoc⇐ H f f')
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        (Pˡ f h D.▷ Ff') D.•
          (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
            ((uy D.◁ F.F-∘⇐ (H C.∘₁ f) f') D.•
              (uy D.◁ F.F₂ (C.assoc⇐ H f f'))))
          ≈⟨ D.•-congˡ (D.≈-trans (D.▷-• (ε h D.▷ Ff)
                                    (D.assoc⇐ uy FH Ff D.•
                                      (uy D.◁ F.F-∘⇐ H f)) Ff')
                       (D.•-congʳ (D.▷-• (D.assoc⇐ uy FH Ff)
                                    (uy D.◁ F.F-∘⇐ H f) Ff'))) ⟩
        (((ε h D.▷ Ff) D.▷ Ff') D.•
          ((D.assoc⇐ uy FH Ff D.▷ Ff') D.• ((uy D.◁ F.F-∘⇐ H f) D.▷ Ff'))) D.•
          (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
            ((uy D.◁ F.F-∘⇐ (H C.∘₁ f) f') D.•
              (uy D.◁ F.F₂ (C.assoc⇐ H f f'))))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc) ⟩
        ((ε h D.▷ Ff) D.▷ Ff') D.•
          ((D.assoc⇐ uy FH Ff D.▷ Ff') D.•
            (((uy D.◁ F.F-∘⇐ H f) D.▷ Ff') D.•
              (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
                ((uy D.◁ F.F-∘⇐ (H C.∘₁ f) f') D.•
                  (uy D.◁ F.F₂ (C.assoc⇐ H f f'))))))
          ≈⟨ D.•-congʳ (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.≈-trans (D.•-congˡ (D.≈-sym
                 (D.assoc-natural⇐ (D.id₂ {f = uy}) (F.F-∘⇐ H f)
                                   (D.id₂ {f = Ff'}))))
                          D.•-assoc))) ⟩
        N ∎

      core : C.Hom.inv iL C.≈ C.Hom.inv iR
      core = ⇑₂-cancel (begin
        ε ((h D.∘₁ Ff) D.∘₁ Ff') D.•
          w ((Φ₂ A₂ C.• Φ₂ A₁) C.• Φ-natˡ⇐ (f C.∘₁ f') h)
          ≈⟨ D.•-congʳ (D.≈-trans (w-• (Φ₂ A₂ C.• Φ₂ A₁)
                                       (Φ-natˡ⇐ (f C.∘₁ f') h))
                       (D.•-congˡ (w-• (Φ₂ A₂) (Φ₂ A₁)))) ⟩
        ε ((h D.∘₁ Ff) D.∘₁ Ff') D.•
          ((w (Φ₂ A₂) D.• w (Φ₂ A₁)) D.• w (Φ-natˡ⇐ (f C.∘₁ f') h))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc) (D.•-congˡ (D.≈-sym D.•-assoc)) ⟩
        ((ε ((h D.∘₁ Ff) D.∘₁ Ff') D.• w (Φ₂ A₂)) D.• w (Φ₂ A₁)) D.•
          w (Φ-natˡ⇐ (f C.∘₁ f') h)
          ≈⟨ D.•-congˡ (D.•-congˡ (Φ₂-β A₂)) ⟩
        ((A₂ D.• ε (h D.∘₁ (Ff D.∘₁ Ff'))) D.• w (Φ₂ A₁)) D.•
          w (Φ-natˡ⇐ (f C.∘₁ f') h)
          ≈⟨ D.•-congˡ (D.≈-trans D.•-assoc (D.•-congʳ (Φ₂-β A₁))) ⟩
        (A₂ D.• (A₁ D.• ε (h D.∘₁ F.F₁ (f C.∘₁ f')))) D.•
          w (Φ-natˡ⇐ (f C.∘₁ f') h)
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ (D.≈-trans D.•-assoc
               (D.•-congʳ (⇑₂-β (Pˡ (f C.∘₁ f') h))))) ⟩
        A₂ D.• (A₁ D.• Pˡ (f C.∘₁ f') h)
          ≈⟨ leftN ⟩
        N
          ≈⟨ D.≈-sym rightN ⟩
        ((Pˡ f h D.▷ Ff') D.•
          (D.assoc⇐ uy (F.F₁ (H C.∘₁ f)) Ff' D.•
            (uy D.◁ F.F-∘⇐ (H C.∘₁ f) f'))) D.• w (C.assoc⇐ H f f')
          ≈⟨ D.•-congˡ (D.≈-sym rightReduce) ⟩
        (Pˡ f' (h D.∘₁ Ff) D.• w (Φ-natˡ⇐ f h C.▷ f')) D.• w (C.assoc⇐ H f f')
          ≈⟨ D.•-congˡ (D.•-congˡ (D.≈-sym (⇑₂-β (Pˡ f' (h D.∘₁ Ff))))) ⟩
        ((ε ((h D.∘₁ Ff) D.∘₁ Ff') D.• w (Φ-natˡ⇐ f' (h D.∘₁ Ff))) D.•
          w (Φ-natˡ⇐ f h C.▷ f')) D.• w (C.assoc⇐ H f f')
          ≈⟨ D.≈-trans (D.•-congˡ D.•-assoc) D.•-assoc ⟩
        ε ((h D.∘₁ Ff) D.∘₁ Ff') D.•
          ((w (Φ-natˡ⇐ f' (h D.∘₁ Ff)) D.• w (Φ-natˡ⇐ f h C.▷ f')) D.•
            w (C.assoc⇐ H f f'))
          ≈⟨ D.•-congʳ (D.≈-sym (D.≈-trans
               (w-• (Φ-natˡ⇐ f' (h D.∘₁ Ff) C.• (Φ-natˡ⇐ f h C.▷ f'))
                    (C.assoc⇐ H f f'))
               (D.•-congˡ (w-• (Φ-natˡ⇐ f' (h D.∘₁ Ff))
                               (Φ-natˡ⇐ f h C.▷ f'))))) ⟩
        ε ((h D.∘₁ Ff) D.∘₁ Ff') D.•
          w ((Φ-natˡ⇐ f' (h D.∘₁ Ff) C.• (Φ-natˡ⇐ f h C.▷ f'))
            C.• C.assoc⇐ H f f') ∎)

  -- Pʳ is the pasting of an ε-square with a final ε-square
  Pʳ-fpaste : {x : C.Obj} {y y' : D.Obj} (g : y D.⇒₁ y') (k : F.F₀ x D.⇒₁ y) →
              Pʳ g k
              D.≈ D-P.fpaste (u y) (u y') (F.F₁ (⇑₁ k)) (F.F₁ (R₁ g)) k g
                    (ε (g D.∘₁ u y)) (ε k)
                  D.• (u y' D.◁ F.F-∘⇐ (R₁ g) (⇑₁ k))
  Pʳ-fpaste g k =
    D.≈-sym (D.≈-trans D.•-assoc (D.•-congʳ
            (D.≈-trans D.•-assoc (D.•-congʳ D.•-assoc))))

  -- the comparison for postcomposition is compatible with composition
  Φ-naturalʳ-∘ : {x : C.Obj} {y y' y'' : D.Obj}
                 (g' : y' D.⇒₁ y'') (g : y D.⇒₁ y') (h : F.F₀ x D.⇒₁ y) →
                 (Φ-natʳ⇒ (g' D.∘₁ g) h C.• Φ₂ (D.assoc⇐ g' g h))
                 C.≈ ((R-∘⇒ g' g C.▷ ⇑₁ h) C.•
                       (C.assoc⇐ (R₁ g') (R₁ g) (⇑₁ h) C.•
                         ((R₁ g' C.◁ Φ-natʳ⇒ g h) C.• Φ-natʳ⇒ g' (g D.∘₁ h))))
  Φ-naturalʳ-∘ {x} {y} {y'} {y''} g' g h = C.Hom.inv-cong iL iR core
    where
      open D.⇒₂-Reasoning

      u₀ = u y
      u₁ = u y'
      u₂ = u y''
      H  = ⇑₁ h
      FH = F.F₁ H
      Rg  = R₁ g
      Rg' = R₁ g'
      FRg  = F.F₁ Rg
      FRg' = F.F₁ Rg'
      εh   = ε h
      εg   = ε (g D.∘₁ u₀)
      εg'  = ε (g' D.∘₁ u₁)
      εgg' = ε ((g' D.∘₁ g) D.∘₁ u₀)
      A    = D.assoc⇒ g' g h
      ψ    = F.F₂ (R-∘⇒ g' g)
      φ    = F.F₂ (Φ-natʳ⇐ g h)
      pst  = D-P.paste u₀ u₁ u₂ FRg FRg' g g' εg' εg
      Qf   = D-P.fpaste u₁ u₂ (FRg D.∘₁ FH) FRg' (g D.∘₁ h) g' εg'
               (D-P.fpaste u₀ u₁ FH FRg h g εg εh)
      T₂   = u₂ D.◁ F.F-∘⇐ (Rg' C.∘₁ Rg) H

      R-∘-inv : C.Invertible₂ (R-∘⇒ g' g)
      R-∘-inv = ⇑₂-invertible (R-P-inv g' g)

      iL : C.Invertible₂ (Φ-natʳ⇒ (g' D.∘₁ g) h C.• Φ₂ (D.assoc⇐ g' g h))
      iL = C.Hom.∘-invertible
             (C.Hom.inv-invertible (Φ-natʳ-inv (g' D.∘₁ g) h))
             (Φ₂-inv (assoc⇐-inv g' g h))

      iR : C.Invertible₂ ((R-∘⇒ g' g C.▷ ⇑₁ h) C.•
             (C.assoc⇐ Rg' Rg H C.•
               ((Rg' C.◁ Φ-natʳ⇒ g h) C.• Φ-natʳ⇒ g' (g D.∘₁ h))))
      iR = C.Hom.∘-invertible (C▷-inv H R-∘-inv)
             (C.Hom.∘-invertible
               (C.invertible-≅₂ (C.≅₂-sym (C.associator Rg' Rg H)))
               (C.Hom.∘-invertible
                 (C◁-inv Rg' (C.Hom.inv-invertible (Φ-natʳ-inv g h)))
                 (C.Hom.inv-invertible (Φ-natʳ-inv g' (g D.∘₁ h)))))

      leftRed : (A D.• Pʳ (g' D.∘₁ g) h) D.• w (R-∘⇒ g' g C.▷ H)
                D.≈ (Qf D.• (u₂ D.◁ D.assoc⇒ FRg' FRg FH)) D.•
                      ((u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)) D.• T₂)
      leftRed = begin
        (A D.• Pʳ (g' D.∘₁ g) h) D.• w (R-∘⇒ g' g C.▷ H)
          ≈⟨ D.•-congˡ (D.•-congʳ (Pʳ-fpaste (g' D.∘₁ g) h)) ⟩
        (A D.• (D-P.fpaste u₀ u₂ FH (F.F₁ (R₁ (g' D.∘₁ g))) h (g' D.∘₁ g)
                  εgg' εh
                D.• (u₂ D.◁ F.F-∘⇐ (R₁ (g' D.∘₁ g)) H)))
          D.• w (R-∘⇒ g' g C.▷ H)
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ (D.≈-trans D.•-assoc
               (D.•-congʳ (D.≈-trans (D.≈-sym (D.◁-• u₂
                             (F.F-∘⇐ (R₁ (g' D.∘₁ g)) H)
                             (F.F₂ (R-∘⇒ g' g C.▷ H))))
               (D.≈-trans (D.◁-cong u₂ (F.F-∘-natural⇐ (R-∘⇒ g' g)
                                         (C.id₂ {f = H})))
               (D.≈-trans (D.◁-• u₂ (ψ D.∗ F.F₂ (C.id₂ {f = H}))
                                    (F.F-∘⇐ (Rg' C.∘₁ Rg) H))
                          (D.•-congˡ (D.◁-cong u₂
                            (D.∗-cong D.≈-refl F.F₂-id₂))))))))) ⟩
        A D.• (D-P.fpaste u₀ u₂ FH (F.F₁ (R₁ (g' D.∘₁ g))) h (g' D.∘₁ g) εgg' εh
          D.• ((u₂ D.◁ (ψ D.▷ FH)) D.• T₂))
          ≈⟨ D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ (D-P.fpaste-▷ u₀ u₂ FH (F.F₁ (R₁ (g' D.∘₁ g)))
                 (F.F₁ (Rg' C.∘₁ Rg)) h (g' D.∘₁ g) εgg' εh ψ))) ⟩
        A D.• (D-P.fpaste u₀ u₂ FH (F.F₁ (Rg' C.∘₁ Rg)) h (g' D.∘₁ g)
                 (εgg' D.• (u₂ D.◁ ψ)) εh
          D.• T₂)
          ≈⟨ D.•-congʳ (D.•-congˡ (D-P.fpaste-cong u₀ u₂ FH
               (F.F₁ (Rg' C.∘₁ Rg)) h (g' D.∘₁ g)
               (D.≈-trans (⇑₂-β (R-P g' g)) (R-P-paste g' g)) D.≈-refl)) ⟩
        A D.• (D-P.fpaste u₀ u₂ FH (F.F₁ (Rg' C.∘₁ Rg)) h (g' D.∘₁ g)
                 (pst D.• (u₂ D.◁ F.F-∘⇐ Rg' Rg)) εh
          D.• T₂)
          ≈⟨ D.•-congʳ (D.•-congˡ (D.≈-sym (D-P.fpaste-▷ u₀ u₂ FH
               (FRg' D.∘₁ FRg) (F.F₁ (Rg' C.∘₁ Rg)) h (g' D.∘₁ g)
               pst εh (F.F-∘⇐ Rg' Rg)))) ⟩
        A D.• ((D-P.fpaste u₀ u₂ FH (FRg' D.∘₁ FRg) h (g' D.∘₁ g) pst εh
                 D.• (u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)))
          D.• T₂)
          ≈⟨ D.≈-trans (D.•-congʳ D.•-assoc) (D.≈-sym D.•-assoc) ⟩
        (A D.• D-P.fpaste u₀ u₂ FH (FRg' D.∘₁ FRg) h (g' D.∘₁ g) pst εh) D.•
          ((u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)) D.• T₂)
          ≈⟨ D.•-congˡ (D-P.fpaste-assoc u₀ u₁ u₂ FH FRg FRg' h g g' εg' εg εh) ⟩
        (Qf D.• (u₂ D.◁ D.assoc⇒ FRg' FRg FH)) D.•
          ((u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)) D.• T₂) ∎

      rightRed : Pʳ g' (g D.∘₁ h) D.•
                   (w (Rg' C.◁ Φ-natʳ⇐ g h) D.• w (C.assoc⇒ Rg' Rg H))
                 D.≈ (Qf D.• (u₂ D.◁ (FRg' D.◁ F.F-∘⇐ Rg H))) D.•
                       ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.•
                         (u₂ D.◁ F.F₂ (C.assoc⇒ Rg' Rg H)))
      rightRed = begin
        Pʳ g' (g D.∘₁ h) D.•
          (w (Rg' C.◁ Φ-natʳ⇐ g h) D.• w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.•-congˡ (Pʳ-fpaste g' (g D.∘₁ h)) ⟩
        (D-P.fpaste u₁ u₂ (F.F₁ (⇑₁ (g D.∘₁ h))) FRg' (g D.∘₁ h) g' εg'
           (ε (g D.∘₁ h))
          D.• (u₂ D.◁ F.F-∘⇐ Rg' (⇑₁ (g D.∘₁ h)))) D.•
          (w (Rg' C.◁ Φ-natʳ⇐ g h) D.• w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ (D.≈-trans (D.≈-sym D.•-assoc)
               (D.•-congˡ (D.≈-trans (D.≈-sym (D.◁-• u₂
                             (F.F-∘⇐ Rg' (⇑₁ (g D.∘₁ h)))
                             (F.F₂ (Rg' C.◁ Φ-natʳ⇐ g h))))
               (D.≈-trans (D.◁-cong u₂ (F.F-∘-natural⇐ (C.id₂ {f = Rg'})
                                         (Φ-natʳ⇐ g h)))
               (D.≈-trans (D.◁-• u₂ (F.F₂ (C.id₂ {f = Rg'}) D.∗ φ)
                                    (F.F-∘⇐ Rg' (Rg C.∘₁ H)))
                          (D.•-congˡ (D.◁-cong u₂
                            (D.∗-cong F.F₂-id₂ D.≈-refl))))))))) ⟩
        D-P.fpaste u₁ u₂ (F.F₁ (⇑₁ (g D.∘₁ h))) FRg' (g D.∘₁ h) g' εg'
          (ε (g D.∘₁ h)) D.•
          (((u₂ D.◁ (FRg' D.◁ φ)) D.• (u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H))) D.•
            w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.•-congʳ D.•-assoc ⟩
        D-P.fpaste u₁ u₂ (F.F₁ (⇑₁ (g D.∘₁ h))) FRg' (g D.∘₁ h) g' εg'
          (ε (g D.∘₁ h)) D.•
          ((u₂ D.◁ (FRg' D.◁ φ)) D.•
            ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.• w (C.assoc⇒ Rg' Rg H)))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc)
             (D.•-congˡ (D-P.fpaste-◁ u₁ u₂ (F.F₁ (⇑₁ (g D.∘₁ h)))
               (F.F₁ (Rg C.∘₁ H)) FRg' (g D.∘₁ h) g' εg' (ε (g D.∘₁ h)) φ)) ⟩
        D-P.fpaste u₁ u₂ (F.F₁ (Rg C.∘₁ H)) FRg' (g D.∘₁ h) g' εg'
          (ε (g D.∘₁ h) D.• (u₁ D.◁ φ)) D.•
          ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.• w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.•-congˡ (D-P.fpaste-cong u₁ u₂ (F.F₁ (Rg C.∘₁ H)) FRg'
               (g D.∘₁ h) g' D.≈-refl
               (D.≈-trans (⇑₂-β (Pʳ g h)) (Pʳ-fpaste g h))) ⟩
        D-P.fpaste u₁ u₂ (F.F₁ (Rg C.∘₁ H)) FRg' (g D.∘₁ h) g' εg'
          (D-P.fpaste u₀ u₁ FH FRg h g εg εh D.• (u₁ D.◁ F.F-∘⇐ Rg H)) D.•
          ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.• w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.•-congˡ (D.≈-sym (D-P.fpaste-◁ u₁ u₂ (FRg D.∘₁ FH)
               (F.F₁ (Rg C.∘₁ H)) FRg' (g D.∘₁ h) g' εg'
               (D-P.fpaste u₀ u₁ FH FRg h g εg εh) (F.F-∘⇐ Rg H))) ⟩
        (Qf D.• (u₂ D.◁ (FRg' D.◁ F.F-∘⇐ Rg H))) D.•
          ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.•
            (u₂ D.◁ F.F₂ (C.assoc⇒ Rg' Rg H))) ∎

      tail : (u₂ D.◁ D.assoc⇒ FRg' FRg FH) D.•
               ((u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)) D.• T₂)
             D.≈ (u₂ D.◁ (FRg' D.◁ F.F-∘⇐ Rg H)) D.•
                   ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.•
                     (u₂ D.◁ F.F₂ (C.assoc⇒ Rg' Rg H)))
      tail = begin
        (u₂ D.◁ D.assoc⇒ FRg' FRg FH) D.•
          ((u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)) D.• T₂)
          ≈⟨ D.•-congʳ (D.≈-sym (D.◁-• u₂ (F.F-∘⇐ Rg' Rg D.▷ FH)
                                          (F.F-∘⇐ (Rg' C.∘₁ Rg) H))) ⟩
        (u₂ D.◁ D.assoc⇒ FRg' FRg FH) D.•
          (u₂ D.◁ ((F.F-∘⇐ Rg' Rg D.▷ FH) D.• F.F-∘⇐ (Rg' C.∘₁ Rg) H))
          ≈⟨ D.≈-sym (D.◁-• u₂ (D.assoc⇒ FRg' FRg FH)
                               ((F.F-∘⇐ Rg' Rg D.▷ FH)
                                 D.• F.F-∘⇐ (Rg' C.∘₁ Rg) H)) ⟩
        u₂ D.◁ (D.assoc⇒ FRg' FRg FH D.•
          ((F.F-∘⇐ Rg' Rg D.▷ FH) D.• F.F-∘⇐ (Rg' C.∘₁ Rg) H))
          ≈⟨ D.◁-cong u₂ (F₂-assoc Rg' Rg H) ⟩
        u₂ D.◁ ((FRg' D.◁ F.F-∘⇐ Rg H) D.•
          (F.F-∘⇐ Rg' (Rg C.∘₁ H) D.• F.F₂ (C.assoc⇒ Rg' Rg H)))
          ≈⟨ D.≈-trans (D.◁-• u₂ (FRg' D.◁ F.F-∘⇐ Rg H)
                          (F.F-∘⇐ Rg' (Rg C.∘₁ H)
                            D.• F.F₂ (C.assoc⇒ Rg' Rg H)))
                       (D.•-congʳ (D.◁-• u₂ (F.F-∘⇐ Rg' (Rg C.∘₁ H))
                                    (F.F₂ (C.assoc⇒ Rg' Rg H)))) ⟩
        (u₂ D.◁ (FRg' D.◁ F.F-∘⇐ Rg H)) D.•
          ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.•
            (u₂ D.◁ F.F₂ (C.assoc⇒ Rg' Rg H))) ∎

      X = (Φ-natʳ⇐ g' (g D.∘₁ h) C.• (Rg' C.◁ Φ-natʳ⇐ g h)) C.•
            C.assoc⇒ Rg' Rg H

      E : (Φ₂ A C.• Φ-natʳ⇐ (g' D.∘₁ g) h) C.• (R-∘⇒ g' g C.▷ H) C.≈ X
      E = ⇑₂-cancel (begin
        ε (g' D.∘₁ (g D.∘₁ h)) D.•
          w ((Φ₂ A C.• Φ-natʳ⇐ (g' D.∘₁ g) h) C.• (R-∘⇒ g' g C.▷ H))
          ≈⟨ D.•-congʳ (D.≈-trans (w-• (Φ₂ A C.• Φ-natʳ⇐ (g' D.∘₁ g) h)
                                       (R-∘⇒ g' g C.▷ H))
                       (D.•-congˡ (w-• (Φ₂ A) (Φ-natʳ⇐ (g' D.∘₁ g) h)))) ⟩
        ε (g' D.∘₁ (g D.∘₁ h)) D.•
          ((w (Φ₂ A) D.• w (Φ-natʳ⇐ (g' D.∘₁ g) h)) D.• w (R-∘⇒ g' g C.▷ H))
          ≈⟨ D.≈-trans (D.≈-sym D.•-assoc) (D.•-congˡ (D.≈-sym D.•-assoc)) ⟩
        ((ε (g' D.∘₁ (g D.∘₁ h)) D.• w (Φ₂ A)) D.•
          w (Φ-natʳ⇐ (g' D.∘₁ g) h)) D.• w (R-∘⇒ g' g C.▷ H)
          ≈⟨ D.•-congˡ (D.•-congˡ (Φ₂-β A)) ⟩
        ((A D.• ε ((g' D.∘₁ g) D.∘₁ h)) D.• w (Φ-natʳ⇐ (g' D.∘₁ g) h)) D.•
          w (R-∘⇒ g' g C.▷ H)
          ≈⟨ D.•-congˡ (D.≈-trans D.•-assoc
               (D.•-congʳ (⇑₂-β (Pʳ (g' D.∘₁ g) h)))) ⟩
        (A D.• Pʳ (g' D.∘₁ g) h) D.• w (R-∘⇒ g' g C.▷ H)
          ≈⟨ leftRed ⟩
        (Qf D.• (u₂ D.◁ D.assoc⇒ FRg' FRg FH)) D.•
          ((u₂ D.◁ (F.F-∘⇐ Rg' Rg D.▷ FH)) D.• T₂)
          ≈⟨ D.≈-trans D.•-assoc (D.≈-trans (D.•-congʳ tail) (D.≈-sym D.•-assoc)) ⟩
        (Qf D.• (u₂ D.◁ (FRg' D.◁ F.F-∘⇐ Rg H))) D.•
          ((u₂ D.◁ F.F-∘⇐ Rg' (Rg C.∘₁ H)) D.•
            (u₂ D.◁ F.F₂ (C.assoc⇒ Rg' Rg H)))
          ≈⟨ D.≈-sym rightRed ⟩
        Pʳ g' (g D.∘₁ h) D.•
          (w (Rg' C.◁ Φ-natʳ⇐ g h) D.• w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.•-congˡ (D.≈-sym (⇑₂-β (Pʳ g' (g D.∘₁ h)))) ⟩
        (ε (g' D.∘₁ (g D.∘₁ h)) D.• w (Φ-natʳ⇐ g' (g D.∘₁ h))) D.•
          (w (Rg' C.◁ Φ-natʳ⇐ g h) D.• w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.≈-trans D.•-assoc (D.•-congʳ (D.≈-sym D.•-assoc)) ⟩
        ε (g' D.∘₁ (g D.∘₁ h)) D.•
          ((w (Φ-natʳ⇐ g' (g D.∘₁ h)) D.• w (Rg' C.◁ Φ-natʳ⇐ g h)) D.•
            w (C.assoc⇒ Rg' Rg H))
          ≈⟨ D.•-congʳ (D.≈-sym (D.≈-trans
               (w-• (Φ-natʳ⇐ g' (g D.∘₁ h) C.• (Rg' C.◁ Φ-natʳ⇐ g h))
                    (C.assoc⇒ Rg' Rg H))
               (D.•-congˡ (w-• (Φ-natʳ⇐ g' (g D.∘₁ h))
                               (Rg' C.◁ Φ-natʳ⇐ g h))))) ⟩
        ε (g' D.∘₁ (g D.∘₁ h)) D.• w X ∎)

      core : C.Hom.inv iL C.≈ C.Hom.inv iR
      core = C.Hom.∘-cancelʳ (C▷-inv H R-∘-inv)
        (C.≈-trans E (C.≈-sym (C.≈-trans C.•-assoc
          (C.≈-trans (C.•-congʳ
            (C.≈-trans (C.≈-sym (C.▷-• (C.Hom.inv R-∘-inv) (R-∘⇒ g' g) H))
            (C.≈-trans (C.▷-cong H (C.Hom.invˡ R-∘-inv))
                       (C.▷-id (R₁ g' C.∘₁ R₁ g) H))))
                     C.•-identityʳ))))

  ----------------------------------------------------------------------
  -- The biadjunction
  ----------------------------------------------------------------------

  -- a bifunctor with a biuniversal arrow to every object is a left
  -- biadjoint, the right biadjoint being the one built above
  biadjunction : F ⊣₂ R
  biadjunction = record
    { Φ             = Φ
    ; Ψ             = Ψ
    ; equivalence   = Φ-equivalence
    ; Φ-naturalˡ    = Φ-naturalˡ
    ; Φ-naturalʳ    = Φ-naturalʳ
    ; Φ-exchange    = Φ-exchange
    ; Φ-naturalˡ-∘  = Φ-naturalˡ-∘
    ; Φ-naturalˡ-id = Φ-naturalˡ-id
    ; Φ-naturalʳ-∘  = Φ-naturalʳ-∘
    ; Φ-naturalʳ-id = Φ-naturalʳ-id
    }
