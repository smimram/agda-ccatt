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
open Fun using (Functor)
import Universal as Univ
open Univ using (Universal)
import adjunction.UniversalBiadjunction as UBiadj
open UBiadj using (UniversalBiadjunction)
import adjunction.NaturalTransformation as NatTrans
open NatTrans using (NaturalTransformation; pointwise-invertible; [_,_])
import adjunction.Adjunction as Adj
open Adj using (Adjunction; Equivalence; _⊣_)

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
