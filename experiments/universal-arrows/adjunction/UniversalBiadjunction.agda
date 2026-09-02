------------------------------------------------------------------------
-- Biadjunctions presented by universal arrows: a bifunctor F : C → D
-- has a right biadjoint as soon as there is a biuniversal arrow from F
-- to every object of D, in the sense of Universal.agda.
--
-- This is the bicategorical analogue of the classical characterization
-- of a left adjoint: what the equivalence of Universal.agda supplies is
-- the freedom to build such an arrow in the algebraic style
-- (UniversalHA) and to use it through its universal property.
--
-- Only the definition and the data it immediately yields are here: the
-- object part R₀ of the right biadjoint, its action R₁/R₂ on 1- and
-- 2-cells, and the pointwise unit and counit. Assembling those into a
-- Bifunctor and a Biadjunction is not done — it needs the compositor of
-- R, which is a real proof, and is the natural next step.
------------------------------------------------------------------------

-- Usage: since this module and the record it defines have the same name,
-- importers should write
--
--   import adjunction.UniversalBiadjunction as UBiadj
--   open UBiadj using (UniversalBiadjunction)
--
-- so that "open UniversalBiadjunction U" unambiguously refers to the
-- record module.

module adjunction.UniversalBiadjunction where

open import Level using (Level; _⊔_)

import Bicategory as Bicat
open Bicat using (Bicategory)
import Bifunctor as Bifun
open Bifun using (Bifunctor)
import Universal as Univ
open Univ using (Universal; UniversalHA; Universal→UniversalHA)

private
  variable
    o ℓ₁ ℓ₂ e o' ℓ₁' ℓ₂' e' : Level

record UniversalBiadjunction
  {C : Bicategory o  ℓ₁  ℓ₂  e }
  {D : Bicategory o' ℓ₁' ℓ₂' e'}
  (F : Bifunctor C D)
  : Set (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e ⊔ o' ⊔ ℓ₁' ⊔ ℓ₂' ⊔ e')
  where

  private module C = Bicategory C
  private module D = Bicategory D
  private module F = Bifunctor F

  field
    -- a biuniversal arrow from F to every object
    universal : (y : D.Obj) → Universal F y

  private module U (y : D.Obj) = Universal (universal y)

  -- the same data in the algebraic formulation, should it be the
  -- convenient one: the two are equivalent, see Universal.agda
  universalHA : (y : D.Obj) → UniversalHA F y
  universalHA y = Universal→UniversalHA (universal y)

  ----------------------------------------------------------------------
  -- The right biadjoint on objects, and the counit
  ----------------------------------------------------------------------

  R₀ : D.Obj → C.Obj
  R₀ y = U.U₀ y

  -- the universal 1-cell u : F (R₀ y) ⇒ y
  u : (y : D.Obj) → F.F₀ (R₀ y) D.⇒₁ y
  u y = U.U₁ y

  ----------------------------------------------------------------------
  -- Transposition, pointwise
  ----------------------------------------------------------------------

  -- all of these are the fields of Universal at the object y, with y
  -- turned into an implicit argument since it is determined by the
  -- 1-cell being transposed
  ⇑₁ : {x : C.Obj} {y : D.Obj} → F.F₀ x D.⇒₁ y → x C.⇒₁ R₀ y
  ⇑₁ {y = y} = U.⇑₁ y

  ε : {x : C.Obj} {y : D.Obj} (f : F.F₀ x D.⇒₁ y) →
      (u y D.∘₁ F.F₁ (⇑₁ f)) D.⇒₂ f
  ε {y = y} = U.ε y

  ε-invertible : {x : C.Obj} {y : D.Obj} (f : F.F₀ x D.⇒₁ y) →
                 D.Invertible₂ (ε f)
  ε-invertible {y = y} = U.ε-invertible y

  ε⁻¹ : {x : C.Obj} {y : D.Obj} (f : F.F₀ x D.⇒₁ y) →
        f D.⇒₂ (u y D.∘₁ F.F₁ (⇑₁ f))
  ε⁻¹ {y = y} = U.ε⁻¹ y

  ε-iso : {x : C.Obj} {y : D.Obj} (f : F.F₀ x D.⇒₁ y) →
          (u y D.∘₁ F.F₁ (⇑₁ f)) D.≅₂ f
  ε-iso {y = y} = U.ε-iso y

  ⇑₂ : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y} →
       (u y D.∘₁ F.F₁ g) D.⇒₂ f → g C.⇒₂ ⇑₁ f
  ⇑₂ {y = y} = U.⇑₂ y

  ⇑₂-β : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
         (α : (u y D.∘₁ F.F₁ g) D.⇒₂ f) →
         ε f D.• (u y D.◁ F.F₂ (⇑₂ α)) D.≈ α
  ⇑₂-β {y = y} = U.⇑₂-β y

  ⇑₂-unique : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
              {α : (u y D.∘₁ F.F₁ g) D.⇒₂ f} (β : g C.⇒₂ ⇑₁ f) →
              ε f D.• (u y D.◁ F.F₂ β) D.≈ α → β C.≈ ⇑₂ α
  ⇑₂-unique {y = y} = U.⇑₂-unique y

  ⇑₂-cong : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
            {α β : (u y D.∘₁ F.F₁ g) D.⇒₂ f} → α D.≈ β → ⇑₂ α C.≈ ⇑₂ β
  ⇑₂-cong {y = y} = U.⇑₂-cong y

  ⇑₂-cancel : {x : C.Obj} {y : D.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ R₀ y}
              {α β : g C.⇒₂ ⇑₁ f} →
              ε f D.• (u y D.◁ F.F₂ α) D.≈ ε f D.• (u y D.◁ F.F₂ β) → α C.≈ β
  ⇑₂-cancel {y = y} = U.⇑₂-cancel y

  ----------------------------------------------------------------------
  -- The unit
  ----------------------------------------------------------------------

  η : {x : C.Obj} {y : D.Obj} (g : x C.⇒₁ R₀ y) →
      g C.⇒₂ ⇑₁ (u y D.∘₁ F.F₁ g)
  η {y = y} = U.η y

  η-invertible : {x : C.Obj} {y : D.Obj} (g : x C.⇒₁ R₀ y) →
                 C.Invertible₂ (η g)
  η-invertible {y = y} = U.η-invertible y

  η⁻¹ : {x : C.Obj} {y : D.Obj} (g : x C.⇒₁ R₀ y) →
        ⇑₁ (u y D.∘₁ F.F₁ g) C.⇒₂ g
  η⁻¹ {y = y} = U.η⁻¹ y

  η-iso : {x : C.Obj} {y : D.Obj} (g : x C.⇒₁ R₀ y) →
          g C.≅₂ ⇑₁ (u y D.∘₁ F.F₁ g)
  η-iso {y = y} = U.η-iso y

  ----------------------------------------------------------------------
  -- The right biadjoint on 1-cells and 2-cells
  ----------------------------------------------------------------------

  -- R g is the transpose of g ∘ u, exactly as in the 1-categorical case
  -- (⌊_⌋ applied to g ∘ ε, in adjunction.Adjunction)
  R₁ : {y y' : D.Obj} → y D.⇒₁ y' → R₀ y C.⇒₁ R₀ y'
  R₁ {y} g = ⇑₁ (g D.∘₁ u y)

  -- and R β is the transpose of β whiskered by u, factored through ε
  R₂ : {y y' : D.Obj} {g g' : y D.⇒₁ y'} → g D.⇒₂ g' → R₁ g C.⇒₂ R₁ g'
  R₂ {y} {g = g} β = ⇑₂ ((β D.▷ u y) D.• ε (g D.∘₁ u y))

  R₂-cong : {y y' : D.Obj} {g g' : y D.⇒₁ y'} {β β' : g D.⇒₂ g'} →
            β D.≈ β' → R₂ β C.≈ R₂ β'
  R₂-cong {y} p = ⇑₂-cong (D.•-congˡ (D.▷-cong (u y) p))
