------------------------------------------------------------------------
-- Universal arrows for bicategories.
--
-- First formulation: a biuniversal arrow from a bifunctor F to an
-- object y is an object ȳ together with a 1-cell u : F ȳ → y through
-- which every 1-cell f : F x → y factors, up to an invertible 2-cell,
-- in an essentially unique way (see universal1.tex).
------------------------------------------------------------------------

module Universal where

open import Level using (Level; _⊔_)

import Bicategory as Bicat
open Bicat using (Bicategory)
import Bifunctor as Bifun
open Bifun using (Bifunctor)

private
  variable
    o ℓ₁ ℓ₂ e o' ℓ₁' ℓ₂' e' : Level

-- A biuniversal arrow from a bifunctor to an object
record Universal1
  {C : Bicategory o  ℓ₁  ℓ₂  e }
  {D : Bicategory o' ℓ₁' ℓ₂' e'}
  (F : Bifunctor C D)
  (y : Bicategory.Obj D)
  : Set (o ⊔ ℓ₁ ⊔ ℓ₂ ⊔ e ⊔ ℓ₁' ⊔ ℓ₂' ⊔ e')
  where

  private module C = Bicategory C
  private module D = Bicategory D
  private module F = Bifunctor F

  ----------------------------------------------------------------------
  -- The universal arrow
  ----------------------------------------------------------------------

  field
    -- the object ȳ…
    U₀ : C.Obj
    -- …and the 1-cell u : F ȳ ⇒ y
    U₁ : F.F₀ U₀ D.⇒₁ y

  ----------------------------------------------------------------------
  -- Factorization of 1-cells
  ----------------------------------------------------------------------

  field
    -- every 1-cell f : F x ⇒ y induces a 1-cell f̄ : x ⇒ ȳ…
    ⇑₁ : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → x C.⇒₁ U₀

    -- …through which it factors, up to an invertible 2-cell
    --
    --   F x ---- F f̄ ----> F ȳ
    --    ‖         ε f ⇓    | u
    --   F x ------- f ----> y
    ε : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → (U₁ D.∘₁ F.F₁ (⇑₁ f)) D.≅₂ f

  ε⇒ : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → (U₁ D.∘₁ F.F₁ (⇑₁ f)) D.⇒₂ f
  ε⇒ f = D.≅₂to (ε f)

  ε⇐ : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → f D.⇒₂ (U₁ D.∘₁ F.F₁ (⇑₁ f))
  ε⇐ f = D.≅₂from (ε f)

  ----------------------------------------------------------------------
  -- Factorization of 2-cells
  ----------------------------------------------------------------------

  field
    -- every 2-cell α : u ∘ F g ⇒ f induces a 2-cell α' : g ⇒ f̄…
    ⇑₂ : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀} →
         (U₁ D.∘₁ F.F₁ g) D.⇒₂ f → g C.⇒₂ ⇑₁ f

    -- …such that (u ◁ F α') followed by ε f is α…
    ⇑₂-β : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
           (α : (U₁ D.∘₁ F.F₁ g) D.⇒₂ f) →
           ε⇒ f D.• (U₁ D.◁ F.F₂ (⇑₂ α)) D.≈ α

    -- …and α' is the only such 2-cell
    ⇑₂-unique : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
                {α : (U₁ D.∘₁ F.F₁ g) D.⇒₂ f} (β : g C.⇒₂ ⇑₁ f) →
                ε⇒ f D.• (U₁ D.◁ F.F₂ β) D.≈ α → β C.≈ ⇑₂ α

  ----------------------------------------------------------------------
  -- The unit
  ----------------------------------------------------------------------

  -- the 2-cell induced by the identity on u ∘ F g
  η : {x : C.Obj} (g : x C.⇒₁ U₀) → g C.⇒₂ ⇑₁ (U₁ D.∘₁ F.F₁ g)
  η g = ⇑₂ (D.id₂ {f = U₁ D.∘₁ F.F₁ g})

  field
    -- η is invertible
    η-invertible : {x : C.Obj} (g : x C.⇒₁ U₀) → C.Invertible₂ (η g)

  η⁻¹ : {x : C.Obj} (g : x C.⇒₁ U₀) → ⇑₁ (U₁ D.∘₁ F.F₁ g) C.⇒₂ g
  η⁻¹ g = C.Hom.inv (η-invertible g)

  η-iso : {x : C.Obj} (g : x C.⇒₁ U₀) → g C.≅₂ ⇑₁ (U₁ D.∘₁ F.F₁ g)
  η-iso g = C.≅₂-invertible (η-invertible g)

  ----------------------------------------------------------------------
  -- Consequences of the universal property
  ----------------------------------------------------------------------

  -- every 2-cell into f̄ is the factorization of its own image
  ⇑₂-β' : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
          (β : g C.⇒₂ ⇑₁ f) → β C.≈ ⇑₂ (ε⇒ f D.• (U₁ D.◁ F.F₂ β))
  ⇑₂-β' β = ⇑₂-unique β D.≈-refl

  -- the factorization is compatible with equality of 2-cells
  ⇑₂-cong : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
            {α β : (U₁ D.∘₁ F.F₁ g) D.⇒₂ f} →
            α D.≈ β → ⇑₂ α C.≈ ⇑₂ β
  ⇑₂-cong {α = α} p = ⇑₂-unique (⇑₂ α) (D.≈-trans (⇑₂-β α) p)

  -- two 2-cells with the same image are equal
  ⇑₂-cancel : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
              {α β : g C.⇒₂ ⇑₁ f} →
              ε⇒ f D.• (U₁ D.◁ F.F₂ α) D.≈ ε⇒ f D.• (U₁ D.◁ F.F₂ β) → α C.≈ β
  ⇑₂-cancel {α = α} {β = β} p =
    C.≈-trans (⇑₂-unique α p) (C.≈-sym (⇑₂-β' β))
