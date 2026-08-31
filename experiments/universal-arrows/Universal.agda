------------------------------------------------------------------------
-- Universal arrows for bicategories.
--
-- First formulation: a biuniversal arrow from a bifunctor F to an
-- object y is an object ȳ together with a 1-cell u : F ȳ → y through
-- which every 1-cell f : F x → y factors, up to an invertible 2-cell,
-- in an essentially unique way (see universal1.tex).
--
-- Second formulation: the same notion, presented algebraically in the
-- "half-adjoint" style. The lifting of 2-cells is given as data, with
-- no uniqueness clause, and so is the unit η; the two are tied
-- together by a single triangle identity, η and ε being invertible
-- (see universal2.tex).
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
record Universal
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
    ε : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → (U₁ D.∘₁ F.F₁ (⇑₁ f)) D.⇒₂ f

    -- ε is invertible
    ε-invertible : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → D.Invertible₂ (ε f)

  ε⁻¹ : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → f D.⇒₂ (U₁ D.∘₁ F.F₁ (⇑₁ f))
  ε⁻¹ f = D.Hom.inv (ε-invertible f)

  ε-iso : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → (U₁ D.∘₁ F.F₁ (⇑₁ f)) D.≅₂ f
  ε-iso f = D.≅₂-invertible (ε-invertible f)

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
           ε f D.• (U₁ D.◁ F.F₂ (⇑₂ α)) D.≈ α

    -- …and α' is the only such 2-cell
    ⇑₂-unique : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
                {α : (U₁ D.∘₁ F.F₁ g) D.⇒₂ f} (β : g C.⇒₂ ⇑₁ f) →
                ε f D.• (U₁ D.◁ F.F₂ β) D.≈ α → β C.≈ ⇑₂ α

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
          (β : g C.⇒₂ ⇑₁ f) → β C.≈ ⇑₂ (ε f D.• (U₁ D.◁ F.F₂ β))
  ⇑₂-β' β = ⇑₂-unique β D.≈-refl

  -- the factorization is compatible with equality of 2-cells
  ⇑₂-cong : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
            {α β : (U₁ D.∘₁ F.F₁ g) D.⇒₂ f} →
            α D.≈ β → ⇑₂ α C.≈ ⇑₂ β
  ⇑₂-cong {α = α} p = ⇑₂-unique (⇑₂ α) (D.≈-trans (⇑₂-β α) p)

  -- two 2-cells with the same image are equal
  ⇑₂-cancel : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ U₀}
              {α β : g C.⇒₂ ⇑₁ f} →
              ε f D.• (U₁ D.◁ F.F₂ α) D.≈ ε f D.• (U₁ D.◁ F.F₂ β) → α C.≈ β
  ⇑₂-cancel {α = α} {β = β} p =
    C.≈-trans (⇑₂-unique α p) (C.≈-sym (⇑₂-β' β))

------------------------------------------------------------------------
-- A biuniversal arrow, half-adjoint style
------------------------------------------------------------------------

record UniversalHA
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
  -- Factorization of 1-cells: the counit
  ----------------------------------------------------------------------

  field
    -- every 1-cell f : F x ⇒ y induces a 1-cell f̄ : x ⇒ ȳ…
    ⇑₁ : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → x C.⇒₁ U₀

    -- …through which it factors, up to an invertible 2-cell
    --
    --   F x ---- F f̄ ----> F ȳ
    --    ‖         ε f ⇓    | u
    --   F x ------- f ----> y
    ε : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → (U₁ D.∘₁ F.F₁ (⇑₁ f)) D.⇒₂ f

    -- ε is invertible
    ε-invertible : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → D.Invertible₂ (ε f)

  ε⁻¹ : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → f D.⇒₂ (U₁ D.∘₁ F.F₁ (⇑₁ f))
  ε⁻¹ f = D.Hom.inv (ε-invertible f)

  ε-iso : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → (U₁ D.∘₁ F.F₁ (⇑₁ f)) D.≅₂ f
  ε-iso f = D.≅₂-invertible (ε-invertible f)

  ----------------------------------------------------------------------
  -- The unit
  ----------------------------------------------------------------------

  field
    -- every 1-cell f : x ⇒ ȳ is, up to an invertible 2-cell, the
    -- factorization of its own image u ∘ F f
    η : {x : C.Obj} (f : x C.⇒₁ U₀) → f C.⇒₂ ⇑₁ (U₁ D.∘₁ F.F₁ f)

    -- η is invertible
    η-invertible : {x : C.Obj} (f : x C.⇒₁ U₀) → C.Invertible₂ (η f)

    -- the triangle identity: whiskering η f by u and factoring the
    -- result through ε gives back the identity, i.e. the composite
    --
    --   u ∘ F f ⇒ u ∘ F (u ∘ F f) ⇒ u ∘ F f
    --
    -- (the first map being u ◁ F (η f), the second ε (u ∘ F f)) is id
    η-triangle : {x : C.Obj} (f : x C.⇒₁ U₀) →
                 ε (U₁ D.∘₁ F.F₁ f) D.• (U₁ D.◁ F.F₂ (η f))
                 D.≈ D.id₂ {f = U₁ D.∘₁ F.F₁ f}

  η⁻¹ : {x : C.Obj} (f : x C.⇒₁ U₀) → ⇑₁ (U₁ D.∘₁ F.F₁ f) C.⇒₂ f
  η⁻¹ f = C.Hom.inv (η-invertible f)

  η-iso : {x : C.Obj} (f : x C.⇒₁ U₀) → f C.≅₂ ⇑₁ (U₁ D.∘₁ F.F₁ f)
  η-iso f = C.≅₂-invertible (η-invertible f)

  ----------------------------------------------------------------------
  -- Factorization of 2-cells
  ----------------------------------------------------------------------

  field
    -- every 2-cell α : f ⇒ g between 1-cells F x ⇒ y induces a 2-cell
    -- ᾱ : f̄ ⇒ ḡ between their factorizations…
    ⇑₂ : {x : C.Obj} {f g : F.F₀ x D.⇒₁ y} → f D.⇒₂ g → ⇑₁ f C.⇒₂ ⇑₁ g

    -- …compatibly with equality of 2-cells (in the setoid approach
    -- this is a genuine extra condition, just as for F-cong: it does
    -- not follow from the axioms below, since cancelling ε in
    -- ε-natural only gives u ◁ F ᾱ ≈ u ◁ F β̄, and coming back from
    -- there through η-natural needs ⇑₂-cong itself)
    ⇑₂-cong : {x : C.Obj} {f g : F.F₀ x D.⇒₁ y} {α β : f D.⇒₂ g} →
              α D.≈ β → ⇑₂ α C.≈ ⇑₂ β

    -- ε is natural: factoring f and then applying α is the same as
    -- applying ᾱ and then factoring g
    ε-natural : {x : C.Obj} {f g : F.F₀ x D.⇒₁ y} (α : f D.⇒₂ g) →
                α D.• ε f D.≈ ε g D.• (U₁ D.◁ F.F₂ (⇑₂ α))

    -- η is natural: for α : f ⇒ g between 1-cells x ⇒ ȳ, the unit
    -- takes α to the factorization of its whiskering by u
    η-natural : {x : C.Obj} {f g : x C.⇒₁ U₀} (α : f C.⇒₂ g) →
                ⇑₂ (U₁ D.◁ F.F₂ α) C.• η f C.≈ η g C.• α

  ----------------------------------------------------------------------
  -- Consequences
  ----------------------------------------------------------------------

  -- since ε is invertible, the triangle identity says that the
  -- whiskering of η by u is the inverse of ε
  η-triangle' : {x : C.Obj} (f : x C.⇒₁ U₀) →
                U₁ D.◁ F.F₂ (η f) D.≈ ε⁻¹ (U₁ D.∘₁ F.F₁ f)
  η-triangle' f =
    D.≈-trans (D.≈-sym D.•-identityˡ)
    (D.≈-trans (D.•-congˡ (D.≈-sym (D.≅₂isoˡ (ε-iso (U₁ D.∘₁ F.F₁ f)))))
    (D.≈-trans D.•-assoc
    (D.≈-trans (D.•-congʳ (η-triangle f)) D.•-identityʳ)))

  -- naturality of ε, in the reverse direction
  ε-natural⇐ : {x : C.Obj} {f g : F.F₀ x D.⇒₁ y} (α : f D.⇒₂ g) →
               ε⁻¹ g D.• α D.≈ (U₁ D.◁ F.F₂ (⇑₂ α)) D.• ε⁻¹ f
  ε-natural⇐ {f = f} {g = g} α =
    D.Hom.≅-natural (ε-iso f) (ε-iso g) (U₁ D.◁ F.F₂ (⇑₂ α)) α (ε-natural α)

  -- naturality of η, in the reverse direction
  η-natural⇐ : {x : C.Obj} {f g : x C.⇒₁ U₀} (α : f C.⇒₂ g) →
               η⁻¹ g C.• ⇑₂ (U₁ D.◁ F.F₂ α) C.≈ α C.• η⁻¹ f
  η-natural⇐ {f = f} {g = g} α =
    C.Hom.≅-natural (η-iso f) (η-iso g) α (⇑₂ (U₁ D.◁ F.F₂ α)) (η-natural α)
