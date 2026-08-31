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

------------------------------------------------------------------------
-- Equivalence between the two formulations
--
-- The two records carry the same object ȳ, the same 1-cell u and the
-- same factorization ⇑₁/ε: the translations below copy those fields
-- unchanged, and only have to rebuild the factorization of 2-cells and
-- the unit. Consequently a round trip is definitionally the identity on
-- U₀, U₁, ⇑₁ and ε, and the round-trip lemmas at the end only concern
-- ⇑₂ and η, which agree up to _≈_.
------------------------------------------------------------------------

module _ {C : Bicategory o  ℓ₁  ℓ₂  e }
         {D : Bicategory o' ℓ₁' ℓ₂' e'}
         {F : Bifunctor C D}
         {y : Bicategory.Obj D}
         where

  private module C = Bicategory C
  private module D = Bicategory D
  private module F = Bifunctor F

  ----------------------------------------------------------------------
  -- From the universal property to the algebraic formulation
  ----------------------------------------------------------------------

  Universal→UniversalHA : Universal F y → UniversalHA F y
  Universal→UniversalHA U = record
    { U₀           = U.U₀
    ; U₁           = U.U₁
    ; ⇑₁           = U.⇑₁
    ; ε            = U.ε
    ; ε-invertible = U.ε-invertible
    ; η            = U.η
    ; η-invertible = U.η-invertible
      -- η f is U.⇑₂ id₂, so the triangle is ⇑₂-β at the identity
    ; η-triangle   = λ f → U.⇑₂-β D.id₂
      -- α : f ⇒₂ g is factored by first composing with ε f, which
      -- brings it into the shape u ∘₁ F (⇑₁ f) ⇒₂ g expected by U.⇑₂
    ; ⇑₂           = λ {x} {f} α → U.⇑₂ (α D.• U.ε f)
    ; ⇑₂-cong      = λ p → U.⇑₂-cong (D.•-congˡ p)
    ; ε-natural    = λ {x} {f} α → D.≈-sym (U.⇑₂-β (α D.• U.ε f))
    ; η-natural    = η-natural'
    }
    where
      module U = Universal U

      -- both sides become u ◁ F α once whiskered by u and factored
      -- through ε, so ⇑₂-cancel applies
      η-natural' : {x : C.Obj} {f g : x C.⇒₁ U.U₀} (α : f C.⇒₂ g) →
                   U.⇑₂ ((U.U₁ D.◁ F.F₂ α) D.• U.ε (U.U₁ D.∘₁ F.F₁ f)) C.• U.η f
                   C.≈ U.η g C.• α
      η-natural' {f = f} {g = g} α = U.⇑₂-cancel (D.≈-trans left (D.≈-sym right))
        where
          open D.⇒₂-Reasoning

          w : {p q : _ C.⇒₁ U.U₀} → p C.⇒₂ q → _
          w β = U.U₁ D.◁ F.F₂ β

          -- u ◁ F (β • γ) splits into two whiskerings
          split : {p q r : _ C.⇒₁ U.U₀} (β : q C.⇒₂ r) (γ : p C.⇒₂ q) →
                  w (β C.• γ) D.≈ w β D.• w γ
          split β γ = D.≈-trans (D.◁-cong U.U₁ (F.F₂-• β γ))
                                (D.◁-• U.U₁ (F.F₂ β) (F.F₂ γ))

          left : U.ε (U.U₁ D.∘₁ F.F₁ g) D.•
                 w (U.⇑₂ ((U.U₁ D.◁ F.F₂ α) D.• U.ε (U.U₁ D.∘₁ F.F₁ f)) C.• U.η f)
                 D.≈ (U.U₁ D.◁ F.F₂ α)
          left = begin
            U.ε (U.U₁ D.∘₁ F.F₁ g) D.•
              w (U.⇑₂ ((U.U₁ D.◁ F.F₂ α) D.• U.ε (U.U₁ D.∘₁ F.F₁ f)) C.• U.η f)
              ≈⟨ D.•-congʳ (split _ (U.η f)) ⟩
            U.ε (U.U₁ D.∘₁ F.F₁ g) D.•
              (w (U.⇑₂ ((U.U₁ D.◁ F.F₂ α) D.• U.ε (U.U₁ D.∘₁ F.F₁ f))) D.• w (U.η f))
              ≈⟨ D.≈-sym D.•-assoc ⟩
            (U.ε (U.U₁ D.∘₁ F.F₁ g) D.•
              w (U.⇑₂ ((U.U₁ D.◁ F.F₂ α) D.• U.ε (U.U₁ D.∘₁ F.F₁ f)))) D.• w (U.η f)
              ≈⟨ D.•-congˡ (U.⇑₂-β _) ⟩
            ((U.U₁ D.◁ F.F₂ α) D.• U.ε (U.U₁ D.∘₁ F.F₁ f)) D.• w (U.η f)
              ≈⟨ D.•-assoc ⟩
            (U.U₁ D.◁ F.F₂ α) D.• (U.ε (U.U₁ D.∘₁ F.F₁ f) D.• w (U.η f))
              ≈⟨ D.•-congʳ (U.⇑₂-β D.id₂) ⟩
            (U.U₁ D.◁ F.F₂ α) D.• D.id₂
              ≈⟨ D.•-identityʳ ⟩
            (U.U₁ D.◁ F.F₂ α) ∎

          right : U.ε (U.U₁ D.∘₁ F.F₁ g) D.• w (U.η g C.• α)
                  D.≈ (U.U₁ D.◁ F.F₂ α)
          right = begin
            U.ε (U.U₁ D.∘₁ F.F₁ g) D.• w (U.η g C.• α)
              ≈⟨ D.•-congʳ (split (U.η g) α) ⟩
            U.ε (U.U₁ D.∘₁ F.F₁ g) D.• (w (U.η g) D.• w α)
              ≈⟨ D.≈-sym D.•-assoc ⟩
            (U.ε (U.U₁ D.∘₁ F.F₁ g) D.• w (U.η g)) D.• w α
              ≈⟨ D.•-congˡ (U.⇑₂-β D.id₂) ⟩
            D.id₂ D.• w α
              ≈⟨ D.•-identityˡ ⟩
            (U.U₁ D.◁ F.F₂ α) ∎

  ----------------------------------------------------------------------
  -- From the algebraic formulation to the universal property
  ----------------------------------------------------------------------

  module _ (H : UniversalHA F y) where

    private module H = UniversalHA H

    -- The key lemma: on 2-cells between 1-cells x ⇒₁ ȳ, whiskering by u
    -- and applying F is faithful. This is what replaces the uniqueness
    -- clause of the first formulation, and it is where ⇑₂-cong and the
    -- invertibility of η are used.
    ◁-faithful : {x : C.Obj} {p q : x C.⇒₁ H.U₀} {γ δ : p C.⇒₂ q} →
                 (H.U₁ D.◁ F.F₂ γ) D.≈ (H.U₁ D.◁ F.F₂ δ) → γ C.≈ δ
    ◁-faithful {q = q} {γ = γ} {δ = δ} p =
      C.Hom.∘-cancelˡ (H.η-invertible q)
        (C.≈-trans (C.≈-sym (H.η-natural γ))
        (C.≈-trans (C.•-congˡ (H.⇑₂-cong p)) (H.η-natural δ)))

    -- the factorization of an identity is an identity
    ⇑₂-id : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → H.⇑₂ (D.id₂ {f = f}) C.≈ C.id₂
    ⇑₂-id f = ◁-faithful (D.Hom.∘-cancelˡ (H.ε-invertible f)
                (D.≈-trans (D.≈-trans (D.≈-sym (H.ε-natural D.id₂)) D.•-identityˡ)
                           (D.≈-sym (D.≈-trans (D.•-congʳ
                             (D.≈-trans (D.◁-cong H.U₁ F.F₂-id₂)
                                        (D.◁-id H.U₁ (F.F₁ (H.⇑₁ f)))))
                             D.•-identityʳ))))

    ----------------------------------------------------------------------
    -- The data of the universal property
    ----------------------------------------------------------------------

    private

      -- a 2-cell α : u ∘₁ F g ⇒₂ f is factored by applying H.⇑₂ and
      -- then correcting the source with the unit
      ⇑₂' : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ H.U₀} →
            (H.U₁ D.∘₁ F.F₁ g) D.⇒₂ f → g C.⇒₂ H.⇑₁ f
      ⇑₂' {g = g} α = H.⇑₂ α C.• H.η g

      ⇑₂'-β : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ H.U₀}
              (α : (H.U₁ D.∘₁ F.F₁ g) D.⇒₂ f) →
              H.ε f D.• (H.U₁ D.◁ F.F₂ (⇑₂' α)) D.≈ α
      ⇑₂'-β {f = f} {g = g} α = begin
        H.ε f D.• (H.U₁ D.◁ F.F₂ (H.⇑₂ α C.• H.η g))
          ≈⟨ D.•-congʳ (D.≈-trans (D.◁-cong H.U₁ (F.F₂-• (H.⇑₂ α) (H.η g)))
                                  (D.◁-• H.U₁ (F.F₂ (H.⇑₂ α)) (F.F₂ (H.η g)))) ⟩
        H.ε f D.• ((H.U₁ D.◁ F.F₂ (H.⇑₂ α)) D.• (H.U₁ D.◁ F.F₂ (H.η g)))
          ≈⟨ D.≈-sym D.•-assoc ⟩
        (H.ε f D.• (H.U₁ D.◁ F.F₂ (H.⇑₂ α))) D.• (H.U₁ D.◁ F.F₂ (H.η g))
          ≈⟨ D.•-congˡ (D.≈-sym (H.ε-natural α)) ⟩
        (α D.• H.ε (H.U₁ D.∘₁ F.F₁ g)) D.• (H.U₁ D.◁ F.F₂ (H.η g))
          ≈⟨ D.•-assoc ⟩
        α D.• (H.ε (H.U₁ D.∘₁ F.F₁ g) D.• (H.U₁ D.◁ F.F₂ (H.η g)))
          ≈⟨ D.•-congʳ (H.η-triangle g) ⟩
        α D.• D.id₂
          ≈⟨ D.•-identityʳ ⟩
        α ∎
        where open D.⇒₂-Reasoning

      ⇑₂'-unique : {x : C.Obj} {f : F.F₀ x D.⇒₁ y} {g : x C.⇒₁ H.U₀}
                   {α : (H.U₁ D.∘₁ F.F₁ g) D.⇒₂ f} (β : g C.⇒₂ H.⇑₁ f) →
                   H.ε f D.• (H.U₁ D.◁ F.F₂ β) D.≈ α → β C.≈ ⇑₂' α
      ⇑₂'-unique {α = α} β p =
        ◁-faithful (D.Hom.∘-cancelˡ (H.ε-invertible _)
                     (D.≈-trans p (D.≈-sym (⇑₂'-β α))))

      -- the unit of the universal property, ⇑₂' id₂, is H.η up to the
      -- identity factorization, hence invertible
      η'-invertible : {x : C.Obj} (g : x C.⇒₁ H.U₀) →
                      C.Invertible₂ (⇑₂' (D.id₂ {f = H.U₁ D.∘₁ F.F₁ g}))
      η'-invertible g = C.Hom.mkInv (H.η⁻¹ g)
        (C.≈-trans (C.•-congʳ (C.≈-trans (C.•-congˡ (⇑₂-id _)) C.•-identityˡ))
                   (C.Hom.invˡ (H.η-invertible g)))
        (C.≈-trans (C.•-congˡ (C.≈-trans (C.•-congˡ (⇑₂-id _)) C.•-identityˡ))
                   (C.Hom.invʳ (H.η-invertible g)))

    UniversalHA→Universal : Universal F y
    UniversalHA→Universal = record
      { U₀           = H.U₀
      ; U₁           = H.U₁
      ; ⇑₁           = H.⇑₁
      ; ε            = H.ε
      ; ε-invertible = H.ε-invertible
      ; ⇑₂           = ⇑₂'
      ; ⇑₂-β         = ⇑₂'-β
      ; ⇑₂-unique    = ⇑₂'-unique
      ; η-invertible = η'-invertible
      }

  ----------------------------------------------------------------------
  -- The two translations are mutually inverse
  --
  -- A round trip leaves U₀, U₁, ⇑₁ and ε unchanged on the nose (both
  -- translations copy those fields), so only ⇑₂ and η are worth
  -- stating: they are recovered up to _≈_.
  ----------------------------------------------------------------------

  -- starting from the universal property
  Universal-roundtrip-⇑₂ :
    (U : Universal F y) {x : C.Obj} {f : F.F₀ x D.⇒₁ y}
    {g : x C.⇒₁ Universal.U₀ U} (α : (Universal.U₁ U D.∘₁ F.F₁ g) D.⇒₂ f) →
    Universal.⇑₂ (UniversalHA→Universal (Universal→UniversalHA U)) α
    C.≈ Universal.⇑₂ U α
  Universal-roundtrip-⇑₂ U α =
    Universal.⇑₂-unique U _
      (Universal.⇑₂-β (UniversalHA→Universal (Universal→UniversalHA U)) α)

  -- η is ⇑₂ at the identity on both sides, so this is a special case
  Universal-roundtrip-η :
    (U : Universal F y) {x : C.Obj} (g : x C.⇒₁ Universal.U₀ U) →
    Universal.η (UniversalHA→Universal (Universal→UniversalHA U)) g
    C.≈ Universal.η U g
  Universal-roundtrip-η U g = Universal-roundtrip-⇑₂ U D.id₂

  -- starting from the algebraic formulation
  UniversalHA-roundtrip-η :
    (H : UniversalHA F y) {x : C.Obj} (g : x C.⇒₁ UniversalHA.U₀ H) →
    UniversalHA.η (Universal→UniversalHA (UniversalHA→Universal H)) g
    C.≈ UniversalHA.η H g
  UniversalHA-roundtrip-η H g =
    C.≈-trans (C.•-congˡ (⇑₂-id H _)) C.•-identityˡ

  UniversalHA-roundtrip-⇑₂ :
    (H : UniversalHA F y) {x : C.Obj} {f g : F.F₀ x D.⇒₁ y} (α : f D.⇒₂ g) →
    UniversalHA.⇑₂ (Universal→UniversalHA (UniversalHA→Universal H)) α
    C.≈ UniversalHA.⇑₂ H α
  UniversalHA-roundtrip-⇑₂ H {f = f} {g = g} α =
    ◁-faithful H (D.Hom.∘-cancelˡ (UniversalHA.ε-invertible H g)
      (D.≈-trans (Universal.⇑₂-β (UniversalHA→Universal H)
                    (α D.• UniversalHA.ε H f))
                 (UniversalHA.ε-natural H α)))
