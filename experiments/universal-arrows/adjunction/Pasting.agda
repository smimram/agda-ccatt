------------------------------------------------------------------------
-- Pasting of squares in a bicategory.
--
-- A "square" is a 2-cell u₂ ∘ p ⇒ q ∘ u₁, thought of as filling
--
--          p
--     ∙ -------> ∙
--     |          |
--  u₁ |    σ     | u₂        (read as u₂ ∘ p ⇒ q ∘ u₁)
--     v          v
--     ∙ -------> ∙
--          q
--
-- Two such squares paste side by side. The pasting is associative up
-- to the associators of the two rows, which is paste-assoc.
------------------------------------------------------------------------

-- Usage: the contents are parametrized by a bicategory, so importers
-- should write
--
--   import adjunction.Pasting as Past
--   open Past using (module Pasting)
--
-- and then, for a bicategory D, "private module D-P = Pasting D".

module adjunction.Pasting where

open import Level using (Level)

import Bicategory as Bicat
open Bicat using (Bicategory)

module Pasting {o ℓ₁ ℓ₂ e : Level} (B : Bicategory o ℓ₁ ℓ₂ e) where

  open Bicategory B

  paste : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
          (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
          (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) →
          (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁) → (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀) →
          (u₂ ∘₁ (p₂ ∘₁ p₁)) ⇒₂ ((q₂ ∘₁ q₁) ∘₁ u₀)
  paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ =
    assoc⇐ q₂ q₁ u₀ •
      ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)))

  paste-cong : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
               (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
               (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
               {σ' σ'' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)}
               {σ σ''' : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀)} →
               σ' ≈ σ'' → σ ≈ σ''' →
               paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ
               ≈ paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ'' σ'''
  paste-cong u₀ u₁ u₂ p₁ p₂ q₁ q₂ p p' =
    •-congʳ (•-cong (◁-cong q₂ p') (•-congʳ (•-congˡ (▷-cong p₁ p))))

  paste-assoc :
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Obj}
    (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂) (u₃ : a₃ ⇒₁ b₃)
    (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (p₃ : a₂ ⇒₁ a₃)
    (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) (q₃ : b₂ ⇒₁ b₃)
    (σ₃ : (u₃ ∘₁ p₃) ⇒₂ (q₃ ∘₁ u₂)) (σ₂ : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁))
    (σ₁ : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀)) →
    (assoc⇒ q₃ q₂ q₁ ▷ u₀) •
      paste u₀ u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) σ₁
    ≈ paste u₀ u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
        (paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁)
        • (u₃ ◁ assoc⇒ p₃ p₂ p₁)
  paste-assoc u₀ u₁ u₂ u₃ p₁ p₂ p₃ q₁ q₂ q₃ σ₃ σ₂ σ₁ = begin
    (assoc⇒ q₃ q₂ q₁ ▷ u₀) •
      paste u₀ u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) σ₁
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ expandL))) ⟩
    L10 • (L9 • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))) 
      ≈⟨ ≈-sym •-assoc ⟩
    (L10 • L9) • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congˡ step1 ⟩
    (R10 • (R9 • A₁)) • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-assoc ⟩
    R10 • ((R9 • A₁) • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ •-assoc ⟩
    R10 • (R9 • (A₁ • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    R10 • (R9 • ((A₁ • L8) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ step2)) ⟩
    R10 • (R9 • ((R8 • A₂) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    R10 • (R9 • (R8 • (A₂ • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))))) 
      ≈⟨ •-congʳ (•-congʳ (•-congʳ
           (≈-trans (•-congʳ (≈-sym •-assoc)) (≈-sym •-assoc)))) ⟩
    R10 • (R9 • (R8 • ((A₂ • (L7 • L6)) • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ step3))) ⟩
    R10 • (R9 • (R8 • ((R7 • A₃) • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    R10 • (R9 • (R8 • (R7 • (A₃ • (L5 • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc)))) ⟩
    R10 • (R9 • (R8 • (R7 • ((A₃ • L5) • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congˡ step4)))) ⟩
    R10 • (R9 • (R8 • (R7 • ((R6 • A₄) • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ •-assoc))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (A₄ • (L4 • (L3 • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • ((A₄ • L4) • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congˡ step5))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • ((R5 • (R4 • A₅)) • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (≈-trans •-assoc (•-congʳ •-assoc)))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (A₅ • (L3 • (L2 • L1)))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (≈-sym •-assoc))))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • ((A₅ • L3) • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (•-congˡ step6))))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • ((R3 • A₆) • (L2 • L1))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           •-assoc)))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (A₆ • (L2 • L1)))))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ
           (•-congʳ step7))))))) ⟩
    R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))))
      ≈⟨ ≈-sym expandR ⟩
    paste u₀ u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
      (paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁)
      • (u₃ ◁ assoc⇒ p₃ p₂ p₁) ∎
    where
      open ⇒₂-Reasoning

      L1  = assoc⇐ u₃ (p₃ ∘₁ p₂) p₁
      L2  = assoc⇐ u₃ p₃ p₂ ▷ p₁
      L3  = (σ₃ ▷ p₂) ▷ p₁
      L4  = assoc⇒ q₃ u₂ p₂ ▷ p₁
      L5  = (q₃ ◁ σ₂) ▷ p₁
      L6  = assoc⇐ q₃ q₂ u₁ ▷ p₁
      L7  = assoc⇒ (q₃ ∘₁ q₂) u₁ p₁
      L8  = (q₃ ∘₁ q₂) ◁ σ₁
      L9  = assoc⇐ (q₃ ∘₁ q₂) q₁ u₀
      L10 = assoc⇒ q₃ q₂ q₁ ▷ u₀

      R1  = u₃ ◁ assoc⇒ p₃ p₂ p₁
      R2  = assoc⇐ u₃ p₃ (p₂ ∘₁ p₁)
      R3  = σ₃ ▷ (p₂ ∘₁ p₁)
      R4  = assoc⇒ q₃ u₂ (p₂ ∘₁ p₁)
      R5  = q₃ ◁ assoc⇐ u₂ p₂ p₁
      R6  = q₃ ◁ (σ₂ ▷ p₁)
      R7  = q₃ ◁ assoc⇒ q₂ u₁ p₁
      R8  = q₃ ◁ (q₂ ◁ σ₁)
      R9  = q₃ ◁ assoc⇐ q₂ q₁ u₀
      R10 = assoc⇐ q₃ (q₂ ∘₁ q₁) u₀

      A₁ = assoc⇒ q₃ q₂ (q₁ ∘₁ u₀)
      A₂ = assoc⇒ q₃ q₂ (u₁ ∘₁ p₁)
      A₃ = assoc⇒ q₃ (q₂ ∘₁ u₁) p₁
      A₄ = assoc⇒ q₃ (u₂ ∘₁ p₂) p₁
      A₅ = assoc⇒ (q₃ ∘₁ u₂) p₂ p₁
      A₆ = assoc⇒ (u₃ ∘₁ p₃) p₂ p₁

      -- the two pastings, flattened
      expandL : (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁) • L1
                ≈ L6 • (L5 • (L4 • (L3 • (L2 • L1))))
      expandL = ≈-trans (•-congˡ expand▷)
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc))))))
        where
          expand▷ : paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁
                    ≈ L6 • (L5 • (L4 • (L3 • L2)))
          expand▷ =
            ≈-trans (▷-• (assoc⇐ q₃ q₂ u₁)
                         ((q₃ ◁ σ₂) • (assoc⇒ q₃ u₂ p₂
                           • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂))) p₁)
            (•-congʳ (≈-trans (▷-• (q₃ ◁ σ₂)
                         (assoc⇒ q₃ u₂ p₂ • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂)) p₁)
            (•-congʳ (≈-trans (▷-• (assoc⇒ q₃ u₂ p₂)
                         ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂) p₁)
            (•-congʳ (▷-• (σ₃ ▷ p₂) (assoc⇐ u₃ p₃ p₂) p₁))))))

      expandR : paste u₀ u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
                  (paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁)
                  • (u₃ ◁ assoc⇒ p₃ p₂ p₁)
                ≈ R10 • (R9 • (R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))))
      expandR = ≈-trans (•-congˡ (•-congʳ (•-congˡ expand◁)))
                (≈-trans (•-congˡ (•-congʳ
                  (≈-trans •-assoc (•-congʳ
                  (≈-trans •-assoc (•-congʳ
                  (≈-trans •-assoc (•-congʳ •-assoc))))))))
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc)))))))))))))))
        where
          expand◁ : q₃ ◁ paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ₂ σ₁
                    ≈ R9 • (R8 • (R7 • (R6 • R5)))
          expand◁ =
            ≈-trans (◁-• q₃ (assoc⇐ q₂ q₁ u₀)
                         ((q₂ ◁ σ₁) • (assoc⇒ q₂ u₁ p₁
                           • ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁))))
            (•-congʳ (≈-trans (◁-• q₃ (q₂ ◁ σ₁)
                         (assoc⇒ q₂ u₁ p₁ • ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁)))
            (•-congʳ (≈-trans (◁-• q₃ (assoc⇒ q₂ u₁ p₁)
                         ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁))
            (•-congʳ (◁-• q₃ (σ₂ ▷ p₁) (assoc⇐ u₂ p₂ p₁)))))))

      -- the pentagon at (q₃,q₂,q₁,u₀), with two associators inverted
      step1 : L10 • L9 ≈ R10 • (R9 • A₁)
      step1 = Hom.∘-cancelˡ
        (Hom.∘-invertible (invertible-≅₂ (q₃ ◁≅ associator q₂ q₁ u₀))
                          (invertible-≅₂ (associator q₃ (q₂ ∘₁ q₁) u₀)))
        (begin
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • assoc⇒ q₃ (q₂ ∘₁ q₁) u₀) • (L10 • L9)
            ≈⟨ •-assoc ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • (assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • (L10 • L9))
            ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • ((assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • L10) • L9)
            ≈⟨ ≈-sym •-assoc ⟩
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • (assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • L10)) • L9
            ≈⟨ •-congˡ (≈-sym (pentagon q₃ q₂ q₁ u₀)) ⟩
          (A₁ • assoc⇒ (q₃ ∘₁ q₂) q₁ u₀) • L9
            ≈⟨ •-assoc ⟩
          A₁ • (assoc⇒ (q₃ ∘₁ q₂) q₁ u₀ • L9)
            ≈⟨ •-congʳ (≅₂isoʳ (associator (q₃ ∘₁ q₂) q₁ u₀)) ⟩
          A₁ • id₂
            ≈⟨ •-identityʳ ⟩
          A₁
            ≈⟨ ≈-sym •-identityˡ ⟩
          id₂ • A₁
            ≈⟨ •-congˡ (≈-sym (≈-trans (≈-sym (◁-• q₃ (assoc⇒ q₂ q₁ u₀)
                                                     (assoc⇐ q₂ q₁ u₀)))
                              (≈-trans (◁-cong q₃ (≅₂isoʳ (associator q₂ q₁ u₀)))
                                       (◁-id q₃ (q₂ ∘₁ (q₁ ∘₁ u₀)))))) ⟩
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • R9) • A₁
            ≈⟨ •-assoc ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • (R9 • A₁)
            ≈⟨ •-congʳ (≈-sym (≈-trans (•-congˡ (≅₂isoʳ (associator q₃ (q₂ ∘₁ q₁) u₀)))
                                       •-identityˡ)) ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • ((assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • R10) • (R9 • A₁))
            ≈⟨ •-congʳ •-assoc ⟩
          (q₃ ◁ assoc⇒ q₂ q₁ u₀) • (assoc⇒ q₃ (q₂ ∘₁ q₁) u₀ • (R10 • (R9 • A₁)))
            ≈⟨ ≈-sym •-assoc ⟩
          ((q₃ ◁ assoc⇒ q₂ q₁ u₀) • assoc⇒ q₃ (q₂ ∘₁ q₁) u₀) • (R10 • (R9 • A₁)) ∎)

      -- naturality of the associator in the last variable
      step2 : A₁ • L8 ≈ R8 • A₂
      step2 = ≈-sym (≈-trans (assoc-natural (id₂ {f = q₃}) (id₂ {f = q₂}) σ₁)
                             (•-congʳ (∗-cong (∗-id q₃ q₂) ≈-refl)))

      -- the pentagon at (q₃,q₂,u₁,p₁)
      step3 : A₂ • (L7 • L6) ≈ R7 • A₃
      step3 = begin
        A₂ • (L7 • L6)
          ≈⟨ ≈-sym •-assoc ⟩
        (A₂ • L7) • L6
          ≈⟨ •-congˡ (pentagon q₃ q₂ u₁ p₁) ⟩
        (R7 • (A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁))) • L6
          ≈⟨ •-assoc ⟩
        R7 • ((A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁)) • L6)
          ≈⟨ •-congʳ •-assoc ⟩
        R7 • (A₃ • ((assoc⇒ q₃ q₂ u₁ ▷ p₁) • L6))
          ≈⟨ •-congʳ (•-congʳ (≈-trans (≈-sym (▷-• (assoc⇒ q₃ q₂ u₁)
                                                   (assoc⇐ q₃ q₂ u₁) p₁))
                              (≈-trans (▷-cong p₁ (≅₂isoʳ (associator q₃ q₂ u₁)))
                                       (▷-id (q₃ ∘₁ (q₂ ∘₁ u₁)) p₁)))) ⟩
        R7 • (A₃ • id₂)
          ≈⟨ •-congʳ •-identityʳ ⟩
        R7 • A₃ ∎

      -- naturality of the associator in the middle variable
      step4 : A₃ • L5 ≈ R6 • A₄
      step4 = ≈-sym (assoc-natural (id₂ {f = q₃}) σ₂ (id₂ {f = p₁}))

      -- the pentagon at (q₃,u₂,p₂,p₁)
      step5 : A₄ • L4 ≈ R5 • (R4 • A₅)
      step5 = ≈-sym (begin
        R5 • (R4 • A₅)
          ≈⟨ •-congʳ (pentagon q₃ u₂ p₂ p₁) ⟩
        R5 • ((q₃ ◁ assoc⇒ u₂ p₂ p₁) • (A₄ • L4))
          ≈⟨ ≈-sym •-assoc ⟩
        (R5 • (q₃ ◁ assoc⇒ u₂ p₂ p₁)) • (A₄ • L4)
          ≈⟨ •-congˡ (≈-trans (≈-sym (◁-• q₃ (assoc⇐ u₂ p₂ p₁) (assoc⇒ u₂ p₂ p₁)))
                     (≈-trans (◁-cong q₃ (≅₂isoˡ (associator u₂ p₂ p₁)))
                              (◁-id q₃ ((u₂ ∘₁ p₂) ∘₁ p₁)))) ⟩
        id₂ • (A₄ • L4)
          ≈⟨ •-identityˡ ⟩
        A₄ • L4 ∎)

      -- naturality of the associator in the first variable
      step6 : A₅ • L3 ≈ R3 • A₆
      step6 = ≈-sym (≈-trans (•-congˡ (∗-cong ≈-refl (≈-sym (∗-id p₂ p₁))))
                             (assoc-natural σ₃ (id₂ {f = p₂}) (id₂ {f = p₁})))

      -- the pentagon at (u₃,p₃,p₂,p₁)
      step7 : A₆ • (L2 • L1) ≈ R2 • R1
      step7 = Hom.∘-cancelˡ (invertible-≅₂ (associator u₃ p₃ (p₂ ∘₁ p₁))) (begin
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (A₆ • (L2 • L1))
          ≈⟨ ≈-sym •-assoc ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • A₆) • (L2 • L1)
          ≈⟨ •-congˡ (pentagon u₃ p₃ p₂ p₁) ⟩
        (R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁))) • (L2 • L1)
          ≈⟨ •-assoc ⟩
        R1 • ((assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁)) • (L2 • L1))
          ≈⟨ •-congʳ •-assoc ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • ((assoc⇒ u₃ p₃ p₂ ▷ p₁) • (L2 • L1)))
          ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (((assoc⇒ u₃ p₃ p₂ ▷ p₁) • L2) • L1))
          ≈⟨ •-congʳ (•-congʳ (•-congˡ
               (≈-trans (≈-sym (▷-• (assoc⇒ u₃ p₃ p₂) (assoc⇐ u₃ p₃ p₂) p₁))
               (≈-trans (▷-cong p₁ (≅₂isoʳ (associator u₃ p₃ p₂)))
                        (▷-id (u₃ ∘₁ (p₃ ∘₁ p₂)) p₁))))) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (id₂ • L1))
          ≈⟨ •-congʳ (•-congʳ •-identityˡ) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • L1)
          ≈⟨ •-congʳ (≅₂isoʳ (associator u₃ (p₃ ∘₁ p₂) p₁)) ⟩
        R1 • id₂
          ≈⟨ •-identityʳ ⟩
        R1
          ≈⟨ ≈-sym •-identityˡ ⟩
        id₂ • R1
          ≈⟨ •-congˡ (≈-sym (≅₂isoʳ (associator u₃ p₃ (p₂ ∘₁ p₁)))) ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • R2) • R1
          ≈⟨ •-assoc ⟩
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (R2 • R1) ∎)

  -- the pasting is natural in its two squares: a 2-cell of the top row
  -- can be absorbed into the right-hand square…
  paste-▷ : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
            (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
            (p₁ : a₀ ⇒₁ a₁) (p₂ p₂' : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
            (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (σ : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀))
            (τ : p₂' ⇒₂ p₂) →
            paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (τ ▷ p₁))
            ≈ paste u₀ u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ τ)) σ
  paste-▷ u₀ u₁ u₂ p₁ p₂ p₂' q₁ q₂ σ' σ τ = begin
    paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (τ ▷ p₁))
      ≈⟨ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • (((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))) • (u₂ ◁ (τ ▷ p₁)))
      ≈⟨ •-congʳ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)) • (u₂ ◁ (τ ▷ p₁))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁) • (u₂ ◁ (τ ▷ p₁)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (τ ▷ p₁))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ
           (assoc-natural⇐ (id₂ {f = u₂}) τ (id₂ {f = p₁}))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (((u₂ ◁ τ) ▷ p₁) • assoc⇐ u₂ p₂' p₁))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • ((u₂ ◁ τ) ▷ p₁)) • assoc⇐ u₂ p₂' p₁)))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ
           (≈-sym (▷-• σ' (u₂ ◁ τ) p₁))))) ⟩
    paste u₀ u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ τ)) σ ∎
    where open ⇒₂-Reasoning

  -- …and one of the bottom row into the left-hand square
  paste-◁ : {a₀ a₁ a₂ b₀ b₁ b₂ : Obj}
            (u₀ : a₀ ⇒₁ b₀) (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
            (p₁ p₁' : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : b₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
            (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (σ : (u₁ ∘₁ p₁) ⇒₂ (q₁ ∘₁ u₀))
            (τ : p₁' ⇒₂ p₁) →
            paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (p₂ ◁ τ))
            ≈ paste u₀ u₁ u₂ p₁' p₂ q₁ q₂ σ' (σ • (u₁ ◁ τ))
  paste-◁ u₀ u₁ u₂ p₁ p₁' p₂ q₁ q₂ σ' σ τ = begin
    paste u₀ u₁ u₂ p₁ p₂ q₁ q₂ σ' σ • (u₂ ◁ (p₂ ◁ τ))
      ≈⟨ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • (((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))) • (u₂ ◁ (p₂ ◁ τ)))
      ≈⟨ •-congʳ •-assoc ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)) • (u₂ ◁ (p₂ ◁ τ))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁) • (u₂ ◁ (p₂ ◁ τ)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (p₂ ◁ τ))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ
           (≈-trans (assoc-natural⇐ (id₂ {f = u₂}) (id₂ {f = p₂}) τ)
                    (•-congˡ (∗-cong (∗-id u₂ p₂) ≈-refl)))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((σ' ▷ p₁) • (((u₂ ∘₁ p₂) ◁ τ) • assoc⇐ u₂ p₂ p₁'))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((σ' ▷ p₁) • ((u₂ ∘₁ p₂) ◁ τ)) • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ
           (≈-trans (≈-sym (∗-• σ' (id₂ {f = u₂ ∘₁ p₂}) (id₂ {f = p₁}) τ))
           (≈-trans (∗-cong •-identityʳ •-identityˡ)
                    (∗-decomposeʳ σ' τ)))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • ((((q₂ ∘₁ u₁) ◁ τ) • (σ' ▷ p₁')) • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (assoc⇒ q₂ u₁ p₁
      • (((q₂ ∘₁ u₁) ◁ τ) • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((assoc⇒ q₂ u₁ p₁ • ((q₂ ∘₁ u₁) ◁ τ))
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ
           (≈-trans (•-congʳ (∗-cong (≈-sym (∗-id q₂ u₁)) ≈-refl))
                    (≈-sym (assoc-natural (id₂ {f = q₂}) (id₂ {f = u₁}) τ))))) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • (((q₂ ◁ (u₁ ◁ τ)) • assoc⇒ q₂ u₁ p₁')
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • ((q₂ ◁ σ) • ((q₂ ◁ (u₁ ◁ τ)) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))))
      ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
    assoc⇐ q₂ q₁ u₀ • (((q₂ ◁ σ) • (q₂ ◁ (u₁ ◁ τ))) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congˡ (≈-sym (◁-• q₂ σ (u₁ ◁ τ)))) ⟩
    paste u₀ u₁ u₂ p₁' p₂ q₁ q₂ σ' (σ • (u₁ ◁ τ)) ∎
    where open ⇒₂-Reasoning

  -- The same pasting where the last square has no bottom-left leg: its
  -- 2-cell is u₁ ∘ p₁ ⇒ q₁ instead of u₁ ∘ p₁ ⇒ q₁ ∘ u₀. This is the
  -- shape a universal arrow produces, ε being a square of that kind.
  fpaste : {a₀ a₁ a₂ b₁ b₂ : Obj}
           (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
           (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) →
           (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁) → (u₁ ∘₁ p₁) ⇒₂ q₁ →
           (u₂ ∘₁ (p₂ ∘₁ p₁)) ⇒₂ (q₂ ∘₁ q₁)
  fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ =
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))

  fpaste-cong : {a₀ a₁ a₂ b₁ b₂ : Obj}
                (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
                (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
                {σ' σ'' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)}
                {τ τ' : (u₁ ∘₁ p₁) ⇒₂ q₁} →
                σ' ≈ σ'' → τ ≈ τ' →
                fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ ≈ fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ'' τ'
  fpaste-cong u₁ u₂ p₁ p₂ q₁ q₂ p p' =
    •-cong (◁-cong q₂ p') (•-congʳ (•-congˡ (▷-cong p₁ p)))

  fpaste-▷ : {a₀ a₁ a₂ b₁ b₂ : Obj}
             (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
             (p₁ : a₀ ⇒₁ a₁) (p₂ p₂' : a₁ ⇒₁ a₂)
             (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
             (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (τ : (u₁ ∘₁ p₁) ⇒₂ q₁)
             (κ : p₂' ⇒₂ p₂) →
             fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (κ ▷ p₁))
             ≈ fpaste u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ κ)) τ
  fpaste-▷ u₁ u₂ p₁ p₂ p₂' q₁ q₂ σ' τ κ = begin
    fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (κ ▷ p₁))
      ≈⟨ •-assoc ⟩
    (q₂ ◁ τ) • ((assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))
      • (u₂ ◁ (κ ▷ p₁)))
      ≈⟨ •-congʳ •-assoc ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)
      • (u₂ ◁ (κ ▷ p₁))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (κ ▷ p₁)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ
           (assoc-natural⇐ (id₂ {f = u₂}) κ (id₂ {f = p₁})))) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (((u₂ ◁ κ) ▷ p₁) • assoc⇐ u₂ p₂' p₁)))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • ((u₂ ◁ κ) ▷ p₁))
      • assoc⇐ u₂ p₂' p₁))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ (≈-sym (▷-• σ' (u₂ ◁ κ) p₁)))) ⟩
    fpaste u₁ u₂ p₁ p₂' q₁ q₂ (σ' • (u₂ ◁ κ)) τ ∎
    where open ⇒₂-Reasoning

  fpaste-◁ : {a₀ a₁ a₂ b₁ b₂ : Obj}
             (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂)
             (p₁ p₁' : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂)
             (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂)
             (σ' : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁)) (τ : (u₁ ∘₁ p₁) ⇒₂ q₁)
             (κ : p₁' ⇒₂ p₁) →
             fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (p₂ ◁ κ))
             ≈ fpaste u₁ u₂ p₁' p₂ q₁ q₂ σ' (τ • (u₁ ◁ κ))
  fpaste-◁ u₁ u₂ p₁ p₁' p₂ q₁ q₂ σ' τ κ = begin
    fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ' τ • (u₂ ◁ (p₂ ◁ κ))
      ≈⟨ •-assoc ⟩
    (q₂ ◁ τ) • ((assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁))
      • (u₂ ◁ (p₂ ◁ κ)))
      ≈⟨ •-congʳ •-assoc ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • assoc⇐ u₂ p₂ p₁)
      • (u₂ ◁ (p₂ ◁ κ))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (assoc⇐ u₂ p₂ p₁ • (u₂ ◁ (p₂ ◁ κ)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ
           (≈-trans (assoc-natural⇐ (id₂ {f = u₂}) (id₂ {f = p₂}) κ)
                    (•-congˡ (∗-cong (∗-id u₂ p₂) ≈-refl))))) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((σ' ▷ p₁)
      • (((u₂ ∘₁ p₂) ◁ κ) • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((σ' ▷ p₁) • ((u₂ ∘₁ p₂) ◁ κ))
      • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ
           (≈-trans (≈-sym (∗-• σ' (id₂ {f = u₂ ∘₁ p₂}) (id₂ {f = p₁}) κ))
           (≈-trans (∗-cong •-identityʳ •-identityˡ)
                    (∗-decomposeʳ σ' κ))))) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • ((((q₂ ∘₁ u₁) ◁ κ) • (σ' ▷ p₁'))
      • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    (q₂ ◁ τ) • (assoc⇒ q₂ u₁ p₁ • (((q₂ ∘₁ u₁) ◁ κ)
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ •-congʳ (≈-sym •-assoc) ⟩
    (q₂ ◁ τ) • ((assoc⇒ q₂ u₁ p₁ • ((q₂ ∘₁ u₁) ◁ κ))
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ (•-congˡ
           (≈-trans (•-congʳ (∗-cong (≈-sym (∗-id q₂ u₁)) ≈-refl))
                    (≈-sym (assoc-natural (id₂ {f = q₂}) (id₂ {f = u₁}) κ)))) ⟩
    (q₂ ◁ τ) • (((q₂ ◁ (u₁ ◁ κ)) • assoc⇒ q₂ u₁ p₁')
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congʳ •-assoc ⟩
    (q₂ ◁ τ) • ((q₂ ◁ (u₁ ◁ κ)) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁')))
      ≈⟨ ≈-sym •-assoc ⟩
    ((q₂ ◁ τ) • (q₂ ◁ (u₁ ◁ κ))) • (assoc⇒ q₂ u₁ p₁'
      • ((σ' ▷ p₁') • assoc⇐ u₂ p₂ p₁'))
      ≈⟨ •-congˡ (≈-sym (◁-• q₂ τ (u₁ ◁ κ))) ⟩
    fpaste u₁ u₂ p₁' p₂ q₁ q₂ σ' (τ • (u₁ ◁ κ)) ∎
    where open ⇒₂-Reasoning

  fpaste-assoc :
    {a₀ a₁ a₂ a₃ b₁ b₂ b₃ : Obj}
    (u₁ : a₁ ⇒₁ b₁) (u₂ : a₂ ⇒₁ b₂) (u₃ : a₃ ⇒₁ b₃)
    (p₁ : a₀ ⇒₁ a₁) (p₂ : a₁ ⇒₁ a₂) (p₃ : a₂ ⇒₁ a₃)
    (q₁ : a₀ ⇒₁ b₁) (q₂ : b₁ ⇒₁ b₂) (q₃ : b₂ ⇒₁ b₃)
    (σ₃ : (u₃ ∘₁ p₃) ⇒₂ (q₃ ∘₁ u₂)) (σ₂ : (u₂ ∘₁ p₂) ⇒₂ (q₂ ∘₁ u₁))
    (τ : (u₁ ∘₁ p₁) ⇒₂ q₁) →
    assoc⇒ q₃ q₂ q₁ •
      fpaste u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) τ
    ≈ fpaste u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
        (fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ)
        • (u₃ ◁ assoc⇒ p₃ p₂ p₁)
  fpaste-assoc u₁ u₂ u₃ p₁ p₂ p₃ q₁ q₂ q₃ σ₃ σ₂ τ = begin
    assoc⇒ q₃ q₂ q₁ •
      fpaste u₁ u₃ p₁ (p₃ ∘₁ p₂) q₁ (q₃ ∘₁ q₂)
        (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂) τ
      ≈⟨ •-congʳ (•-congʳ (•-congʳ expandL)) ⟩
    L9 • (L8 • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ ≈-sym •-assoc ⟩
    (L9 • L8) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-congˡ step2 ⟩
    (R8 • A₂) • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-assoc ⟩
    R8 • (A₂ • (L7 • (L6 • (L5 • (L4 • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (≈-trans (•-congʳ (≈-sym •-assoc)) (≈-sym •-assoc)) ⟩
    R8 • ((A₂ • (L7 • L6)) • (L5 • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congˡ step3) ⟩
    R8 • ((R7 • A₃) • (L5 • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ •-assoc ⟩
    R8 • (R7 • (A₃ • (L5 • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
    R8 • (R7 • ((A₃ • L5) • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ (•-congˡ step4)) ⟩
    R8 • (R7 • ((R6 • A₄) • (L4 • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ •-assoc) ⟩
    R8 • (R7 • (R6 • (A₄ • (L4 • (L3 • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))) ⟩
    R8 • (R7 • (R6 • ((A₄ • L4) • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congˡ step5))) ⟩
    R8 • (R7 • (R6 • ((R5 • (R4 • A₅)) • (L3 • (L2 • L1)))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (≈-trans •-assoc (•-congʳ •-assoc)))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • (A₅ • (L3 • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (≈-sym •-assoc))))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • ((A₅ • L3) • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congˡ step6))))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • ((R3 • A₆) • (L2 • L1))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ •-assoc)))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (A₆ • (L2 • L1)))))))
      ≈⟨ •-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ (•-congʳ step7))))) ⟩
    R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))
      ≈⟨ ≈-sym expandR ⟩
    fpaste u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
      (fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ)
      • (u₃ ◁ assoc⇒ p₃ p₂ p₁) ∎
    where
      open ⇒₂-Reasoning

      L1 = assoc⇐ u₃ (p₃ ∘₁ p₂) p₁
      L2 = assoc⇐ u₃ p₃ p₂ ▷ p₁
      L3 = (σ₃ ▷ p₂) ▷ p₁
      L4 = assoc⇒ q₃ u₂ p₂ ▷ p₁
      L5 = (q₃ ◁ σ₂) ▷ p₁
      L6 = assoc⇐ q₃ q₂ u₁ ▷ p₁
      L7 = assoc⇒ (q₃ ∘₁ q₂) u₁ p₁
      L8 = (q₃ ∘₁ q₂) ◁ τ
      L9 = assoc⇒ q₃ q₂ q₁

      R1 = u₃ ◁ assoc⇒ p₃ p₂ p₁
      R2 = assoc⇐ u₃ p₃ (p₂ ∘₁ p₁)
      R3 = σ₃ ▷ (p₂ ∘₁ p₁)
      R4 = assoc⇒ q₃ u₂ (p₂ ∘₁ p₁)
      R5 = q₃ ◁ assoc⇐ u₂ p₂ p₁
      R6 = q₃ ◁ (σ₂ ▷ p₁)
      R7 = q₃ ◁ assoc⇒ q₂ u₁ p₁
      R8 = q₃ ◁ (q₂ ◁ τ)

      A₂ = assoc⇒ q₃ q₂ (u₁ ∘₁ p₁)
      A₃ = assoc⇒ q₃ (q₂ ∘₁ u₁) p₁
      A₄ = assoc⇒ q₃ (u₂ ∘₁ p₂) p₁
      A₅ = assoc⇒ (q₃ ∘₁ u₂) p₂ p₁
      A₆ = assoc⇒ (u₃ ∘₁ p₃) p₂ p₁

      expandL : (paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁) • L1
                ≈ L6 • (L5 • (L4 • (L3 • (L2 • L1))))
      expandL = ≈-trans (•-congˡ expand▷)
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc))))))
        where
          expand▷ : paste u₁ u₂ u₃ p₂ p₃ q₂ q₃ σ₃ σ₂ ▷ p₁
                    ≈ L6 • (L5 • (L4 • (L3 • L2)))
          expand▷ =
            ≈-trans (▷-• (assoc⇐ q₃ q₂ u₁)
                         ((q₃ ◁ σ₂) • (assoc⇒ q₃ u₂ p₂
                           • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂))) p₁)
            (•-congʳ (≈-trans (▷-• (q₃ ◁ σ₂)
                         (assoc⇒ q₃ u₂ p₂ • ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂)) p₁)
            (•-congʳ (≈-trans (▷-• (assoc⇒ q₃ u₂ p₂)
                         ((σ₃ ▷ p₂) • assoc⇐ u₃ p₃ p₂) p₁)
            (•-congʳ (▷-• (σ₃ ▷ p₂) (assoc⇐ u₃ p₃ p₂) p₁))))))

      expandR : fpaste u₂ u₃ (p₂ ∘₁ p₁) p₃ (q₂ ∘₁ q₁) q₃ σ₃
                  (fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ) • R1
                ≈ R8 • (R7 • (R6 • (R5 • (R4 • (R3 • (R2 • R1))))))
      expandR = ≈-trans (•-congˡ (•-congˡ expand◁))
                (≈-trans (•-congˡ
                  (≈-trans •-assoc (•-congʳ
                  (≈-trans •-assoc (•-congʳ •-assoc)))))
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ
                (≈-trans •-assoc (•-congʳ •-assoc)))))))))))
        where
          expand◁ : q₃ ◁ fpaste u₁ u₂ p₁ p₂ q₁ q₂ σ₂ τ
                    ≈ R8 • (R7 • (R6 • R5))
          expand◁ =
            ≈-trans (◁-• q₃ (q₂ ◁ τ)
                         (assoc⇒ q₂ u₁ p₁ • ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁)))
            (•-congʳ (≈-trans (◁-• q₃ (assoc⇒ q₂ u₁ p₁)
                         ((σ₂ ▷ p₁) • assoc⇐ u₂ p₂ p₁))
            (•-congʳ (◁-• q₃ (σ₂ ▷ p₁) (assoc⇐ u₂ p₂ p₁)))))

      step2 : L9 • L8 ≈ R8 • A₂
      step2 = ≈-sym (≈-trans (assoc-natural (id₂ {f = q₃}) (id₂ {f = q₂}) τ)
                             (•-congʳ (∗-cong (∗-id q₃ q₂) ≈-refl)))

      step3 : A₂ • (L7 • L6) ≈ R7 • A₃
      step3 = begin
        A₂ • (L7 • L6)
          ≈⟨ ≈-sym •-assoc ⟩
        (A₂ • L7) • L6
          ≈⟨ •-congˡ (pentagon q₃ q₂ u₁ p₁) ⟩
        (R7 • (A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁))) • L6
          ≈⟨ •-assoc ⟩
        R7 • ((A₃ • (assoc⇒ q₃ q₂ u₁ ▷ p₁)) • L6)
          ≈⟨ •-congʳ •-assoc ⟩
        R7 • (A₃ • ((assoc⇒ q₃ q₂ u₁ ▷ p₁) • L6))
          ≈⟨ •-congʳ (•-congʳ (≈-trans (≈-sym (▷-• (assoc⇒ q₃ q₂ u₁)
                                                   (assoc⇐ q₃ q₂ u₁) p₁))
                              (≈-trans (▷-cong p₁ (≅₂isoʳ (associator q₃ q₂ u₁)))
                                       (▷-id (q₃ ∘₁ (q₂ ∘₁ u₁)) p₁)))) ⟩
        R7 • (A₃ • id₂)
          ≈⟨ •-congʳ •-identityʳ ⟩
        R7 • A₃ ∎

      step4 : A₃ • L5 ≈ R6 • A₄
      step4 = ≈-sym (assoc-natural (id₂ {f = q₃}) σ₂ (id₂ {f = p₁}))

      step5 : A₄ • L4 ≈ R5 • (R4 • A₅)
      step5 = ≈-sym (begin
        R5 • (R4 • A₅)
          ≈⟨ •-congʳ (pentagon q₃ u₂ p₂ p₁) ⟩
        R5 • ((q₃ ◁ assoc⇒ u₂ p₂ p₁) • (A₄ • L4))
          ≈⟨ ≈-sym •-assoc ⟩
        (R5 • (q₃ ◁ assoc⇒ u₂ p₂ p₁)) • (A₄ • L4)
          ≈⟨ •-congˡ (≈-trans (≈-sym (◁-• q₃ (assoc⇐ u₂ p₂ p₁)
                                              (assoc⇒ u₂ p₂ p₁)))
                     (≈-trans (◁-cong q₃ (≅₂isoˡ (associator u₂ p₂ p₁)))
                              (◁-id q₃ ((u₂ ∘₁ p₂) ∘₁ p₁)))) ⟩
        id₂ • (A₄ • L4)
          ≈⟨ •-identityˡ ⟩
        A₄ • L4 ∎)

      step6 : A₅ • L3 ≈ R3 • A₆
      step6 = ≈-sym (≈-trans (•-congˡ (∗-cong ≈-refl (≈-sym (∗-id p₂ p₁))))
                             (assoc-natural σ₃ (id₂ {f = p₂}) (id₂ {f = p₁})))

      step7 : A₆ • (L2 • L1) ≈ R2 • R1
      step7 = Hom.∘-cancelˡ (invertible-≅₂ (associator u₃ p₃ (p₂ ∘₁ p₁))) (begin
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (A₆ • (L2 • L1))
          ≈⟨ ≈-sym •-assoc ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • A₆) • (L2 • L1)
          ≈⟨ •-congˡ (pentagon u₃ p₃ p₂ p₁) ⟩
        (R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁))) • (L2 • L1)
          ≈⟨ •-assoc ⟩
        R1 • ((assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (assoc⇒ u₃ p₃ p₂ ▷ p₁)) • (L2 • L1))
          ≈⟨ •-congʳ •-assoc ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • ((assoc⇒ u₃ p₃ p₂ ▷ p₁) • (L2 • L1)))
          ≈⟨ •-congʳ (•-congʳ (≈-sym •-assoc)) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (((assoc⇒ u₃ p₃ p₂ ▷ p₁) • L2) • L1))
          ≈⟨ •-congʳ (•-congʳ (•-congˡ
               (≈-trans (≈-sym (▷-• (assoc⇒ u₃ p₃ p₂) (assoc⇐ u₃ p₃ p₂) p₁))
               (≈-trans (▷-cong p₁ (≅₂isoʳ (associator u₃ p₃ p₂)))
                        (▷-id (u₃ ∘₁ (p₃ ∘₁ p₂)) p₁))))) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • (id₂ • L1))
          ≈⟨ •-congʳ (•-congʳ •-identityˡ) ⟩
        R1 • (assoc⇒ u₃ (p₃ ∘₁ p₂) p₁ • L1)
          ≈⟨ •-congʳ (≅₂isoʳ (associator u₃ (p₃ ∘₁ p₂) p₁)) ⟩
        R1 • id₂
          ≈⟨ •-identityʳ ⟩
        R1
          ≈⟨ ≈-sym •-identityˡ ⟩
        id₂ • R1
          ≈⟨ •-congˡ (≈-sym (≅₂isoʳ (associator u₃ p₃ (p₂ ∘₁ p₁)))) ⟩
        (assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • R2) • R1
          ≈⟨ •-assoc ⟩
        assoc⇒ u₃ p₃ (p₂ ∘₁ p₁) • (R2 • R1) ∎)
