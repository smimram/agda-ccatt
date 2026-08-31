import Bicategory as Bicat
open Bicat using (Bicategory)
import Bifunctor as Bifun
open Bifun using (Bifunctor)

-- A biuniversal arrow from a bifunctor to an object
record Universal1
  {C : Bicategory {!!} {!!} {!!} {!!}}
  {D : Bicategory {!!} {!!} {!!} {!!}}
  (F : Bifunctor C D)
  (y : Bicategory.Obj D)
  : Set {!!}
  where

  private module C = Bicategory C
  private module D = Bicategory D
  private module F = Bifunctor F

  field
    U₀ : C.Obj
    U₁ : F.F₀ U₀ D.⇒₁ y
    ε : {x : C.Obj} (f : F.F₀ x D.⇒₁ y) → {!!}
