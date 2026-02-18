import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Bicategory.SingleObj
import Mathlib.CategoryTheory.Bicategory.Functor.Lax

open CategoryTheory

instance : Monoid Unit where
  mul _ _ := ()
  mul_assoc _ _ _ := by rfl
  one := ()
  one_mul _ := by rfl
  mul_one _ := by rfl

-- wht is the different between Unit and PUnit
#check Unit
#check PUnit

abbrev triv := MonoidalSingleObj <| Discrete Unit

open Bicategory

variable (B : Type) [Bicategory B]

/-
A monad of a bicategory B is a lax functor M : 𝟙 ⥤ B, where 𝟙 is the terminal bicategory.
-/
def monad := triv ⥤ᴸ B
