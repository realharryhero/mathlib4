/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Module.Hom

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
TODO

## Tags
linear algebra, vector space, module

-/

open Function

/-! ### Properties of linear maps -/

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
def addMonoidHomLequivNat {A B : Type*} (R : Type*) [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℕ] B
    where
  toFun := AddMonoidHom.toNatLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_nat addMonoidHomLequivNat

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
def addMonoidHomLequivInt {A B : Type*} (R : Type*) [Semiring R] [AddCommGroup A] [AddCommGroup B]
    [Module R B] : (A →+ B) ≃ₗ[R] A →ₗ[ℤ] B
    where
  toFun := AddMonoidHom.toIntLinearMap
  invFun := LinearMap.toAddMonoidHom
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl
  left_inv := by intro f; ext; rfl
  right_inv := by intro f; ext; rfl
#align add_monoid_hom_lequiv_int addMonoidHomLequivInt

/-- Ring equivalence between additive group endomorphisms of an `AddCommGroup` `A` and
`ℤ`-module endomorphisms of `A.` -/
@[simps] def addMonoidEndRingEquivInt (A : Type*) [AddCommGroup A] :
    AddMonoid.End A ≃+* Module.End ℤ A :=
  { addMonoidHomLequivInt (B := A) ℤ with
    map_mul' := fun _ _ => rfl }
