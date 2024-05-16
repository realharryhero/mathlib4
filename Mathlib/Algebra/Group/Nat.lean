/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.TypeTags
import Mathlib.Algebra.Group.Units

#align_import data.nat.basic from "leanprover-community/mathlib"@"bd835ef554f37ef9b804f0903089211f89cb370b"
#align_import data.nat.units from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-!
# The natural numbers form a monoid

This file contains the additive and multiplicative monoid instances on the natural numbers.

See note [foundational algebra order theory].
-/

assert_not_exists Ring

open Multiplicative

namespace Nat

/-! ### Instances -/

instance instAddCommMonoid : AddCommMonoid ℕ where
  add := Nat.add
  add_assoc := Nat.add_assoc
  zero := Nat.zero
  zero_add := Nat.zero_add
  add_zero := Nat.add_zero
  add_comm := Nat.add_comm
  nsmul m n := m * n
  nsmul_zero := Nat.zero_mul
  nsmul_succ := succ_mul

instance instCommMonoid : CommMonoid ℕ where
  mul := Nat.mul
  mul_assoc := Nat.mul_assoc
  one := Nat.succ Nat.zero
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
  mul_comm := Nat.mul_comm
  npow m n := n ^ m
  npow_zero := Nat.pow_zero
  npow_succ _ _ := rfl

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instAddMonoid        : AddMonoid ℕ        := by infer_instance
instance instMonoid           : Monoid ℕ           := by infer_instance
instance instCommSemigroup    : CommSemigroup ℕ    := by infer_instance
instance instSemigroup        : Semigroup ℕ        := by infer_instance
instance instAddCommSemigroup : AddCommSemigroup ℕ := by infer_instance
instance instAddSemigroup     : AddSemigroup ℕ     := by infer_instance

/-! ### Miscellaneous lemmas -/

protected lemma nsmul_eq_mul (m n : ℕ) : m • n = m * n := rfl
#align nat.nsmul_eq_mul Nat.nsmul_eq_mul

section Multiplicative

lemma toAdd_pow (a : Multiplicative ℕ) (b : ℕ) : toAdd (a ^ b) = toAdd a * b := mul_comm _ _
#align nat.to_add_pow Nat.toAdd_pow

@[simp] lemma ofAdd_mul (a b : ℕ) : ofAdd (a * b) = ofAdd a ^ b := (toAdd_pow _ _).symm
#align nat.of_add_mul Nat.ofAdd_mul

end Multiplicative

/-! ### Units -/

lemma units_eq_one (u : ℕˣ) : u = 1 := Units.ext <| Nat.eq_one_of_dvd_one ⟨u.inv, u.val_inv.symm⟩
#align nat.units_eq_one Nat.units_eq_one

lemma addUnits_eq_zero (u : AddUnits ℕ) : u = 0 :=
  AddUnits.ext <| (Nat.eq_zero_of_add_eq_zero u.val_neg).1
#align nat.add_units_eq_zero Nat.addUnits_eq_zero

@[simp] protected lemma isUnit_iff {n : ℕ} : IsUnit n ↔ n = 1 where
  mp := by rintro ⟨u, rfl⟩; obtain rfl := Nat.units_eq_one u; rfl
  mpr h := h.symm ▸ ⟨1, rfl⟩
#align nat.is_unit_iff Nat.isUnit_iff

instance unique_units : Unique ℕˣ where
  default := 1
  uniq := Nat.units_eq_one
#align nat.unique_units Nat.unique_units

instance unique_addUnits : Unique (AddUnits ℕ) where
  default := 0
  uniq := Nat.addUnits_eq_zero
#align nat.unique_add_units Nat.unique_addUnits

end Nat
