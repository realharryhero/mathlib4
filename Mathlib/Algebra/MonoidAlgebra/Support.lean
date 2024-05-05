/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finset.Pointwise

#align_import algebra.monoid_algebra.support from "leanprover-community/mathlib"@"16749fc4661828cba18cd0f4e3c5eb66a8e80598"

/-!
#  Lemmas about the support of a finitely supported function
-/

open scoped Pointwise

universe u₁ u₂ u₃

namespace MonoidAlgebra

open Finset Finsupp

variable {k : Type u₁} {G : Type u₂} [Semiring k]

theorem support_mul [Mul G] [DecidableEq G] (a b : MonoidAlgebra k G) :
    (a * b).support ⊆ a.support * b.support := by
  rw [MonoidAlgebra.mul_def]
  exact support_sum.trans <| biUnion_subset.2 fun _x hx ↦
    support_sum.trans <| biUnion_subset.2 fun _y hy ↦
      support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy
#align monoid_algebra.support_mul MonoidAlgebra.support_mul

theorem support_single_mul_subset [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) (r : k) (a : G) :
    (single a r * f : MonoidAlgebra k G).support ⊆ Finset.image (a * ·) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_right support_single_subset).trans <| by
    rw [Finset.image₂_singleton_left]
#align monoid_algebra.support_single_mul_subset MonoidAlgebra.support_single_mul_subset

theorem support_mul_single_subset [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_left support_single_subset).trans <| by
    rw [Finset.image₂_singleton_right]
#align monoid_algebra.support_mul_single_subset MonoidAlgebra.support_mul_single_subset

theorem support_single_mul_eq_image [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) {r : k}
    (hr : ∀ y, r * y = 0 ↔ y = 0) {x : G} (lx : IsLeftRegular x) :
    (single x r * f : MonoidAlgebra k G).support = Finset.image (x * ·) f.support := by
  refine' subset_antisymm (support_single_mul_subset f _ _) fun y hy => _
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp only [mul_apply, mem_support_iff.mp yf, hr, mem_support_iff, sum_single_index,
    Finsupp.sum_ite_eq', Ne, not_false_iff, if_true, zero_mul, ite_self, sum_zero, lx.eq_iff]
#align monoid_algebra.support_single_mul_eq_image MonoidAlgebra.support_single_mul_eq_image

theorem support_mul_single_eq_image [DecidableEq G] [Mul G] (f : MonoidAlgebra k G) {r : k}
    (hr : ∀ y, y * r = 0 ↔ y = 0) {x : G} (rx : IsRightRegular x) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine' subset_antisymm (support_mul_single_subset f _ _) fun y hy => _
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp only [mul_apply, mem_support_iff.mp yf, hr, mem_support_iff, sum_single_index,
    Finsupp.sum_ite_eq', Ne, not_false_iff, if_true, mul_zero, ite_self, sum_zero, rx.eq_iff]
#align monoid_algebra.support_mul_single_eq_image MonoidAlgebra.support_mul_single_eq_image

theorem support_mul_single [Mul G] [IsRightCancelMul G] (f : MonoidAlgebra k G) (r : k)
    (hr : ∀ y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
    ext
    simp only [support_mul_single_eq_image f hr (IsRightRegular.all x),
      mem_image, mem_map, mulRightEmbedding_apply]
#align monoid_algebra.support_mul_single MonoidAlgebra.support_mul_single

theorem support_single_mul [Mul G] [IsLeftCancelMul G] (f : MonoidAlgebra k G) (r : k)
    (hr : ∀ y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : MonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
    ext
    simp only [support_single_mul_eq_image f hr (IsLeftRegular.all x), mem_image,
      mem_map, mulLeftEmbedding_apply]
#align monoid_algebra.support_single_mul MonoidAlgebra.support_single_mul

lemma support_one_subset [One G] : (1 : MonoidAlgebra k G).support ⊆ 1 :=
  Finsupp.support_single_subset

@[simp]
lemma support_one [One G] [NeZero (1 : k)] : (1 : MonoidAlgebra k G).support = 1 :=
  Finsupp.support_single_ne_zero _ one_ne_zero

section Span

variable [MulOneClass G]

/-- An element of `MonoidAlgebra k G` is in the subalgebra generated by its support. -/
theorem mem_span_support (f : MonoidAlgebra k G) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  erw [of, MonoidHom.coe_mk, ← supported_eq_span_single, Finsupp.mem_supported]
#align monoid_algebra.mem_span_support MonoidAlgebra.mem_span_support

end Span

end MonoidAlgebra

namespace AddMonoidAlgebra

open Finset Finsupp MulOpposite

variable {k : Type u₁} {G : Type u₂} [Semiring k]

theorem support_mul [DecidableEq G] [Add G] (a b : k[G]) :
    (a * b).support ⊆ a.support + b.support :=
  @MonoidAlgebra.support_mul k (Multiplicative G) _ _ _ _ _
#align add_monoid_algebra.support_mul AddMonoidAlgebra.support_mul

theorem support_mul_single [Add G] [IsRightCancelAdd G] (f : k[G]) (r : k)
    (hr : ∀ y, y * r = 0 ↔ y = 0) (x : G) :
    (f * single x r : k[G]).support = f.support.map (addRightEmbedding x) :=
  MonoidAlgebra.support_mul_single (G := Multiplicative G) _ _ hr _
#align add_monoid_algebra.support_mul_single AddMonoidAlgebra.support_mul_single

theorem support_single_mul [Add G] [IsLeftCancelAdd G] (f : k[G]) (r : k)
    (hr : ∀ y, r * y = 0 ↔ y = 0) (x : G) :
    (single x r * f : k[G]).support = f.support.map (addLeftEmbedding x) :=
  MonoidAlgebra.support_single_mul (G := Multiplicative G) _ _ hr _
#align add_monoid_algebra.support_single_mul AddMonoidAlgebra.support_single_mul

lemma support_one_subset [Zero G] : (1 : k[G]).support ⊆ 0 := Finsupp.support_single_subset

@[simp]
lemma support_one [Zero G] [NeZero (1 : k)] : (1 : k[G]).support = 0 :=
  Finsupp.support_single_ne_zero _ one_ne_zero

section Span

/-- An element of `k[G]` is in the submodule generated by its support. -/
theorem mem_span_support [AddZeroClass G] (f : k[G]) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  erw [of, MonoidHom.coe_mk, ← Finsupp.supported_eq_span_single, Finsupp.mem_supported]
#align add_monoid_algebra.mem_span_support AddMonoidAlgebra.mem_span_support

/-- An element of `k[G]` is in the subalgebra generated by its support, using
unbundled inclusion. -/
theorem mem_span_support' (f : k[G]) :
    f ∈ Submodule.span k (of' k G '' (f.support : Set G)) := by
  delta of'
  rw [← Finsupp.supported_eq_span_single, Finsupp.mem_supported]
#align add_monoid_algebra.mem_span_support' AddMonoidAlgebra.mem_span_support'

end Span

end AddMonoidAlgebra
