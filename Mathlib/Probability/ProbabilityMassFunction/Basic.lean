/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathlib.Topology.Instances.ENNReal
import Mathlib.MeasureTheory.Measure.Dirac

#align_import probability.probability_mass_function.basic from "leanprover-community/mathlib"@"4ac69b290818724c159de091daa3acd31da0ee6d"

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `ProbabilityMassFunction/Monad.lean`,
other constructions of `Pmf`s are found in `ProbabilityMassFunction/Constructions.lean`.

Given `p : Pmf α`, `Pmf.toOuterMeasure` constructs an `OuterMeasure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `Measure` on `α`, see `Pmf.toMeasure`.
`Pmf.toMeasure.isProbabilityMeasure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.toPmf` constructs a `Pmf` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/


noncomputable section

variable {α β γ : Type*}

open Classical BigOperators NNReal ENNReal MeasureTheory

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such
  that the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0 // ∑' (x : α), (f x : ℝ≥0∞) = 1 }
#align pmf Pmf

namespace Pmf

instance funLike : FunLike (Pmf α) α fun _ => ℝ≥0 where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h
#align pmf.fun_like Pmf.funLike

@[ext]
protected theorem ext {p q : Pmf α} (h : ∀ x, p x = q x) : p = q :=
  FunLike.ext p q h
#align pmf.ext Pmf.ext

theorem ext_iff {p q : Pmf α} : p = q ↔ ∀ x, p x = q x :=
  FunLike.ext_iff
#align pmf.ext_iff Pmf.ext_iff

theorem hasSum_coe_ennreal_one (p : Pmf α) : HasSum (fun x => (p x : ℝ≥0∞)) 1 :=
  ENNReal.summable.hasSum_iff.2 p.2

@[simp]
theorem tsum_coe_ennreal (p : Pmf α) : ∑' (x : α), (p x : ℝ≥0∞) = 1 := p.2

theorem tsum_coe_ennreal_ne_top (p : Pmf α) : ∑' (x : α), (p x : ℝ≥0∞) ≠ ⊤ := by simp

lemma summable (p : Pmf α) : Summable p := by
  have := ENNReal.summable_toNNReal_of_tsum_ne_top p.tsum_coe_ennreal_ne_top
  apply this

theorem hasSum_coe_one (p : Pmf α) : HasSum p 1 := by
  have := ENNReal.hassum_toNNReal_of_hassum_of_ne_top 1 one_ne_top p.tsum_coe_ennreal
  simpa
#align pmf.has_sum_coe_one Pmf.hasSum_coe_one

@[simp]
theorem tsum_coe (p : Pmf α) : ∑' a, p a = 1 := p.hasSum_coe_one.tsum_eq
#align pmf.tsum_coe Pmf.tsum_coe


lemma summable_indicator (p : Pmf α) (s : Set α) : Summable (fun x => s.indicator p x) :=
  NNReal.summable_of_le (fun _ => Set.indicator_apply_le (fun _ => le_refl _)) p.summable

lemma summable_ite (p : Pmf α) (x : α) : Summable (fun y => ite (y = x) 0 (p y)) :=
  NNReal.summable_of_le (fun x => by {split_ifs <;> simp}) p.summable

theorem tsum_coe_indicator_le_on (p : Pmf α) (s : Set α) : ∑' a, s.indicator p a ≤ 1 := calc
  ∑' a, s.indicator p a ≤ ∑' a, p a := tsum_le_tsum
    (fun _ => Set.indicator_apply_le (fun _ => le_rfl)) (p.summable_indicator s) p.summable
  _ = 1 := tsum_coe p

  -- ne_of_lt (lt_of_le_of_lt
  --   (tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl) ENNReal.summable
  --     ENNReal.summable)
  --   (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp]
theorem coe_ne_zero (p : Pmf α) : ⇑p ≠ 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)
#align pmf.coe_ne_zero Pmf.coe_ne_zero

/-- The support of a `Pmf` is the set where it is nonzero. -/
def support (p : Pmf α) : Set α :=
  Function.support p
#align pmf.support Pmf.support

@[simp]
theorem mem_support_iff (p : Pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl
#align pmf.mem_support_iff Pmf.mem_support_iff

@[simp]
theorem support_nonempty (p : Pmf α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero
#align pmf.support_nonempty Pmf.support_nonempty

@[simp]
theorem support_countable (p : Pmf α) : p.support.Countable :=
  Summable.countable_support_nnreal p p.summable

theorem apply_eq_zero_iff (p : Pmf α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]
#align pmf.apply_eq_zero_iff Pmf.apply_eq_zero_iff

theorem apply_pos_iff (p : Pmf α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm
#align pmf.apply_pos_iff Pmf.apply_pos_iff

theorem apply_eq_one_iff (p : Pmf α) (a : α) : p a = 1 ↔ p.support = {a} := by
  refine' ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => _)
    fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a by exact ne_of_lt this p.tsum_coe.symm
  calc
    1 = p a := h.symm
    _ < p a + p a' := lt_add_of_pos_right _ $ Iff.mpr (apply_pos_iff p a') ha'
    _ = p a + ite (a' = a) 0 (p a') := by simp at ha; simp [ha]
    _ ≤ p a + ∑' b, ite (b = a) 0 (p b) := add_le_add_left (le_tsum' (summable_ite p a) a') _
    _ = ∑' b, p b := (NNReal.tsum_eq_add_tsum_ite (summable p) a).symm
#align pmf.apply_eq_one_iff Pmf.apply_eq_one_iff


theorem apply_le_one (p : Pmf α) (a : α) : p a ≤ 1 := by
  refine' hasSum_le (fun b => _) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp only [h, zero_le', le_rfl]

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

/-- Construct an `OuterMeasure` from a `Pmf`, by assigning measure to each set `s : Set α` equal
  to the sum of `p x` for each `x ∈ α`. -/
def toOuterMeasure (p : Pmf α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => (p x : ℝ≥0∞) • dirac x
#align pmf.to_outer_measure Pmf.toOuterMeasure

variable (p : Pmf α) (s t : Set α)

theorem toOuterMeasure_apply :
    p.toOuterMeasure s = ∑' x, s.indicator (fun x => (p x : ℝ≥0∞)) x := by
  apply tsum_congr fun x => smul_dirac_apply (p x) x s
#align pmf.to_outer_measure_apply Pmf.toOuterMeasure_apply

@[simp]
theorem toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤ := by
  refine' eq_top_iff.2 <| le_trans (le_sInf fun x hx => _) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)
#align pmf.to_outer_measure_caratheodory Pmf.toOuterMeasure_caratheodory

@[simp]
theorem toOuterMeasure_apply_finite (hs : s.Finite) :
    p.toOuterMeasure s = ∑ x in hs.toFinset, p x := by
  simp [toOuterMeasure_apply p s, sum_eq_tsum_indicator,
    ENNReal.coe_tsum (p.summable_indicator _), ENNReal.coe_indicator]

@[simp]
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s, p x := by simp
#align pmf.to_outer_measure_apply_finset Pmf.toOuterMeasure_apply_finset

theorem toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a := by simp
#align pmf.to_outer_measure_apply_singleton Pmf.toOuterMeasure_apply_singleton

theorem toOuterMeasure_injective : (toOuterMeasure : Pmf α → OuterMeasure α).Injective :=
  fun p q h => Pmf.ext fun x => by
    have : p.toOuterMeasure ({x} : Set α) = q.toOuterMeasure {x} := by rw [h]
    simpa
#align pmf.to_outer_measure_injective Pmf.toOuterMeasure_injective

@[simp]
theorem toOuterMeasure_inj {p q : Pmf α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff
#align pmf.to_outer_measure_inj Pmf.toOuterMeasure_inj

theorem toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  simp_rw [ Pmf.support, Function.support_disjoint_iff (f := p) (s := s)]
  apply forall_congr'
  simp
#align pmf.to_outer_measure_apply_eq_zero_iff Pmf.toOuterMeasure_apply_eq_zero_iff

theorem toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support ⊆ s := by
  refine' (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => _, fun h => _⟩
  · refine' by_contra fun hs => ne_of_lt _ h
    suffices ∑' (x : α), Set.indicator s (fun x => (p x : ℝ≥0∞)) x < ∑' (x : α), (p x : ℝ≥0∞)
      by simpa
    apply ENNReal.tsum_lt_tsum
    · sorry
    · exact (fun x => Set.indicator_apply_le fun _ => le_rfl)
    · calc s.indicator (fun x => (p x : ℝ≥0∞)) a = 0 :=
          Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
        _ < p a := sorry -- (p.apply_pos_iff a).2 hap
  · suffices ∑' (x : α), Set.indicator s (↑p) x = ∑' (x : α), p x by simpa
    apply tsum_congr
    · intro x
      have h : ∀ (_ : x ∉ s), p x = 0 := fun hx =>
        (p.apply_eq_zero_iff x).2 <| Set.not_mem_subset h hx
      simp [Set.indicator_apply]
      tauto
#align pmf.to_outer_measure_apply_eq_one_iff Pmf.toOuterMeasure_apply_eq_one_iff

@[simp]
theorem toOuterMeasure_apply_inter_support :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [toOuterMeasure_apply, Pmf.support, Set.indicator_inter_support]
#align pmf.to_outer_measure_apply_inter_support Pmf.toOuterMeasure_apply_inter_support

/-- Slightly stronger than `OuterMeasure.mono` having an intersection with `p.support`. -/
theorem toOuterMeasure_mono {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)
#align pmf.to_outer_measure_mono Pmf.toOuterMeasure_mono

theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left t p.support))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left s p.support))
#align pmf.to_outer_measure_apply_eq_of_inter_support_eq Pmf.toOuterMeasure_apply_eq_of_inter_support_eq

@[simp]
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x := by
  rw [p.toOuterMeasure_apply]
  congr 1
  apply tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h
#align pmf.to_outer_measure_apply_fintype Pmf.toOuterMeasure_apply_fintype

end OuterMeasure

section Measure

open MeasureTheory

/-- Since every set is Carathéodory-measurable under `Pmf.toOuterMeasure`,
  we can further extend this `OuterMeasure` to a `Measure` on `α`. -/
def toMeasure [MeasurableSpace α] (p : Pmf α) : Measure α :=
  p.toOuterMeasure.toMeasure ((toOuterMeasure_caratheodory p).symm ▸ le_top)
#align pmf.to_measure Pmf.toMeasure

variable [MeasurableSpace α] (p : Pmf α) (s t : Set α)

theorem toOuterMeasure_apply_le_toMeasure_apply : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s
#align pmf.to_outer_measure_apply_le_to_measure_apply Pmf.toOuterMeasure_apply_le_toMeasure_apply

theorem toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs
#align pmf.to_measure_apply_eq_to_outer_measure_apply Pmf.toMeasure_apply_eq_toOuterMeasure_apply

theorem toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs).trans (p.toOuterMeasure_apply s)
#align pmf.to_measure_apply Pmf.toMeasure_apply

theorem toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [toMeasure_apply_eq_toOuterMeasure_apply _ _ h, toOuterMeasure_apply_singleton]
#align pmf.to_measure_apply_singleton Pmf.toMeasure_apply_singleton

theorem toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply p s hs, toOuterMeasure_apply_eq_zero_iff]
#align pmf.to_measure_apply_eq_zero_iff Pmf.toMeasure_apply_eq_zero_iff

theorem toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s
#align pmf.to_measure_apply_eq_one_iff Pmf.toMeasure_apply_eq_one_iff

@[simp]
theorem toMeasure_apply_inter_support (hs : MeasurableSet s) (hp : MeasurableSet p.support) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s := by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply s hs,
    p.toMeasure_apply_eq_toOuterMeasure_apply _ (hs.inter hp)]
#align pmf.to_measure_apply_inter_support Pmf.toMeasure_apply_inter_support

@[simp]
theorem restrict_toMeasure_support [MeasurableSpace α] [MeasurableSingletonClass α]  (p : Pmf α) :
    Measure.restrict (toMeasure p) (support p) = toMeasure p := by
  ext s hs
  apply (MeasureTheory.Measure.restrict_apply hs).trans
  apply toMeasure_apply_inter_support p s hs p.support_countable.measurableSet

theorem toMeasure_mono {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using toOuterMeasure_mono p h
#align pmf.to_measure_mono Pmf.toMeasure_mono

theorem toMeasure_apply_eq_of_inter_support_eq {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    toOuterMeasure_apply_eq_of_inter_support_eq p h
#align pmf.to_measure_apply_eq_of_inter_support_eq Pmf.toMeasure_apply_eq_of_inter_support_eq

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

theorem toMeasure_injective : (toMeasure : Pmf α → Measure α).Injective := by
  intro p q h
  ext1 x
  apply ENNReal.coe_injective
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x,
    ← q.toMeasure_apply_singleton x <| measurableSet_singleton x, h]
#align pmf.to_measure_injective Pmf.toMeasure_injective

@[simp]
theorem toMeasure_inj {p q : Pmf α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff
#align pmf.to_measure_inj Pmf.toMeasure_inj

@[simp]
theorem toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s s.measurableSet).trans
    (p.toOuterMeasure_apply_finset s)
#align pmf.to_measure_apply_finset Pmf.toMeasure_apply_finset

theorem toMeasure_apply_of_finite (hs : s.Finite) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs.measurableSet).trans (p.toOuterMeasure_apply s)
#align pmf.to_measure_apply_of_finite Pmf.toMeasure_apply_of_finite

@[simp]
theorem toMeasure_apply_fintype [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s s.toFinite.measurableSet).trans
    (p.toOuterMeasure_apply_fintype s)
#align pmf.to_measure_apply_fintype Pmf.toMeasure_apply_fintype

end MeasurableSingletonClass

end Measure

end Pmf

namespace MeasureTheory

open Pmf

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `Pmf`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toPmf [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : Pmf α :=
  ⟨fun x => (μ ({x} : Set α)).toNNReal, by
    simp_rw [fun x=>coe_toNNReal (measure_ne_top μ {x}), tsum_singleton_univ, measure_univ]⟩
#align measure_theory.measure.to_pmf MeasureTheory.Measure.toPmf

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ]

theorem toPmf_apply (x : α) : μ.toPmf x = (μ {x}).toNNReal := rfl
#align measure_theory.measure.to_pmf_apply MeasureTheory.Measure.toPmf_apply

@[simp]
theorem toPmf_toMeasure : μ.toPmf.toMeasure = μ :=
  Measure.ext fun s hs => by
    rw [μ.toPmf.toMeasure_apply s hs, ← μ.tsum_indicator_apply_singleton s hs, ENNReal.coe_tsum]
    · simp [toPmf_apply, measure_ne_top]
    · exact summable_indicator _ _
#align measure_theory.measure.to_pmf_to_measure MeasureTheory.Measure.toPmf_toMeasure

end Measure

end MeasureTheory

namespace Pmf

open MeasureTheory

/-- The measure associated to a `Pmf` by `toMeasure` is a probability measure. -/
instance toMeasure.isProbabilityMeasure [MeasurableSpace α] (p : Pmf α) :
    IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩
#align pmf.to_measure.is_probability_measure Pmf.toMeasure.isProbabilityMeasure

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : Pmf α) (μ : Measure α)
  [IsProbabilityMeasure μ]

@[simp]
theorem toMeasure_toPmf : p.toMeasure.toPmf = p :=
  Pmf.ext fun x => by
    rw [p.toMeasure.toPmf_apply, p.toMeasure_apply_singleton x (measurableSet_singleton x),
       toNNReal_coe]

#align pmf.to_measure_to_pmf Pmf.toMeasure_toPmf

theorem toMeasure_eq_iff_eq_toPmf (μ : Measure α) [IsProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPmf := by rw [← toMeasure_inj, Measure.toPmf_toMeasure]
#align pmf.to_measure_eq_iff_eq_to_pmf Pmf.toMeasure_eq_iff_eq_toPmf

theorem toPmf_eq_iff_toMeasure_eq (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.toPmf = p ↔ μ = p.toMeasure := by rw [← toMeasure_inj, Measure.toPmf_toMeasure]
#align pmf.to_pmf_eq_iff_to_measure_eq Pmf.toPmf_eq_iff_toMeasure_eq

end Pmf
