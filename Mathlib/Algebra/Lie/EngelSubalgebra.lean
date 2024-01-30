import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Data.Finset.NatAntidiagonal

open BigOperators LieAlgebra LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

lemma LinearMap.iterate_apply_eq_zero_of_le
    {f : M →ₗ[R] M} {m n : ℕ} {x : M} (hmn : m ≤ n) (hf : (f ^ m) x = 0) : (f ^ n) x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm _ k, pow_add, LinearMap.mul_apply, hf, map_zero]

-- move this
lemma toEndomorphism_lie (x y : L) (z : M) :
    (toEndomorphism R L M x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, toEndomorphism R L M x z⁆ := by
  simp

-- move this
lemma ad_lie (x y z : L) :
    (ad R L x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, ad R L x z⁆ :=
  toEndomorphism_lie x y z

-- move this
open Finset in
lemma toEndomorphism_pow_lie (x y : L) (z : M) (n : ℕ) :
    ((toEndomorphism R L M x) ^ n) ⁅y, z⁆ =
      ∑ ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((toEndomorphism R L M x) ^ ij.2) z⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j ↦ ⁅((ad R L x) ^ i) y, ((toEndomorphism R L M x) ^ j) z⁆) n]
    simp only [pow_succ, LinearMap.mul_apply, ih, map_sum, map_nsmul,
      toEndomorphism_lie, nsmul_add, sum_add_distrib]
    convert add_comm _ _ using 4
    rename_i ij hij
    rw [mem_antidiagonal, add_comm] at hij
    exact Nat.choose_symm_of_eq_add hij.symm

-- move this
open Finset in
lemma ad_pow_lie (x y z : L) (n : ℕ) :
    ((ad R L x) ^ n) ⁅y, z⁆ =
      ∑ ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((ad R L x) ^ ij.2) z⁆ :=
  toEndomorphism_pow_lie x y z n

variable (R)

@[simps!]
def LieSubalgebra.Engel (x : L) : LieSubalgebra R L :=
  { (ad R L x).maximalGeneralizedEigenspace 0 with
    lie_mem' := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Module.End.mem_maximalGeneralizedEigenspace, zero_smul,
        sub_zero, forall_exists_index]
      intro y z m hm n hn
      refine ⟨m + n, ?_⟩
      rw [ad_pow_lie]
      apply Finset.sum_eq_zero
      intro ij hij
      obtain (h|h) : m ≤ ij.1 ∨ n ≤ ij.2 := by rw [Finset.mem_antidiagonal] at hij; omega
      all_goals
        simp only [LinearMap.iterate_apply_eq_zero_of_le h,
          hm, hn, map_zero, zero_lie, lie_zero, smul_zero] }

lemma LieSubalgebra.mem_engel_iff (x y : L) :
    y ∈ Engel R x ↔ ∃ n : ℕ, ((ad R L x) ^ n) y = 0 :=
  (Module.End.mem_maximalGeneralizedEigenspace _ _ _).trans <| by simp only [zero_smul, sub_zero]

lemma LieSubalgebra.self_mem_engel (x : L) : x ∈ Engel R x := by
  simp only [LieSubalgebra.mem_engel_iff]
  exact ⟨1, by simp⟩

example : NegMemClass (Submodule R M) M := by infer_instance

open LieSubalgebra in
@[simp]
lemma normalizer_engel (x : L) : normalizer (Engel R x) = Engel R x := by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (self_mem_engel R x)
  rw [← lie_skew, neg_mem_iff (G := L), mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [mem_engel_iff]
  use n+1
  rw [pow_succ', LinearMap.mul_apply]
  exact hn

variable {R}

open LieSubalgebra in
lemma normalizer_eq_self_of_engel_le [IsArtinian R L]
    (H : LieSubalgebra R L) (x : L) (h : Engel R x ≤ H) :
    normalizer H = H := by
  apply le_antisymm _ (le_normalizer H)
  set N := normalizer H
  calc N.toSubmodule ≤ (Engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : ∀ n ∈ N, ⁅x, n⁆ ∈ H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (self_mem_engel R x))
    rwa [← lie_skew, neg_mem_iff (G := L)] at hn
  have aux₂ : ∀ n ∈ N, ⁅x, n⁆ ∈ N := fun n hn ↦ le_normalizer H (aux₁ _ hn)
  let dx : N →ₗ[R] N := (ad R L x).restrict aux₂
  have := dx.eventually_codisjoint_ker_pow_range_pow
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp this
  specialize hk (k+1) (Nat.le_add_right k 1)
  rw [← Submodule.map_subtype_top N.toSubmodule, Submodule.map_le_iff_le_comap]
  apply hk
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_left
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    simp only [Submodule.mem_comap, mem_engel_iff, mem_coe_submodule]
    use (k+1)
    clear hk; revert hy
    generalize k+1 = k
    induction k generalizing y with
    | zero => cases y; intro hy; simpa using hy
    | succ k ih =>
      intro hy
      rw [pow_succ'] at hy ⊢
      simp only [LinearMap.mem_ker, LinearMap.mul_apply] at hy
      specialize ih hy
      cases y
      simpa only [LinearMap.mul_apply, ad_apply] using ih
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_right
    rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨y, rfl⟩
    cases y
    simp only [pow_succ, LinearMap.mul_apply, Submodule.mem_comap, mem_coe_submodule]
    apply aux₁
    simp only [Submodule.coeSubtype, SetLike.coe_mem]

lemma LieSubmodule.coe_toEndomorphism (N : LieSubmodule R L M) (x : L) (y : N) :
    (toEndomorphism R L N x y : M) = toEndomorphism R L M x y := rfl

lemma LieSubmodule.coe_toEndomorphism_pow (N : LieSubmodule R L M) (x : L) (y : N) (n : ℕ) :
    ((toEndomorphism R L N x ^ n) y : M) = (toEndomorphism R L M x ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', LinearMap.mul_apply, ih, LieSubmodule.coe_toEndomorphism]

lemma LieSubalgebra.coe_ad (H : LieSubalgebra R L) (x y : H) :
    (ad R H x y : L) = ad R L x y := rfl

lemma LieSubalgebra.coe_ad_pow (H : LieSubalgebra R L) (x y : H) (n : ℕ) :
    ((ad R H x ^ n) y : L) = (ad R L x ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', LinearMap.mul_apply, ih, LieSubalgebra.coe_ad]

lemma LieSubalgebra.isNilpotent_of_forall_le_engel [IsNoetherian R L]
    (H : LieSubalgebra R L) (h : ∀ x ∈ H, H ≤ Engel R x) :
    LieAlgebra.IsNilpotent R H := by
  rw [LieAlgebra.isNilpotent_iff_forall]
  intro x
  let K : ℕ →o Submodule R H :=
    ⟨fun n ↦ LinearMap.ker ((ad R H x) ^ n), fun m n hmn ↦ ?mono⟩
  case mono =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    rw [add_comm, pow_add, LinearMap.mul_apply, hy, map_zero]
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance K
  use n
  ext y
  rw [LieSubalgebra.coe_ad_pow]
  specialize h x x.2 y.2
  rw [mem_engel_iff] at h
  obtain ⟨m, hm⟩ := h
  obtain (hmn|hmn) : m ≤ n ∨ n ≤ m := le_total m n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [add_comm, pow_add, LinearMap.mul_apply, hm, map_zero,
      LinearMap.zero_apply, ZeroMemClass.coe_zero]
  · suffices y ∈ K n by
      simpa only [OrderHom.coe_mk, LinearMap.mem_ker, Subtype.ext_iff,
        LieSubalgebra.coe_ad_pow, ZeroMemClass.coe_zero]
    rw [hn m hmn]
    simpa only [OrderHom.coe_mk, LinearMap.mem_ker, Subtype.ext_iff,
      LieSubalgebra.coe_ad_pow, ZeroMemClass.coe_zero]
