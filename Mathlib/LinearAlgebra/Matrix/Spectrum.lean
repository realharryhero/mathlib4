/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Hermitian

#align_import linear_algebra.matrix.spectrum from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/


namespace Matrix

variable {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n]

variable {A : Matrix n n 𝕜}

open scoped BigOperators

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]

variable (hA : A.IsHermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `Fin (Fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) → ℝ :=
  (isHermitian_iff_isSymmetric.1 hA).eigenvalues finrank_euclideanSpace
#align matrix.is_hermitian.eigenvalues₀ Matrix.IsHermitian.eigenvalues₀

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i
#align matrix.is_hermitian.eigenvalues Matrix.IsHermitian.eigenvalues

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))
#align matrix.is_hermitian.eigenvector_basis Matrix.IsHermitian.eigenvectorBasis

-- I knew this should be easy to prove
lemma mulVec_eigenvectorBasis (j : n) :
    A *ᵥ (hA.eigenvectorBasis j) = hA.eigenvalues j • hA.eigenvectorBasis j := by
  have := (isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis finrank_euclideanSpace
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)
  rw [IsROrC.real_smul_eq_coe_smul (K := 𝕜)]
  convert this using 2
  all_goals rw [eigenvectorBasis, OrthonormalBasis.reindex_apply]

/- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
--noncomputable def eigenvectorMatrix : Matrix n n 𝕜 :=
--  (PiLp.basisFun _ 𝕜 n).toMatrix (eigenvectorBasis hA).toBasis

/--Find out the right kind of docstring for this!-/
noncomputable def eigenvectorUnitary {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    Matrix.unitaryGroup n 𝕜 :=
    ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (eigenvectorBasis hA).toBasis,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
    (EuclideanSpace.basisFun n 𝕜) (eigenvectorBasis hA)⟩
#align matrix.is_hermitian.eigenvector_matrix Matrix.IsHermitian.eigenvectorUnitary

lemma eigenvectorUnitary_coe {𝕜 : Type*} [IsROrC 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    hA.eigenvectorUnitary =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis :=
  rfl

theorem eigenvectorUnitary_apply (i j : n) :
    (hA.eigenvectorUnitary : Matrix n n 𝕜) i j = hA.eigenvectorBasis j i := by
  simp [eigenvectorUnitary, Basis.toMatrix_apply]
#align matrix.is_hermitian.eigenvector_matrix_apply Matrix.IsHermitian.eigenvectorUnitary_apply

theorem eigenvectorUnitary_mulVec (j : n) :
    (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ Pi.single j 1 = hA.eigenvectorBasis j := by
  ext i
  simp [eigenvectorUnitary_apply]

theorem star_eigenvectorUnitary_mulVec (j : n) :
    star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ hA.eigenvectorBasis j = Pi.single j 1 := by
  simpa only [mulVec_mulVec, unitary.coe_star_mul_self, one_mulVec] using
    congr(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ
      $((hA.eigenvectorUnitary_mulVec j).symm))

lemma spectral_theorem' :
    diagonal ((↑) ∘ hA.eigenvalues) = (star hA.eigenvectorUnitary : Matrix n n 𝕜) * A *
      (hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  apply Matrix.toLin'.injective
  apply Pi.basisFun 𝕜 n |>.ext fun j ↦ ?_
  simp only [Pi.basisFun_apply, Matrix.toLin'_apply, LinearMap.coe_stdBasis]
  rw [← mulVec_mulVec, ← mulVec_mulVec, hA.eigenvectorUnitary_mulVec, hA.mulVec_eigenvectorBasis,
    mulVec_smul, hA.star_eigenvectorUnitary_mulVec, diagonal_mulVec_single, ← Pi.single_smul]
  congr! 1
  simp [Function.comp_apply, IsROrC.real_smul_eq_coe_smul (K := 𝕜)]

lemma spectral_theorem'' :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * diagonal ((↑) ∘ hA.eigenvalues) *
      (star hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  apply Matrix.toLin'.injective
  apply hA.eigenvectorBasis.toBasis |>.ext fun j ↦ ?_
  simp only [OrthonormalBasis.coe_toBasis, toLin'_mul, LinearMap.coe_comp, Function.comp_apply,
    toLin'_apply]
  erw [toLin'_apply, toLin'_apply] -- this is because we're abusing defeq of `EuclideanSpace 𝕜 n` with `n → 𝕜`.
  rw [hA.star_eigenvectorUnitary_mulVec j, diagonal_mulVec_single, ← smul_eq_mul, Pi.single_smul,
    mulVec_smul, hA.eigenvectorUnitary_mulVec, hA.mulVec_eigenvectorBasis, Function.comp_apply,
    IsROrC.real_smul_eq_coe_smul (K := 𝕜)]
#exit

open LinearMap in
@[simp]
theorem _root_.LinearMap.adjoint_id {𝕜 E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    adjoint (.id (R := 𝕜) (M := E)) = .id :=
  Eq.symm <| (eq_adjoint_iff _ _).mpr fun _ _ => rfl

@[simp]
theorem _root_.Matrix.unitaryGroup.inv_coe_eq_star (U : Matrix.unitaryGroup n 𝕜) :
    (U⁻¹ : Matrix n n 𝕜) = (star U : Matrix n n 𝕜) := by
  rw [← unitary.coe_star, unitary.star_eq_inv, ← unitary.val_inv_toUnits_apply, coe_units_inv,
    unitary.val_toUnits_apply]

lemma star_coe_eigenvectorUnitary :
    (star hA.eigenvectorUnitary : Matrix n n 𝕜) =
      (eigenvectorBasis hA).toBasis.toMatrix (EuclideanSpace.basisFun n 𝕜).toBasis := by
  rw [eigenvectorUnitary_coe, star_eq_conjTranspose, ← LinearMap.toMatrix_id_eq_basis_toMatrix,
    ← LinearMap.toMatrix_adjoint]
  simp

/-- The columns of `Matrix.IsHermitian.eigenvectorUnitary` form the basis-/
theorem transpose_eigenvectorUnitary_apply (i : n) :
    hA.eigenvectorUnitaryᵀ i = hA.eigenvectorBasis i :=
  funext fun j => eigenvectorUnitary_apply hA j i

/-- **Diagonalization theorem**, **spectral theorem** for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`. -/
theorem spectral_theorem :
    (star hA.eigenvectorUnitary : Matrix n n 𝕜) * A =
      diagonal ((↑) ∘ hA.eigenvalues) * (star hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  rw [star_coe_eigenvectorUnitary, EuclideanSpace.basisFun_toBasis,
    PiLp.basis_toMatrix_basisFun_mul]
  ext i j
  have := isHermitian_iff_isSymmetric.1 hA
  convert this.eigenvectorBasis_apply_self_apply finrank_euclideanSpace (EuclideanSpace.single j 1)
    ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) using 1
  · dsimp only [EuclideanSpace.single, toEuclideanLin_piLp_equiv_symm, toLin'_apply,
      Matrix.of_apply, IsHermitian.eigenvectorBasis]
    simp_rw [mulVec_single, mul_one, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_reindex]
    rfl
  · simp only [diagonal_mul, (· ∘ ·), eigenvalues]
    rw [eigenvectorBasis, Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_reindex, eigenvalues₀, PiLp.basisFun_apply, WithLp.equiv_symm_single]
#align matrix.is_hermitian.spectral_theorem Matrix.IsHermitian.spectral_theorem

theorem eigenvalues_eq (i : n) :
    hA.eigenvalues i =
      IsROrC.re (star (hA.eigenvectorUnitaryᵀ i) ⬝ᵥ A *ᵥ hA.eigenvectorUnitaryᵀ i) := by
  have := congr($(hA.spectral_theorem) * hA.eigenvectorUnitary)
  simp only [mul_assoc, SetLike.coe_mem, unitary.star_mul_self_of_mem, mul_one] at this
  have := congr_arg IsROrC.re (congr_fun (congr_fun this i) i) |>.symm
  rwa [diagonal_apply_eq, Function.comp_apply, IsROrC.ofReal_re, star_eq_conjTranspose,
    ← mul_assoc, mul_mul_apply] at this
#align matrix.is_hermitian.eigenvalues_eq Matrix.IsHermitian.eigenvalues_eq

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  apply mul_left_cancel₀ <| det_ne_zero_of_left_inverse <|
    unitary.coe_mul_star_self hA.eigenvectorUnitary
  rw [unitary.coe_star, ← det_mul, spectral_theorem, det_mul, mul_comm, det_diagonal]
  simp_rw [Function.comp_apply]
#align matrix.is_hermitian.det_eq_prod_eigenvalues Matrix.IsHermitian.det_eq_prod_eigenvalues

/-- *spectral theorem* (Alternate form for convenience) A hermitian matrix can be can be
replaced by a diagonal matrix sandwiched between the eigenvector matrices. This alternate form
allows direct rewriting of A since: <| A = V D V⁻¹$ -/
lemma spectral_theorem' :
    A = (hA.eigenvectorUnitary : Matrix n n 𝕜) * diagonal ((↑) ∘ hA.eigenvalues) *
      (star hA.eigenvectorUnitary : Matrix n n 𝕜) := by
  simpa [← mul_assoc] using congr((hA.eigenvectorUnitary : Matrix n n 𝕜) * $(hA.spectral_theorem))

/-- rank of a hermitian matrix is the rank of after diagonalization by the eigenvector matrix -/
lemma rank_eq_rank_diagonal : A.rank = (Matrix.diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem']
  have h := by simpa using
    isUnit_iff_isUnit_det _ |>.mp <| (unitary.toUnits hA.eigenvectorUnitary).isUnit
  have h' := by simpa [← det_conjTranspose, ← star_eq_conjTranspose] using h.star
  simp only [rank_mul_eq_right_of_isUnit_det _ _ h, rank_mul_eq_left_of_isUnit_det _ _ h',
    rank_diagonal, Function.comp_apply, ne_eq, algebraMap.lift_map_eq_zero_iff]

/-- rank of a hermitian matrix is the number of nonzero eigenvalues of the hermitian matrix -/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]

/-- The entries of `eigenvectorBasis` are eigenvectors. -/
lemma mulVec_eigenvectorBasis (i : n) :
    A *ᵥ hA.eigenvectorBasis i = hA.eigenvalues i • hA.eigenvectorBasis i := by
  have := congr($(hA.spectral_theorem') * hA.eigenvectorUnitary)
  ext1 j
  simpa [mul_assoc, mul_diagonal, eigenvectorUnitary_apply, mul_comm, IsROrC.real_smul_eq_coe_mul]
    using congr_fun (congr_fun this j) i

end DecidableEq

/-- A nonzero Hermitian matrix has an eigenvector with nonzero eigenvalue. -/
lemma exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A ≠ 0) :
    ∃ (v : n → 𝕜) (t : ℝ), t ≠ 0 ∧ v ≠ 0 ∧ A *ᵥ v = t • v := by
  classical
  have : hA.eigenvalues ≠ 0 := by
    contrapose! h_ne
    have := hA.spectral_theorem'
    rwa [h_ne, Pi.comp_zero, IsROrC.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ ↦ 0),
      diagonal_zero, mul_zero, zero_mul] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  exact ⟨_, _, hi, hA.eigenvectorBasis.orthonormal.ne_zero i, hA.mulVec_eigenvectorBasis i⟩

end IsHermitian

end Matrix
