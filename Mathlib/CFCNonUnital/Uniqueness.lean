/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.NonUnitalSubalgebra
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus
import Mathlib.Topology.ContinuousFunction.StoneWeierstrass
import Mathlib.CFCNonUnital.NonUnitalInstance
import Mathlib.CFCNonUnital.UnitizationL1Norm
section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜]

open NonUnitalStarAlgebra in
theorem RCLike.uniqueNonUnitalContinuousFunctionalCalculus_of_compactSpace_quasispectrum
    [TopologicalSpace A] [T2Space A] [NonUnitalRing A] [StarRing A] [Module 𝕜 A]
    [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [h : ∀ a : A, CompactSpace (quasispectrum 𝕜 a)] :
    UniqueNonUnitalContinuousFunctionalCalculus 𝕜 A where
  eq_of_continuous_of_map_id s hs _inst h0 φ ψ hφ hψ h := by
    rw [DFunLike.ext'_iff, ← Set.eqOn_univ, ← (ContinuousMapZero.adjoin_id_dense h0).closure_eq]
    refine Set.EqOn.closure (fun f hf ↦ ?_) hφ hψ
    rw [← NonUnitalStarAlgHom.mem_equalizer]
    apply adjoin_le ?_ hf
    rw [Set.singleton_subset_iff]
    exact h
  compactSpace_quasispectrum := h

instance RCLike.instUniqueNonUnitalContinuousFunctionalCalculus [NonUnitalNormedRing A]
    [StarRing A] [CompleteSpace A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] :
    UniqueNonUnitalContinuousFunctionalCalculus 𝕜 A :=
  RCLike.uniqueNonUnitalContinuousFunctionalCalculus_of_compactSpace_quasispectrum

end RCLike
