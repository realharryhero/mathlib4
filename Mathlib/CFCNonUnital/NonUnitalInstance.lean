import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.NormedSpace.Star.Unitization
import Mathlib.CFCNonUnital.AdjoinSpan
import Mathlib.CFCNonUnital.UnitizationL1Norm
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus

section MissingTopology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {g : Y → Z}

theorem Inducing.of_comp_iff (hg : Inducing g) : Inducing (g ∘ f) ↔ Inducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [inducing_iff, hg.induced, induced_compose, h.induced]

theorem Embedding.of_comp_iff (hg : Embedding g) : Embedding (g ∘ f) ↔ Embedding f := by
  simp_rw [embedding_iff, hg.toInducing.of_comp_iff, hg.inj.of_comp_iff f]

theorem ClosedEmbedding.of_comp_iff (hg : ClosedEmbedding g) :
    ClosedEmbedding (g ∘ f) ↔ ClosedEmbedding f := by
  simp_rw [closedEmbedding_iff, hg.toEmbedding.of_comp_iff, Set.range_comp,
    ← hg.closed_iff_image_closed]

end MissingTopology
section IsStarNormal

lemma isStarNormal_iff {R : Type*} [Mul R] [Star R] {x : R} :
    IsStarNormal x ↔ star x * x = x * star x :=
  ⟨fun ⟨h⟩ ↦ h.eq, (⟨·⟩)⟩

lemma Unitization.isStarNormal_inr {R A : Type*} [Semiring R] [AddCommMonoid A]
    [Mul A] [SMulWithZero R A] [StarAddMonoid R] [Star A] {a : A} :
    IsStarNormal (a : Unitization R A) ↔ IsStarNormal a := by
  simp only [isStarNormal_iff, ← inr_star, ← inr_mul, inr_injective.eq_iff]

lemma Unitization.instIsStarNormal (R : Type*) {A : Type*} [Semiring R] [AddCommMonoid A]
    [Mul A] [SMulWithZero R A] [StarAddMonoid R] [Star A] (a : A) [IsStarNormal a] :
    IsStarNormal (a : Unitization R A) :=
  Unitization.isStarNormal_inr.mpr ‹_›

end IsStarNormal

section QuasispectrumCompact

variable {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A]
variable [ProperSpace 𝕜] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

theorem quasispectrum.isCompact (a : A) : IsCompact (quasispectrum 𝕜 a) := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜,
    ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 A)]
  exact spectrum.isCompact _

instance quasispectrum.instCompactSpace (a : A) : CompactSpace (quasispectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| quasispectrum.isCompact a

-- we will need this one, but it can wait.
--instance quasispectrum.instCompactSpaceNNReal {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
   -- (a : A) [CompactSpace (spectrum ℝ a)] : CompactSpace (spectrum NNReal a) := sorry

end QuasispectrumCompact

section ContinuousMapClass

variable {F A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [StarRing A]
  [CstarRing A] [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] [StarRing B] [CstarRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarAlgHomClass F ℂ A B]

-- Analysis.NormedSpace.Star.Spectrum
lemma StarAlgHom.lipschitzWith_one (φ : F) : LipschitzWith 1 φ := by
  simp_rw [lipschitzWith_iff_norm_sub_le, ← map_sub φ, NNReal.coe_one, one_mul]
  exact fun _ _ ↦ norm_apply_le φ _

end ContinuousMapClass

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [CstarRing A]
variable [CompleteSpace A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [StarModule 𝕜 A] {p : A → Prop} {p₁ : Unitization 𝕜 A → Prop}

local postfix:max "⁺¹" => Unitization 𝕜
local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

variable (hp₁ : ∀ {x : A}, p₁ x ↔ p x) (a : A) (ha : p a)
variable [ContinuousFunctionalCalculus 𝕜 p₁]

open scoped ContinuousMapZero


---- I think `quasispectrum_eq_spectrum_inr` is stated incorrectly.
---- it should hold for non-unital rings
def homeo : σ 𝕜 (a : A⁺¹) ≃ₜ σₙ 𝕜 a :=
  .setCongr <| (Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm

def φ₁ : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] C(σₙ 𝕜 a, 𝕜) := ContinuousMapZero.toContinuousMapHom
variable (𝕜) in
def φ₂ : C(σₙ 𝕜 a, 𝕜) ≃⋆ₐ[𝕜] C(σ 𝕜 (a : A⁺¹), 𝕜) := Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <|
  .setCongr <| (Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm
noncomputable def φ₃ :  C(σ 𝕜 (a : A⁺¹), 𝕜) →⋆ₐ[𝕜] A⁺¹ := cfcHom (hp₁.mpr ha)
noncomputable def φ := ((φ₃ hp₁ a ha : C(σ 𝕜 (a : A⁺¹), 𝕜) →⋆ₙₐ[𝕜] A⁺¹).comp (φ₂ 𝕜 a)).comp (φ₁ a)

lemma map_id_φ : φ hp₁ a ha (ContinuousMapZero.id rfl) = a := cfcHom_id (hp₁.mpr ha)

lemma closedEmbedding_φ : ClosedEmbedding (φ hp₁ a ha) := by
  simp only [φ, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_closedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.closedEmbedding_toContinuousMapHom
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    { (φ₂ 𝕜 a : C(σₙ 𝕜 a, 𝕜) ≃ C(σ 𝕜 (a : A⁺¹), 𝕜)) with
      continuous_toFun := ContinuousMap.continuous_comp_left _
      continuous_invFun := ContinuousMap.continuous_comp_left _ }
  exact e.closedEmbedding

lemma map_spec (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (φ hp₁ a ha f) = Set.range f := by
  rw [φ, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply, φ₃]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨homeo a x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(homeo a).symm x, rfl⟩

lemma isStarNormal_φ (f : C(σₙ 𝕜 a, 𝕜)₀) : p₁ (φ hp₁ a ha f) :=
  cfcHom_predicate (hp₁.mpr ha) _

-- TODO: generalize this
def Unitization.homeomorphProd : Unitization 𝕜 A ≃ₜ 𝕜 × A :=
  { Unitization.addEquiv 𝕜 A with
    continuous_toFun := continuous_induced_dom,
    continuous_invFun := continuous_induced_rng.mpr continuous_id }

lemma mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    φ hp₁ a ha f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (closedEmbedding_φ hp₁ a ha).continuous.range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (s := σₙ 𝕜 a) rfl) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    apply NonUnitalStarAlgebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, map_id_φ hp₁ a ha]
    exact ⟨a, rfl⟩
  · have : Continuous (Unitization.fst (R := 𝕜) (A := A)) :=
      Unitization.homeomorphProd.continuous.fst
    simp only [NonUnitalStarAlgHom.coe_range]
    convert IsClosed.preimage this (isClosed_singleton (x := 0))
    aesop

@[simps!]
def Unitization.inrRangeEquiv (R A : Type*) [CommSemiring R] [StarAddMonoid R]
    [NonUnitalSemiring A] [Star A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] :
    A ≃⋆ₐ[R] NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A) :=
  StarAlgEquiv.ofLeftInverse' (snd_inr R)

noncomputable
def φ' : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) :=
  NonUnitalStarAlgHom.codRestrict (φ hp₁ a ha) _ (mem_range_inr hp₁ a ha)

noncomputable def φ'' : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A :=
  NonUnitalStarAlgHomClass.toNonUnitalStarAlgHom (Unitization.inrRangeEquiv 𝕜 A).symm |>.comp (φ' hp₁ a ha)

lemma coe_φ'' (f : C(σₙ 𝕜 a, 𝕜)₀) : φ'' hp₁ a ha f = φ hp₁ a ha f :=
  congr(Subtype.val $((Unitization.inrRangeEquiv 𝕜 A).apply_symm_apply ⟨φ hp₁ a ha f, mem_range_inr hp₁ a ha f⟩))

lemma Unitization.closedEmbedding_inr : ClosedEmbedding (inr : A → A⁺¹) :=
  isometry_inr (𝕜 := 𝕜) (A := A) |>.closedEmbedding

theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 (p : A → Prop) where
  exists_cfc_of_predicate a ha := by
    refine ⟨φ'' hp₁ a ha, ?closedEmbedding, ?map_id, ?map_spec, ?isStarNormal⟩
    case closedEmbedding =>
      apply Unitization.isometry_inr (𝕜 := 𝕜) (A := A) |>.closedEmbedding |>.of_comp_iff.mp
      have : Unitization.inr ∘ φ'' hp₁ a ha = φ hp₁ a ha := by
        ext1; rw [Function.comp_apply, coe_φ'']
      exact this ▸ closedEmbedding_φ hp₁ a ha
    case map_id =>
      apply Unitization.inr_injective (R := 𝕜)
      rw [coe_φ'']
      exact map_id_φ hp₁ a ha
    case map_spec =>
      intro f
      rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜, coe_φ'']
      exact map_spec hp₁ a ha f
    case isStarNormal =>
      intro f
      rw [← hp₁, coe_φ'']
      exact isStarNormal_φ hp₁ a ha f

end RCLike

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

instance CstarRing.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop) :=
  RCLike.nonUnitalContinuousFunctionalCalculus Unitization.isStarNormal_inr
