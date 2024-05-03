import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.NormedSpace.Star.Unitization
import Mathlib.CFCNonUnital.AdjoinSpan
import Mathlib.CFCNonUnital.Restrict
import Mathlib.CFCNonUnital.UnitizationL1Norm
import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus

section MissingTopology -- PR: #12639 https://github.com/leanprover-community/mathlib4/pull/12639

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

section MissingUniformity -- PR: #12639 https://github.com/leanprover-community/mathlib4/pull/12639


variable {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] {g : β → γ} {f : α → β}

theorem UniformInducing.of_comp_iff (hg : UniformInducing g) :
    UniformInducing (g ∘ f) ↔ UniformInducing f := by
  refine ⟨fun h ↦ ?_, hg.comp⟩
  rw [uniformInducing_iff, ← hg.comap_uniformity, Filter.comap_comap, ← h.comap_uniformity,
    Function.comp, Function.comp]

theorem UniformEmbedding.of_comp_iff (hg : UniformEmbedding g) :
    UniformEmbedding (g ∘ f) ↔ UniformEmbedding f := by
  simp_rw [uniformEmbedding_iff, hg.toUniformInducing.of_comp_iff, hg.inj.of_comp_iff f]

end MissingUniformity

section IsStarNormal -- PR: #12641 https://github.com/leanprover-community/mathlib4/pull/12641

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

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [CstarRing A]
variable [CompleteSpace A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [StarModule 𝕜 A] {p : A → Prop} {p₁ : Unitization 𝕜 A → Prop}

local postfix:max "⁺¹" => Unitization 𝕜

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

section CstarAlgebra

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

instance CstarRing.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop) :=
  RCLike.nonUnitalContinuousFunctionalCalculus Unitization.isStarNormal_inr

end CstarAlgebra

section SelfAdjoint

instance IsStarNormal.cfcₙ_map {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Nontrivial R] [TopologicalSpace A]
    [NonUnitalRing A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R p] (a : A) (f : R → R) :
    IsStarNormal (cfcₙ f a) where
  star_comm_self := by
    refine cfcₙ_cases (fun x ↦ Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ ↦ ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a, ← cfcₙ_star, ← cfcₙ_mul .., ← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _



variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]
  [NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop)]

-- this is a duplicate, but if we use `abbrev SpectrumRestricts := QuasispectrumRestricts` then we
-- won't need both versions (if we have the unital-to-non-unital instance)
lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ⟨fun x hx ↦ ?_, Complex.ofReal_re⟩⟩, ?_⟩
  · have := eqOn_of_cfcₙ_eq_cfcₙ <| (cfcₙ_star (id : ℂ → ℂ) a).symm ▸ (cfcₙ_id ℂ a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfcₙ_id ℂ a]
    rw [← cfcₙ_star_id a (R := ℂ)]
    refine cfcₙ_congr fun x hx ↦ ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _

-- duplicate
alias ⟨IsSelfAdjoint.quasispectrumRestricts, _⟩ :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

-- duplicate
/-- A normal element whose `ℂ`-spectrum is contained in `ℝ` is selfadjoint. -/
lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩

instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
    [∀ x : A, CompactSpace (σₙ ℂ x)] :
    NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop) :=
  QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)
    (fun _ _ ↦ inferInstance)

end SelfAdjoint

namespace QuasispectrumRestricts

variable {A : Type*} [NonUnitalRing A]

lemma nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A} :
    QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ σₙ ℝ a, 0 ≤ x := by
  simp_rw [QuasispectrumRestricts.quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℝ, SpectrumRestricts.nnreal_iff]

lemma nnreal_of_nonneg [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    QuasispectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| quasispectrum_nonneg_of_nonneg _ ha

lemma real_iff [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {a : A} :
    QuasispectrumRestricts a Complex.reCLM ↔ ∀ x ∈ σₙ ℂ a, x = x.re := by
  simp_rw [QuasispectrumRestricts.quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℂ, SpectrumRestricts.real_iff]

end QuasispectrumRestricts

section Nonneg

-- if we have the unital-to-non-unital instance, we can remove the unital version
lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A ]
    [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ QuasispectrumRestricts x ContinuousMap.realToNNReal ∧ x * x = a := by
  use cfcₙ Real.sqrt a, cfcₙ_predicate Real.sqrt a
  constructor
  -- that's misnamed, it should be `cfcₙ_map_quasispectrum`
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfc_map_quasispectrum Real.sqrt a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ ↦ Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← cfcₙ_id ℝ a]
    apply cfcₙ_congr fun x hx ↦ ?_
    rw [QuasispectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [← sq, Real.sq_sqrt hx]


variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ (IsSelfAdjoint : A → Prop)]
variable [NonnegSpectrumClass ℝ A] [UniqueNonUnitalContinuousFunctionalCalculus ℝ A]

lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
instance Nonneg.instNonUnitalContinuousFunctionalCalculus [∀ a : A, CompactSpace (σₙ ℝ a)] :
    NonUnitalContinuousFunctionalCalculus ℝ≥0 (fun x : A ↦ 0 ≤ x) :=
  QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    isometry_subtype_coe (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)
    (fun _ _ ↦ inferInstance)

end Nonneg

section SpectralOrder

variable (A : Type*) [NormedRing A] [CompleteSpace A] [StarRing A] [CstarRing A]
variable [NormedAlgebra ℂ A] [StarModule ℂ A]

/-- The partial order on a unital C⋆-algebra defined by `x ≤ y` if and only if `y - x` is
selfadjoint and has nonnegative spectrum.

This is not declared as an instance because one may already have a partial order with better
definitional properties. However, it can be useful to invoke this as an instance in proofs. -/
@[reducible]
def CstarRing.spectralOrder : PartialOrder A where
  le x y := IsSelfAdjoint (y - x) ∧ SpectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, isSelfAdjoint_zero, true_and, forall_const]
    rw [SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← sub_eq_zero]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub x y ▸ hxy.2)
  le_trans x y z hxy hyz :=
    ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

/-- The `CstarRing.spectralOrder` on a unital C⋆-algebra is a `StarOrderedRing`. -/
lemma CstarRing.spectralOrderedRing : @StarOrderedRing A _ (CstarRing.spectralOrder A) _ :=
  let _ := CstarRing.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      · intro h
        obtain ⟨s, hs₁, _, hs₂⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_spectrumRestricts h.1 h.2
        refine ⟨s ^ 2, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
        exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq, sq]⟩
      · rintro ⟨p, hp, rfl⟩
        suffices IsSelfAdjoint p ∧ SpectrumRestricts p ContinuousMap.realToNNReal from
          ⟨by simpa using this.1, by simpa using this.2⟩
        induction hp using AddSubmonoid.closure_induction' with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
          rw [SpectrumRestricts.nnreal_iff]
          exact spectrum_star_mul_self_nonneg
        | one =>
          rw [SpectrumRestricts.nnreal_iff]
          nontriviality A
          simp
        | mul x _ y _ hx hy =>
          exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

end SpectralOrder


section NonnegSpectrumClass

variable {A : Type*} [NonUnitalNormedRing A] [CompleteSpace A]
variable [PartialOrder A] [StarRing A] [StarOrderedRing A] [CstarRing A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

instance CstarRing.instNonnegSpectrumClass' : NonnegSpectrumClass ℝ A where
  quasispectrum_nonneg_of_nonneg a ha := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ ℂ]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CstarRing.spectralOrder (Unitization ℂ A)
    have := CstarRing.spectralOrderedRing (Unitization ℂ A)
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom ℂ A) ha
    rw [AddMonoidHom.map_mclosure, ← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

end NonnegSpectrumClass
