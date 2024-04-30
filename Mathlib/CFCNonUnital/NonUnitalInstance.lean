import Mathlib
import Mathlib.CFCNonUnital.AdjoinSpan
import Mathlib.CFCNonUnital.UnitizationL1Norm

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

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CstarRing A] [CompleteSpace A]
variable [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A]

local postfix:max "⁺¹" => Unitization ℂ
local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

variable (a : A) [ha : IsStarNormal a]

open scoped ContinuousMapZero


---- I think `quasispectrum_eq_spectrum_inr` is stated incorrectly.
---- it should hold for non-unital rings
def homeo : σ ℂ (a : A⁺¹) ≃ₜ σₙ ℂ a :=
  .setCongr <| (Unitization.quasispectrum_eq_spectrum_inr' ℂ ℂ a).symm

def φ₁ : C(σₙ ℂ a, ℂ)₀ →⋆ₙₐ[ℂ] C(σₙ ℂ a, ℂ) := ContinuousMapZero.toContinuousMapHom
def φ₂ : C(σₙ ℂ a, ℂ) ≃⋆ₐ[ℂ] C(σ ℂ (a : A⁺¹), ℂ) := Homeomorph.compStarAlgEquiv' ℂ ℂ <|
      .setCongr <| (Unitization.quasispectrum_eq_spectrum_inr' ℂ ℂ a).symm
noncomputable def φ₃ :  C(σ ℂ (a : A⁺¹), ℂ) →⋆ₐ[ℂ] A⁺¹ := cfcHom (Unitization.instIsStarNormal ℂ a)
noncomputable def φ := ((φ₃ a : C(σ ℂ (a : A⁺¹), ℂ) →⋆ₙₐ[ℂ] A⁺¹).comp (φ₂ a)).comp (φ₁ a)

lemma map_id_φ : φ a (ContinuousMapZero.id rfl) = a := cfcHom_id (Unitization.instIsStarNormal ℂ a)

lemma closedEmbedding_φ : ClosedEmbedding (φ a) := by
  simp only [φ, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_closedEmbedding (Unitization.instIsStarNormal ℂ a)).comp ?_).comp
    ContinuousMapZero.closedEmbedding_toContinuousMapHom
  let e : C(σₙ ℂ a, ℂ) ≃ₜ C(σ ℂ (a : A⁺¹), ℂ) :=
    { (φ₂ a : C(σₙ ℂ a, ℂ) ≃ C(σ ℂ (a : A⁺¹), ℂ)) with
      continuous_toFun := StarAlgEquiv.isometry (φ₂ a) |>.continuous
      continuous_invFun := StarAlgEquiv.isometry (φ₂ a).symm |>.continuous }
  exact e.closedEmbedding

lemma map_spec (f : C(σₙ ℂ a, ℂ)₀) : σ ℂ (φ a f) = Set.range f := by
  rw [φ, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply, φ₃]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (Unitization.instIsStarNormal ℂ a) (R := ℂ) _]
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨homeo a x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(homeo a).symm x, rfl⟩

lemma isStarNormal_φ (f : C(σₙ ℂ a, ℂ)₀) : IsStarNormal (φ a f) :=
  IsStarNormal.map (φ a) (hr := ⟨Commute.all (star f) f⟩)

-- TODO: generalize this
def Unitization.homeomorphProd : Unitization ℂ A ≃ₜ ℂ × A :=
  { Unitization.addEquiv ℂ A with
    continuous_toFun := continuous_induced_dom,
    continuous_invFun := continuous_induced_rng.mpr continuous_id }

lemma mem_range_inr (f : C(σₙ ℂ a, ℂ)₀) :
    φ a f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom ℂ A) := by
  have h₁ := (closedEmbedding_φ a).continuous.range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (s := σₙ ℂ a) rfl) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    apply NonUnitalStarAlgebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, map_id_φ a]
    exact ⟨a, rfl⟩
  · have : Continuous (Unitization.fst (R := ℂ) (A := A)) :=
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
def φ' : C(σₙ ℂ a, ℂ)₀ →⋆ₙₐ[ℂ] NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom ℂ A) :=
  NonUnitalStarAlgHom.codRestrict (φ a) _ (mem_range_inr a)

noncomputable def φ'' : C(σₙ ℂ a, ℂ)₀ →⋆ₙₐ[ℂ] A :=
  NonUnitalStarAlgHomClass.toNonUnitalStarAlgHom (Unitization.inrRangeEquiv ℂ A).symm |>.comp (φ' a)

lemma coe_φ'' (f : C(σₙ ℂ a, ℂ)₀) : φ'' a f = φ a f :=
  congr(Subtype.val $((Unitization.inrRangeEquiv ℂ A).apply_symm_apply ⟨φ a f, mem_range_inr a f⟩))

lemma Unitization.closedEmbedding_inr : ClosedEmbedding (inr : A → A⁺¹) :=
  isometry_inr (𝕜 := ℂ) (A := A) |>.closedEmbedding

instance : NonUnitalContinuousFunctionalCalculus ℂ (IsStarNormal : A → Prop) where
  exists_cfc_of_predicate a ha := by
    refine ⟨φ'' a, ?closedEmbedding, ?map_id, ?map_spec, ?isStarNormal⟩
    case closedEmbedding =>
      apply Unitization.isometry_inr (𝕜 := ℂ) (A := A) |>.closedEmbedding |>.of_comp_iff.mp
      have : Unitization.inr ∘ φ'' a = φ a := by ext1; rw [Function.comp_apply, coe_φ'']
      exact this ▸ closedEmbedding_φ a
    case map_id =>
      apply Unitization.inr_injective (R := ℂ)
      rw [coe_φ'']
      exact map_id_φ a
    case map_spec =>
      intro f
      rw [Unitization.quasispectrum_eq_spectrum_inr' ℂ ℂ, coe_φ'']
      exact map_spec a f
    case isStarNormal =>
      intro f
      rw [← Unitization.isStarNormal_inr (R := ℂ), coe_φ'']
      exact isStarNormal_φ a f
