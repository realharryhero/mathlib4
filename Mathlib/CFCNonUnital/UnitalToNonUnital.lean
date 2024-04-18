import Mathlib.Topology.ContinuousFunction.NonUnitalFunctionalCalculus
import Mathlib.CFCNonUnital.ContinuousMapZeroMaterial

section Generic

variable {R A : Type*} {p : A → Prop} [Field R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
variable [Algebra R A] [ContinuousFunctionalCalculus R p]

lemma ContinuousFunctionalCalculus.toNonUnital : NonUnitalContinuousFunctionalCalculus R p where
  exists_cfc_of_predicate a ha := by
    let e := ContinuousMapZero.toContinuousMapHom (X := quasispectrum R a) (R := R)
    let f : C(spectrum R a, quasispectrum R a) :=
      ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
    let ψ := ContinuousMap.compStarAlgHom' R R f
    let ψ' := ((cfcHom ha (R := R) : C(spectrum R a, R) →⋆ₙₐ[R] A).comp
      (ψ : C(quasispectrum R a, R) →⋆ₙₐ[R] C(spectrum R a, R))).comp e
    refine ⟨ψ', ?closedEmbedding, ?map_id, ?map_spectrum, ?predicate⟩
    case closedEmbedding => sorry
    case map_id => exact cfcHom_id ha
    case map_spectrum => sorry
    case predicate => exact fun f ↦ cfcHom_predicate ha _

end Generic
