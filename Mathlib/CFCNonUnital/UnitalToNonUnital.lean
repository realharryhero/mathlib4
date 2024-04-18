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
    case map_spectrum =>
      intro f
      simp only [ψ']
      rw [quasispectrum_eq_spectrum_union_zero]
      simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
        NonUnitalStarAlgHom.coe_coe]
      rw [cfcHom_map_spectrum ha]
      ext x
      constructor
      · rintro (⟨x, rfl⟩ | rfl)
        · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩, rfl⟩
        · exact ⟨0, map_zero f⟩
      · rintro ⟨x, rfl⟩
        have hx := x.2
        simp_rw [quasispectrum_eq_spectrum_union_zero R a] at hx
        obtain (hx | hx) := hx
        · exact Or.inl ⟨⟨x.1, hx⟩, rfl⟩
        · apply Or.inr
          simp only [Set.mem_singleton_iff] at hx ⊢
          rw [show x = 0 from Subtype.val_injective hx, map_zero]
    case predicate => exact fun f ↦ cfcHom_predicate ha _

end Generic
