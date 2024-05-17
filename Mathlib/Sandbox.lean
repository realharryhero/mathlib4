import Mathlib.Analysis.BoxIntegral.Integrability
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section BoxIntegral

open BigOperators

namespace BoxIntegral

variable {ι : Type*} {I : Box ι} (f : (ι → ℝ) → ℝ) (π : Prepartition I)

def Prepartition.taggedMax : TaggedPrepartition I where
  boxes := π.boxes
  le_of_mem' := π.le_of_mem'
  pairwiseDisjoint := π.pairwiseDisjoint
  tag :=
    let e := f
    sorry
  tag_mem_Icc := sorry

def Prepartition.taggedMin : TaggedPrepartition I where
  boxes := π.boxes
  le_of_mem' := π.le_of_mem'
  pairwiseDisjoint := π.pairwiseDisjoint
  tag :=
    let e := f
    sorry
  tag_mem_Icc := sorry

theorem Prepartition.taggedMax_isHenstock :
    (π.taggedMax f).IsHenstock := sorry

theorem Prepartition.taggedMin_isHenstock :
    (π.taggedMin f).IsHenstock := sorry

theorem Prepartition.taggedMax_isPartition (hπ : π.IsPartition) :
    (π.taggedMax f).IsPartition := hπ

theorem Prepartition.taggedMin_isPartition (hπ : π.IsPartition) :
    (π.taggedMin f).IsPartition := hπ

variable [Fintype ι] {r : (ι → ℝ) → Set.Ioi (0 : ℝ)}
    (hπ : ∀ J x, J ∈ π.boxes → Metric.diam (Box.Icc J) ≤ 2 * r x)

def Prepartition.diam : ℝ := by
  let π := π
  sorry

theorem Prepartition.diam_le_diam {J : Box ι} (hJ : J ∈ π.boxes) :
    Metric.diam (Box.Icc J) ≤ π.diam := sorry

variable (τ : TaggedPrepartition I) (vol : BoxIntegral.BoxAdditiveMap ι (ℝ →L[ℝ] ℝ) ⊤)

def _root_.BoxIntegral.TaggedPrepartition.taggedMax : TaggedPrepartition I :=
  τ.toPrepartition.taggedMax f

def _root_.BoxIntegral.TaggedPrepartition.taggedMin : TaggedPrepartition I :=
  τ.toPrepartition.taggedMin f

namespace riemann

variable (hτ : τ.IsHenstock)

theorem TaggedPrepartition.tag_le_taggedMax {J : Box ι} (hJ : J ∈ τ.boxes) :
    f (τ.tag J) ≤ f ((τ.taggedMax f).tag J) := sorry

theorem TaggedPrepartition.taggedMin_le_tag {J : Box ι} (hJ : J ∈ τ.boxes) :
    f ((τ.taggedMin f).tag J) ≤ f (τ.tag J) := sorry

theorem TaggedPrepartition.taggedMin_le_taggedMax {J : Box ι} (hJ : J ∈ τ.boxes) :
    f ((τ.taggedMin f).tag J) ≤ f ((τ.taggedMax f).tag J) := sorry

def rconst {r : ℝ} (hr : 0 < r) : NNReal → ((ι → ℝ) → Set.Ioi (0 : ℝ)) := fun _ ↦ fun  _ ↦ ⟨r, hr⟩

variable {τ} in
/-- τ must be Riemann type. -/
theorem TaggedPrepartition.IsSubordinate_iff {r : ℝ} {c : NNReal} (hr : 0 < r) :
    τ.IsSubordinate (rconst hr c) ↔ τ.diam ≤ 2 * r := sorry

variable (π' : Prepartition I)

theorem integralSum_taggedMax_monotone (h : π' ≤ π) :
    integralSum f vol (π'.taggedMax f) ≤ integralSum f vol (π.taggedMax f) := sorry

theorem integralSum_taggedMin_antitone (h : π' ≤ π) :
    integralSum f vol (π.taggedMin f) ≤ integralSum f vol (π'.taggedMin f) := sorry

theorem integralSum_taggedMin_le_taggedMax :
    integralSum f vol (π.taggedMin f) ≤ integralSum f vol (π'.taggedMax f) := sorry

theorem le_integralSum_taggedMax :
    integralSum f vol τ ≤ integralSum f vol (τ.taggedMax f) := sorry

theorem integralSum_taggedMin_le :
    integralSum f vol (τ.taggedMin f) ≤ integralSum f vol τ := sorry

theorem integralSum_le_infPrepartition_taggedMax :
    integralSum f vol τ ≤ integralSum f vol ((π.taggedMax f).infPrepartition τ.toPrepartition) := sorry

theorem integralSum_infPrepartition_taggedMin_le :
    integralSum f vol ((π.taggedMin f).infPrepartition τ.toPrepartition) ≤ integralSum f vol τ := sorry

variable (I) in
def integralSumSup : ℝ := ⨅ π : Prepartition I, (integralSum f vol (π.taggedMax f))

variable (I) in
def integralSumInf : ℝ := ⨆ π : Prepartition I, (integralSum f vol (π.taggedMin f))

theorem le_integralSumInf :
    integralSum f vol (π.taggedMin f) ≤ integralSumInf I f vol := sorry

theorem integralSumSup_le :
    integralSumSup I f vol ≤ integralSum f vol (π.taggedMax f) := sorry

def δ : Set.Ioi (0 :ℝ) → Set.Ioi (0 : ℝ) := sorry

def rconstδ {ε : ℝ} (hε : 0 < ε) : NNReal → ((ι → ℝ) → Set.Ioi (0 : ℝ)) := rconst (δ ⟨ε, hε⟩).prop

theorem noname {ε : ℝ} (hε : 0 < ε) (hπ : π.diam ≤ 2 * δ ⟨ε, hε⟩) :
    - ε ≤ integralSum f vol (π.taggedMin f) - integralSumInf I f vol ∧
      integralSum f vol (π.taggedMax f) - integralSumSup I f vol ≤ ε := sorry

variable {τ} in
theorem noname' {ε : ℝ} (hε : 0 < ε) (c : NNReal)
    (hτ : IntegrationParams.Riemann.MemBaseSet I c (rconstδ hε c) τ)
    (h : integralSumInf I f vol = integralSumSup I f vol) :
    |integralSum f vol τ - integralSumInf I f vol| ≤ ε := by
  have : τ.IsSubordinate (rconstδ hε c) := hτ.isSubordinate
  have := (TaggedPrepartition.IsSubordinate_iff ((δ _).prop)).mp this
  have main := noname f τ.toPrepartition vol hε this
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_trans main.1 ?_
    gcongr
    exact integralSum_taggedMin_le _ _ _
  · rw [h]
    refine le_trans ?_ main.2
    gcongr
    exact le_integralSum_taggedMax _ _ _

/-- This is the main result. -/
theorem integrable_of_sumInf_eq_sumSup (h : integralSumInf I f vol = integralSumSup I f vol) :
    Integrable I IntegrationParams.Riemann f vol := by
  rw [integrable_iff_cauchy_basis]
  intro ε hε
  refine ⟨rconstδ (half_pos hε), fun _ _ ↦ congr_fun rfl, fun c₁ c₂ τ₁ τ₂ h₁ h₁' h₂ h₂' ↦
    (dist_triangle _ (integralSumInf I f vol) _).trans ?_⟩
  rw [show ε = ε / 2 + ε / 2 by norm_num]
  gcongr
  · exact noname' f vol (half_pos hε) _ h₁ h
  · rw [dist_comm]
    exact noname' f vol (half_pos hε) _ h₂ h






open Filter Topology

variable {π : ℕ → Prepartition I} (hπ : Tendsto (fun n ↦
  integralSum f vol ((π n).taggedMax f) - integralSum f vol ((π n).taggedMin f)) atTop (𝓝 0))

example : Integrable I IntegrationParams.Riemann f vol := by
  rw [integrable_iff_cauchy_basis]
  intro ε hε
  refine ⟨rconst hε, ?_, ?_⟩
  · intro _
    exact integrationParams_RCond
  · intro c₁ c₂ τ₁ τ₂ h₁ h₁' h₂ h₂'
    have := eventually_lt_of_tendsto_lt hε hπ
    rw [eventually_atTop] at this
    obtain ⟨n, hn⟩ := this
    simp only [dist, ge_iff_le, abs_le]
    have t1 := integralSum_infPrepartition_taggedMin_le f (π n) τ₁ vol
    have t2 := integralSum_le_infPrepartition_taggedMax f (π n) τ₂ vol

    let τ₁_min := ((π n).taggedMin f).infPrepartition τ₁.toPrepartition
    let τ₂_max := ((π n).taggedMax f).infPrepartition τ₂.toPrepartition


  --  refine (le_trans (dist_triangle4 _ (integralSum f vol π₁_min) (integralSum f vol π₂_max) _)) ?_



end riemann

end BoxIntegral

#exit

noncomputable section oscillation

open BoxIntegral Topology ENNReal EMetric

variable {E F : Type*} [TopologicalSpace E] (f : E → F) (x : E) (α : ℝ≥0∞)

def oscillation [PseudoEMetricSpace F] : ENNReal := ⨅ S ∈ (𝓝 x).map f, diam S

local notation "ω(" f ", " x ")" => oscillation f x

variable {f x α} in
theorem oscillation_lt_iff [PseudoEMetricSpace F] :
    ω(f, x) < α ↔ ∃ s : Set E, IsOpen s ∧ x ∈ s ∧ diam (f '' s) < α := by
  simp_rw [oscillation, Filter.mem_map, _root_.mem_nhds_iff, iInf_exists, iInf_lt_iff,
    exists_prop, exists_and_right]
  refine ⟨fun ⟨s, ⟨t, ht₁, ht₂, ht₃⟩, hs⟩ ↦ ?_, fun ⟨t, ht₁, ht₂, ht₃⟩ ↦ ?_⟩
  · exact ⟨t, ht₂, ht₃, lt_of_le_of_lt (diam_mono (Set.image_subset_iff.mpr ht₁)) hs⟩
  · exact ⟨f '' t, ⟨t, Set.subset_preimage_image f t, ht₁, ht₂⟩, ht₃⟩

theorem subset_oscillation_lt [PseudoEMetricSpace F] {s : Set E} (hs₁ : IsOpen s)
    (hs₂ : diam (f '' s) < α) :
    s ⊆ {x | ω(f, x) < α} := fun _ h ↦ oscillation_lt_iff.mpr ⟨s, hs₁, h, hs₂⟩

theorem isOpen_oscillation_lt [PseudoEMetricSpace F] :
    IsOpen {x | ω(f, x) < α} := by
  refine isOpen_iff_forall_mem_open.mpr fun _ h ↦ ?_
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := oscillation_lt_iff.mp h
  exact ⟨s, subset_oscillation_lt f α hs₁ hs₃, hs₁, hs₂⟩

theorem oscillation_eq_zero_of_continuousAt [PseudoEMetricSpace F] (h : ContinuousAt f x) :
    ω(f, x) = 0 := by
  apply le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (zero_le _)
  rw [zero_add]
  have : ball (f x) (ε / 2) ∈ (𝓝 x).map f := h <| ball_mem_nhds _ (by simp [ne_of_gt hε])
  apply (biInf_le diam this).trans (le_of_le_of_eq diam_ball ?_)
  apply (ENNReal.mul_div_cancel' ?_ ?_) <;> norm_num

theorem continousAt_of_oscillation_eq_zero [MetricSpace F] (h : ω(f, x) = 0) :
    ContinuousAt f x := by
  simp_rw [← ENNReal.bot_eq_zero, oscillation, iInf_eq_bot, iInf_lt_iff, Filter.mem_map] at h
  refine Metric.continuousAt_iff'.mpr fun ε hε ↦ ?_
  obtain ⟨s, hs₁, hs₂⟩ := h (ENNReal.ofReal ε) (ofReal_pos.mpr hε)
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨f⁻¹' s, hs₁, fun _ hy ↦ edist_lt_ofReal.mp <| lt_of_le_of_lt ?_ hs₂⟩
  exact edist_le_diam_of_mem hy (by convert mem_of_mem_nhds hs₁)

variable {f x} in
/-- The oscillation of `f` at `x` is `0` iff `f` is continuous at `x`. -/
theorem oscillation_eq_zero_iff [MetricSpace F] :
    ω(f, x) = 0 ↔ ContinuousAt f x :=
  ⟨continousAt_of_oscillation_eq_zero _ _, oscillation_eq_zero_of_continuousAt _ _⟩

#exit

variable {ι : Type*} {E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The oscillation of `f` at `x`. -/
noncomputable def oscillation (f : (ι → ℝ) → E) (x : ι → ℝ) : ENNReal :=
  ⨅ S ∈ (𝓝 x).map f, diam S

/-- The oscillation of `f` at `x` is 0 whenever `f` is continuous at `x`. -/
lemma oscillation_zero_of_continuousAt (f : (ι → ℝ) → E) (x : ι → ℝ) (hf : ContinuousAt f x) :
    oscillation f x = 0 := by
  apply le_antisymm (ENNReal.le_of_forall_pos_le_add ?_) (zero_le _)
  intro ε hε _
  rw [zero_add]
  have : ball (f x) (ε / 2) ∈ (𝓝 x).map f := hf <| ball_mem_nhds _ (by simp [ne_of_gt hε])
  apply (biInf_le diam this).trans (le_of_le_of_eq diam_ball ?_)
  apply (ENNReal.mul_div_cancel' ?_ ?_) <;> norm_num

-- Used in the proof of Lebesgue-Vitali
-- See proof at https://en.wikipedia.org/wiki/Riemann_integral#Integrability
def X (f : (ι → ℝ) → E) (I : Box ι) (ε : ENNReal) :=
  { x | oscillation f x ≥ ε } ∩ (Box.Icc I)

lemma isCompact_X (f : (ι → ℝ) → E) (I : Box ι) (ε : ENNReal) : IsCompact (X f I ε) := by
  apply I.isCompact_Icc.of_isClosed_subset (IsClosed.inter ?_ I.isCompact_Icc.isClosed) (by simp)
  rw [isClosed_iff_clusterPt]
  intro a ha
  rw [Set.mem_setOf_eq]
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  obtain ⟨U, hU, U_open, aU⟩ := _root_.mem_nhds_iff.1 hS
  apply le_trans ?_ (diam_mono (Set.image_subset_iff.2 hU))
  rw [clusterPt_iff] at ha
  obtain ⟨b, bU, hb⟩ := ha (U_open.mem_nhds aU) (Filter.mem_principal_self _)
  apply (Set.mem_setOf.1 hb).trans (biInf_le diam ?_)
  exact (𝓝 b).mem_of_superset (U_open.mem_nhds bU) (Set.subset_preimage_image f U)

end oscillation


#exit



open BigOperators

namespace BoxIntegral

variable {ι : Type*} {I : Box ι} (π : Prepartition I) {f : (ι → ℝ) → ℝ} (hf : )

def TaggedPrepartitionOfSup : TaggedPrepartition I where
  boxes := π.boxes
  le_of_mem' := π.le_of_mem'
  pairwiseDisjoint := π.pairwiseDisjoint
  tag := by
    intro J
    let a := IsCompact.exists_isMinOn (Box.isCompact_Icc J) sorry
  tag_mem_Icc := by
    intro J
    dsimp
    exact?

variable (I)

def isStepFunction : Prop :=
  ∃ (s : Finset (Box ι)) (t : Box ι → ℝ),
    (∀ J ∈ s, J ≤ I) ∧ f = ∑ J ∈ s, Set.indicator J (fun _ ↦ t J)

structure stepFunction where
  toFun : (ι → ℝ) → ℝ
  isStepFunction : isStepFunction I toFun

def TaggedPrepartition.stepFunction : stepFunction I where
  toFun := ∑ J ∈ π.boxes, Set.indicator J (fun _ ↦ f (π.tag J))
  isStepFunction := ⟨π.boxes, f ∘ π.tag, π.le_of_mem', rfl⟩
