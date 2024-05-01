import Mathlib.Algebra.Algebra.Quasispectrum

lemma mem_quasispectrum_iff {R A : Type*} [Semifield R] [Ring A]
    [Algebra R A] {a : A} {x : R} :
    x ∈ quasispectrum R a ↔ x = 0 ∨ x ∈ spectrum R a := by
  simp [quasispectrum_eq_spectrum_union_zero]

/-! ### Restriction of the spectrum -/

/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebraMap R S`, and `f` is a right inverse of `algebraMap R S` on `spectrum S a`.
For example, when `f = Complex.re` (so `S := ℂ` and `R := ℝ`), `SpectrumRestricts a f` means that
the `ℂ`-spectrum of `a` is contained within `ℝ`. This arises naturally when `a` is selfadjoint
and `A` is a C⋆-algebra.
This is the property allows us to restrict a continuous functional calculus over `S` to a
continuous functional calculus over `R`. -/
structure QuasispectrumRestricts
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) : Prop where
  /-- `f` is a right inverse of `algebraMap R S` when restricted to `quasispectrum S a`. -/
  rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
  /-- `f` is a left inverse of `algebraMap R S`. -/
  left_inv : Function.LeftInverse f (algebraMap R S)

@[simp]
theorem quasispectrum.algebraMap_mem_iff (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ quasispectrum S a ↔ r ∈ quasispectrum R a := by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

@[simp]
theorem quasispectrum.preimage_algebraMap (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' quasispectrum S a = quasispectrum R a :=
  Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

namespace QuasispectrumRestricts

section NonUnital

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
  [Algebra R S] [IsScalarTower R S A] [SMulCommClass R S A]

theorem of_subset_range_algebraMap (a : A) (f : S → R) (hf : f.LeftInverse (algebraMap R S))
    (h : quasispectrum S a ⊆ Set.range (algebraMap R S)) : QuasispectrumRestricts a f where
  rightInvOn := fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf

variable [IsScalarTower R S A] {a : A} {f : S → R} (h : QuasispectrumRestricts a f)

theorem algebraMap_image : algebraMap R S '' quasispectrum R a = quasispectrum S a := by
  refine' Set.eq_of_subset_of_subset _ fun s hs => ⟨f s, _⟩
  simpa only [quasispectrum.preimage_algebraMap] using
    (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

theorem image : f '' quasispectrum S a = quasispectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

theorem apply_mem {s : S} (hs : s ∈ quasispectrum S a) : f s ∈ quasispectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩

theorem subset_preimage : quasispectrum S a ⊆ f ⁻¹' quasispectrum R a :=
  h.image ▸ (quasispectrum S a).subset_preimage_image f

lemma of_quasispectrum_eq {a b : A} {f : S → R} (ha : QuasispectrumRestricts a f)
    (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f where
  rightInvOn := h ▸ ha.rightInvOn
  left_inv := ha.left_inv

protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
    [NonUnitalRing A] [Module R₁ A] [Module R₂ A] [Module R₃ A] [Algebra R₁ R₂] [Algebra R₂ R₃]
    [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃] [IsScalarTower R₂ R₃ A] [IsScalarTower R₃ A A]
    [SMulCommClass R₃ A A] {a : A} {f : R₃ → R₂} {g : R₂ → R₁} {e : R₃ → R₁} (hfge : g ∘ f = e)
    (hf : QuasispectrumRestricts a f) (hg : QuasispectrumRestricts a g) :
    QuasispectrumRestricts a e where
  left_inv := by
    convert hfge ▸ hf.left_inv.comp hg.left_inv
    congrm(⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ ↦ hf.apply_mem
    congrm(⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))

end NonUnital

end QuasispectrumRestricts
