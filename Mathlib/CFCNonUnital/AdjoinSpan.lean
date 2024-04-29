import Mathlib

open Submodule

namespace Submonoid

variable {M : Type*} [Monoid M]

/-- The `Submonoid.closure` of a set is `1` union the its `Subsemigroup.closure`. -/
lemma closure_eq_one_union (s : Set M) :
    closure s = {(1 : M)} ∪ (Subsemigroup.closure s : Set M) := by
  apply le_antisymm
  · intro x hx
    induction hx using closure_induction' with
    | mem x hx => exact Or.inr <| Subsemigroup.subset_closure hx
    | one => exact Or.inl <| by simp
    | mul x hx y hy hx hy =>
      simp only [Set.singleton_union, Set.mem_insert_iff, SetLike.mem_coe] at hx hy
      obtain ⟨(rfl | hx), (rfl | hy)⟩ := And.intro hx hy
      all_goals simp_all
      exact Or.inr <| mul_mem hx hy
  · rintro x (hx | hx)
    · exact (show x = 1 by simpa using hx) ▸ one_mem (closure s)
    · induction hx using Subsemigroup.closure_induction' with
      | mem x hx => exact subset_closure hx
      | mul x _ y _ hx hy => exact mul_mem hx hy

end Submonoid

namespace Submodule

variable {S R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [SetLike S M] [AddSubmonoidClass S M] [SMulMemClass S R M]

lemma coe_span_eq_self (s : S) : (span R (s : Set M) : Set M) = s := by
  refine le_antisymm ?_ subset_span
  let s' : Submodule R M :=
    { carrier := s
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := SMulMemClass.smul_mem }
  exact span_le (p := s') |>.mpr le_rfl

end Submodule

namespace NonUnitalAlgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

-- This is the version we should actually have as `NonUnitalAlgebra.adjoin_induction'`, but
-- currently that is used for the subtype.
/-- A dependent version of `NonUnitalAlgebra.adjoin_induction`. -/
theorem adjoin_induction'' {s : Set A} {p : ∀ x, x ∈ adjoin R s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_adjoin R h))
    (Hadd : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›))
    (H0 : p 0 (zero_mem _))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem ‹_› ‹_›))
    (Hsmul : ∀ (r : R) (x hx), p x hx → p (r • x) (SMulMemClass.smul_mem _ ‹_›))
    {a} (ha : a ∈ adjoin R s) : p a ha :=
  adjoin_induction' ⟨a, ha⟩ (p := fun x ↦ p x.1 x.2) Hs (fun x y ↦ Hadd x.1 x.2 y.1 y.2)
    H0 (fun x y ↦ Hmul x.1 x.2 y.1 y.2) (fun r x ↦ Hsmul r x.1 x.2)

open Submodule

lemma adjoin_eq (s : NonUnitalSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R)

lemma adjoin_eq_span (s : Set A) : (adjoin R s).toSubmodule = span R (Subsemigroup.closure s) := by
  apply le_antisymm
  · intro x hx
    induction hx using adjoin_induction'' with
    | Hs x hx => exact subset_span <| Subsemigroup.subset_closure hx
    | Hadd x _ y _ hpx hpy => exact add_mem hpx hpy
    | H0 => exact zero_mem _
    | Hmul x _ y _ hpx hpy =>
      apply span_induction₂ hpx hpy ?Hs (by simp) (by simp) ?Hadd_l ?Hadd_r ?Hsmul_l ?Hsmul_r
      case Hs => exact fun x hx y hy ↦ subset_span <| mul_mem hx hy
      case Hadd_l => exact fun x y z hxz hyz ↦ by simpa [add_mul] using add_mem hxz hyz
      case Hadd_r => exact fun x y z hxz hyz ↦ by simpa [mul_add] using add_mem hxz hyz
      case Hsmul_l => exact fun r x y hxy ↦ by simpa [smul_mul_assoc] using smul_mem _ _ hxy
      case Hsmul_r => exact fun r x y hxy ↦ by simpa [mul_smul_comm] using smul_mem _ _ hxy
    | Hsmul r x _ hpx => exact smul_mem _ _ hpx
  · apply span_le.2 _
    show Subsemigroup.closure s ≤ (adjoin R s).toNonUnitalSubsemiring.toSubsemigroup
    exact Subsemigroup.closure_le.2 (subset_adjoin R)

end NonUnitalAlgebra

namespace Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

lemma adjoin_nonUnitalSubalgebra_eq_span_union (s : NonUnitalSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)) = span R ({1} ∪ s) := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union, span_union,
    ← span_span (R := R) (s := (Subsemigroup.closure (s : Set A) : Set A)),
    ← NonUnitalAlgebra.adjoin_eq_span, NonUnitalAlgebra.adjoin_eq,
    NonUnitalSubalgebra.coe_toSubmodule]

lemma adjoin_nonUnitalSubalgebra_eq_span (s : NonUnitalSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)) = span R {1} ⊔ s.toSubmodule := by
  rw [adjoin_eq_span, Submonoid.closure_eq_one_union, span_union, ← NonUnitalAlgebra.adjoin_eq_span,
      NonUnitalAlgebra.adjoin_eq]

end Algebra

namespace NonUnitalStarAlgebra

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [StarRing R] [StarRing A] [StarModule R A]

open scoped Pointwise
open Submodule

lemma adjoin_eq (s : NonUnitalStarSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))

lemma adjoin_eq_span (s : Set A) :
    (adjoin R s).toSubmodule = span R (Subsemigroup.closure (s ∪ star s)) := by
  rw [adjoin_toNonUnitalSubalgebra, NonUnitalAlgebra.adjoin_eq_span]

@[simp]
lemma span_eq_toSubmodule (s : NonUnitalStarSubalgebra R A) :
    span R (s : Set A) = s.toSubmodule := by
  rw [SetLike.ext'_iff, coe_span_eq_self]
  simp

lemma adjoin_induction' {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarRing R] [StarRing A] [StarModule R A]
    {s : Set A} {p : ∀ x, x ∈ adjoin R s → Prop} {a : A} (ha : a ∈ adjoin R s)
    (mem : ∀ (x : A) (hx : x ∈ s), p x (subset_adjoin R s hx))
    (add : ∀ x hx y hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (zero : p 0 (zero_mem _))
    (mul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (smul : ∀ (r : R) x hx, p x hx → p (r • x) (SMulMemClass.smul_mem r hx))
    (star : ∀ x hx, p x hx → p (star x) (star_mem hx)) : p a ha :=
  sorry -- I'm lazy, and why don't we have this?

end NonUnitalStarAlgebra

namespace StarSubalgebra

open Submodule StarAlgebra

variable {R A : Type*} [CommSemiring R] [StarRing R]
variable [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

lemma adjoin_eq (s : StarSubalgebra R A) : adjoin R (s : Set A) = s :=
  le_antisymm (adjoin_le le_rfl) (subset_adjoin R (s : Set A))

lemma adjoin_eq_span (s : Set A) :
    Subalgebra.toSubmodule (adjoin R s).toSubalgebra = span R (Submonoid.closure (s ∪ star s)) := by
  rw [adjoin_toSubalgebra, Algebra.adjoin_eq_span]

lemma adjoin_nonUnitalStarSubalgebra_eq_span (s : NonUnitalStarSubalgebra R A) :
    Subalgebra.toSubmodule (adjoin R (s : Set A)).toSubalgebra = span R ({1} ∪ s) := by
  rw [adjoin_toSubalgebra, StarMemClass.star_coe_eq, Set.union_self,
    ← s.coe_toNonUnitalSubalgebra, Algebra.adjoin_nonUnitalSubalgebra_eq_span,
    ← Submodule.span_eq s.toSubmodule, span_union]
  simp

lemma nonUnitalStarAlgebra_adjoin_le_adjoin_toNonUnitalStarSubalgebra (s : Set A) :
    NonUnitalStarAlgebra.adjoin R s ≤ (adjoin R s).toNonUnitalStarSubalgebra :=
  NonUnitalStarAlgebra.adjoin_le <| subset_adjoin R s

lemma adjoin_nonUnitalStarSubalgebra_adjoin (s : Set A) :
    adjoin R (NonUnitalStarAlgebra.adjoin R s : Set A) = adjoin R s := by
  apply le_antisymm
  · apply adjoin_le
    -- need a lemma here
    change NonUnitalStarAlgebra.adjoin R s ≤ (adjoin R s).toNonUnitalStarSubalgebra
    exact NonUnitalStarAlgebra.adjoin_le <| subset_adjoin R s
  · exact adjoin_le <| (NonUnitalStarAlgebra.subset_adjoin R s).trans <| subset_adjoin R _


end StarSubalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
variable [TopologicalSpace R] [TopologicalSemiring R]
variable {X : Type*} [TopologicalSpace X] {𝕜 : Type*} [RCLike 𝕜]

-- annoying, things break below without this.
instance : IsScalarTower 𝕜 C(X, 𝕜) C(X, 𝕜) := @IsScalarTower.right _ C(X, 𝕜) _ _ _
instance : SMulCommClass 𝕜 C(X, 𝕜) C(X, 𝕜) := @Algebra.to_smulCommClass _ C(X, 𝕜) _ _ _

lemma Set.SeparatesPoints_monotone {α β : Type*} {s t : Set (α → β)}
    (h : s.SeparatesPoints) (h_sub : s ⊆ t) : t.SeparatesPoints := by
  peel h with x y hxy f _
  exact And.imp_left (@h_sub f) this

open NonUnitalStarAlgebra in
lemma foo (s : Set 𝕜) : Set.SeparatesPoints ((⇑) '' (adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} : Set C(s, 𝕜))) :=
  fun _ _ h ↦
    ⟨_, ⟨.restrict s (.id 𝕜), self_mem_adjoin_singleton 𝕜 _, rfl⟩, Subtype.val_injective.ne h ⟩

open NonUnitalAlgebra in
lemma bar (s : Set 𝕜) : Set.SeparatesPoints ((⇑) '' (adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} : Set C(s, 𝕜))) :=
  fun _ _ h ↦
    ⟨_, ⟨.restrict s (.id 𝕜), self_mem_adjoin_singleton 𝕜 _, rfl⟩, Subtype.val_injective.ne h ⟩

def ContinuousMap.evalAlgHom {X : Type*} (R : Type*) [TopologicalSpace X] [CommSemiring R]
    [TopologicalSpace R] [TopologicalSemiring R] (x : X) : C(X, R) →ₐ[R] R where
  toFun := λ f => f x
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  commutes' := fun _ => rfl

@[simps]
def ContinuousMap.evalStarAlgHom {X : Type*} (R : Type*) [TopologicalSpace X] [CommSemiring R]
    [TopologicalSpace R] [TopologicalSemiring R] [StarRing R] [ContinuousStar R] (x : X) :
    C(X, R) →⋆ₐ[R] R where
  toFun := λ f => f x
  map_zero' := rfl
  map_one' := rfl
  map_add' := fun _ _ => rfl
  map_mul' := fun _ _ => rfl
  commutes' := fun _ => rfl
  map_star' := fun _ => rfl

open NonUnitalStarAlgebra Submodule in
lemma ContinuousMap.adjoin_id_eq_span_one_union (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      span 𝕜 ({(1 : C(s, 𝕜))} ∪ (adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))})) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, ← StarSubalgebra.adjoin_nonUnitalStarSubalgebra_adjoin,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarSubalgebra.adjoin_nonUnitalStarSubalgebra_eq_span]

open NonUnitalStarAlgebra Submodule Pointwise in
lemma ContinuousMap.adjoin_id_eq_span_one_union' (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) + (adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} : Set C(s, 𝕜)) := by
  ext x
  rw [SetLike.mem_coe, ← StarSubalgebra.adjoin_nonUnitalStarSubalgebra_adjoin,
    ← StarSubalgebra.mem_toSubalgebra, ← Subalgebra.mem_toSubmodule,
    StarSubalgebra.adjoin_nonUnitalStarSubalgebra_eq_span, span_union, mem_sup, span_eq_toSubmodule]
  simp [Set.mem_add]

open NonUnitalStarAlgebra in
lemma ContinuousMap.mem_ker_evalStarAlgHom_of_mem_nonUnitalStarAlgebraAdjoin_id
    {s : Set 𝕜} (h0 : 0 ∈ s) {f : C(s, 𝕜)} (hf : f ∈ adjoin 𝕜 {.restrict s (.id 𝕜)}) :
    f ∈ RingHom.ker (evalStarAlgHom 𝕜 (⟨0, h0⟩ : s)) := by
  induction hf using NonUnitalStarAlgebra.adjoin_induction' with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f _ g _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f _ g _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [RingHom.mem_ker] at hf ⊢
    rw [map_smul, hf, smul_zero]
  | star f _ hf =>
    rw [RingHom.mem_ker] at hf ⊢
    rw [map_star, hf, star_zero]

open NonUnitalStarAlgebra Submodule in
lemma ContinuousMap.ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 ∈ s) :
    (StarAlgebra.adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} : Set C(s, 𝕜)) ∩
      RingHom.ker (evalStarAlgHom 𝕜 (⟨0, h0⟩ : s)) =
        adjoin 𝕜 {(.restrict s (.id 𝕜) : C(s, 𝕜))} := by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_union', Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := mem_ker_evalStarAlgHom_of_mem_nonUnitalStarAlgebraAdjoin_id h0 hf
    rw [RingHom.mem_ker, evalStarAlgHom_apply] at hf₂ this
    rw [add_apply, this, add_zero, smul_apply, one_apply, smul_eq_mul, mul_one] at hf₂
    rwa [hf₂, zero_smul, zero_add]
  · simp only [Set.mem_inter_iff, SetLike.mem_coe]
    refine fun hf ↦ ⟨?_, mem_ker_evalStarAlgHom_of_mem_nonUnitalStarAlgebraAdjoin_id h0 hf⟩
    exact StarSubalgebra.nonUnitalStarAlgebra_adjoin_le_adjoin_toNonUnitalStarSubalgebra _ hf
