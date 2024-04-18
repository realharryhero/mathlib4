import Mathlib

variable {X R : Type*} [TopologicalSpace X] [Zero X]
variable [TopologicalSpace R] [CommRing R] [TopologicalRing R]

namespace ContinuousMapZero

instance instContinuousMapSMul : SMul C(X, R) C(X, R)₀ where
  smul f g₀ := ⟨f * g₀, by simp⟩

instance instContinuousMapModule : Module C(X, R) C(X, R)₀ :=
  toContinuousMap_injective.module C(X, R)
    ({ toFun := toContinuousMap, map_add' := fun _ _ ↦ rfl, map_zero' := rfl})
    fun _ _ ↦ rfl

lemma smul_coe (f : C(X, R)) (g₀ : C(X, R)₀) : f • (g₀ : C(X, R)) = ↑(f • g₀) := rfl

@[simp] lemma coe_add (f g : C(X, R)₀) : ⇑(f + g) = f + g := rfl
@[simp] lemma coe_mul (f g : C(X, R)₀) : ⇑(f * g) = f * g := rfl
@[simp] lemma coe_zero : ⇑(0 : C(X, R)₀) = 0 := rfl
@[simp] lemma coe_smul (r : R) (f : C(X, R)₀) : ⇑(r • f) = r • f := rfl
@[simp] lemma coe_smul' (g : C(X, R)) (f : C(X, R)₀) : ⇑(g • f) = ⇑g • ⇑f := rfl

-- this is not a continuous linear map in general unless `X` is locally compact. Or is it?
@[simps!]
noncomputable def ofContinuousMap : C(X, R) →ₗ[R] C(X, R)₀ where
  toFun f := ⟨f - algebraMap R C(X, R) (f 0), by simp⟩
  map_add' f g := by ext; simp [sub_add_sub_comm]
  map_smul' r f := by ext; simp [mul_sub]

lemma surjective_ofContinuousMap : Function.Surjective (ofContinuousMap (X := X) (R := R)) :=
  fun f ↦ ⟨f, by ext; simp⟩

-- missing instance!
instance [LocallyCompactSpace X] : TopologicalSemiring C(X, R) := by exact TopologicalSemiring.mk

-- missing `fun_prop` attributes!
attribute [fun_prop] continuous_algebraMap ContinuousMap.continuous_eval_const

-- we don't bundle this above because it requires `X` to be locally compact.
@[fun_prop]
lemma continuous_ofContinuousMap [LocallyCompactSpace X] :
    Continuous (ofContinuousMap (X := X) (R := R)) := by
  simp only [ofContinuousMap, LinearMap.coe_mk, AddHom.coe_mk, continuous_induced_rng,
    Function.comp]
  fun_prop

lemma ofContinuousMap_of_map_zero (f₀ : C(X, R)₀) :
    ofContinuousMap (X := X) (R := R) f₀ = f₀ := by
  ext; simp

lemma ofContinuousMap_of_map_zero' (f : C(X, R)) (hf : f 0 = 0) :
    ofContinuousMap (X := X) (R := R) f = ⟨f, hf⟩ :=
  ofContinuousMap_of_map_zero ⟨f, hf⟩

instance instCanLift : CanLift C(X, R) C(X, R)₀ (↑) (fun f ↦ f 0 = 0) where
  prf f hf := ⟨⟨f, hf⟩, rfl⟩

@[simps]
def toContinuousMapHom [StarRing R] [ContinuousStar R] : C(X, R)₀ →⋆ₙₐ[R] C(X, R) where
  toFun f := f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

lemma closedEmbedding_toContinuousMapHom [T1Space R] [StarRing R] [ContinuousStar R] :
    ClosedEmbedding (toContinuousMapHom (X := X) (R := R)) where
  induced := rfl
  inj f g h := ext fun x ↦ congr($(h) x)
  isClosed_range := by
    convert isClosed_singleton (x := (0 : R)) |>.preimage <|
      ContinuousMap.continuous_eval_const (0 : X)
    ext f
    simp only [Set.mem_range, toContinuousMapHom_apply, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, rfl⟩
      exact map_zero f
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩

@[simps]
def toContinuousMapHomL : C(X, R)₀ →L[C(X, R)] C(X, R) where
  toFun := toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_induced_dom

instance instSMulCommClass' {X R : Type*} [Zero X] [TopologicalSpace X]
    [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R] {M : Type*}
    [SMulZeroClass M R] [SMulCommClass M R R] [ContinuousConstSMul M R] :
    SMulCommClass M C(X, R)₀ C(X, R)₀ where
  smul_comm m f g := ext fun x ↦ smul_comm m (f x) (g x)

instance instIsScalarTower' {X R : Type*} [Zero X] [TopologicalSpace X]
    [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R] {M : Type*}
    [SMulZeroClass M R] [IsScalarTower M R R] [ContinuousConstSMul M R] :
    IsScalarTower M C(X, R)₀ C(X, R)₀ where
  smul_assoc m f g := ext fun x ↦ smul_assoc m (f x) (g x)

@[simp]
lemma StarAlgHom.toFun_eq_coe {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
    [Semiring B] [Algebra R B] [Star B] (f : A →⋆ₐ[R] B) :
    f.toFun = ⇑f :=
  rfl

open Unitization in
noncomputable def unitizationStarAlgEquiv [StarRing R] [ContinuousStar R] :
    Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R) where
  __ := starLift (toContinuousMapHom (X := X) (R := R))
  invFun := fun f ↦ algebraMap R _ (f 0) + (ContinuousMapZero.ofContinuousMap (X := X) (R := R) f)
  left_inv u := by
    ext1
    · rw [fst_add, fst_inr, add_zero, algebraMap_eq_inl, fst_inl, StarAlgHom.toFun_eq_coe]
      simp
    · ext x
      simp [algebraMap_eq_inl]
  right_inv f := by
    ext x
    simp only [StarAlgHom.toFun_eq_coe, starLift_apply_apply]
    simp [algebraMap_eq_inl]
  map_smul' r u := (starLift (toContinuousMapHom (X := X) (R := R))).map_smul r u

open Polynomial

example :
    (fun f : C(R, R) ↦ f - algebraMap R C(R, R) (f 0)) '' ((⊤ : Subalgebra R R[X]).map toContinuousMapAlgHom) ⊆
      NonUnitalAlgebra.adjoin R {(.id R : C(R, R))} := by
  rintro - ⟨-, ⟨p, -, rfl⟩, rfl⟩
  simp only [RingHom.coe_coe, SetLike.mem_coe]
  induction p using Polynomial.induction_on with
  | h_C r =>
    have : Polynomial.toContinuousMap (C r) - (algebraMap R C(R, R)) (eval 0 (C r)) = 0 := by
      ext; simp
    exact this ▸ zero_mem _
  | h_add p q hp hq =>
    simp [add_sub_add_comm]
    exact add_mem hp hq
  | h_monomial n r h =>
    sorry

example :
    ofContinuousMap (X := R) (R := R) '' (Subalgebra.map toContinuousMapAlgHom (⊤ : Subalgebra R R[X])) ⊆
      NonUnitalAlgebra.adjoin R {(⟨.id R, rfl⟩ : C(R, R)₀)} := by
  rintro - ⟨-, ⟨p, -, rfl⟩, rfl⟩
  simp only [RingHom.coe_coe, SetLike.mem_coe]
  induction p using Polynomial.induction_on with
  | h_C r =>
    have : ofContinuousMap (X := R) (R := R) (Polynomial.toContinuousMap (C r)) = 0 := by
      ext; simp
    exact this ▸ zero_mem _
  | h_add p q hp hq => aesop
  | h_monomial n r h =>
    rw [pow_succ', ← mul_assoc, map_mul, ← smul_eq_mul]
    simp only [toContinuousMapAlgHom_apply]
    lift (Polynomial.X.toContinuousMap : C(R, R)) to C(R, R)₀ using (by simp) with foo
    sorry
