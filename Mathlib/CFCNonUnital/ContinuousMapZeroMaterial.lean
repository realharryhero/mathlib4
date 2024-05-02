import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Topology.ContinuousFunction.ContinuousMapZero
import Mathlib.Topology.Algebra.Algebra


namespace ContinuousMapZero

section Semiring

variable {X R : Type*} [TopologicalSpace X] [Zero X]
variable [TopologicalSpace R] [CommSemiring R] [TopologicalSemiring R]


@[simps!]
protected def id {s : Set R} [Zero s] (h0 : ((0 : s) : R) = 0) : C(s, R)₀ :=
  ⟨.restrict s (.id R), h0⟩

@[simp]
lemma toContinuousMap_id {s : Set R} [Zero s] (h0 : ((0 : s) : R) = 0) :
    (ContinuousMapZero.id h0 : C(s, R)) = .restrict s (.id R) :=
  rfl

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
@[simp] lemma coe_star [StarRing R] [ContinuousStar R] (f : C(X, R)₀) : ⇑(star f) = star ⇑f := rfl

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

instance instStarModule {X R : Type*} [Zero X] [TopologicalSpace X]
    [CommSemiring R] [StarRing R] [TopologicalSpace R] [TopologicalSemiring R] {M : Type*}
    [SMulZeroClass M R] [ContinuousConstSMul M R] [Star M] [StarModule M R] [ContinuousStar R]:
    StarModule M C(X, R)₀ where
  star_smul r f := ext fun x ↦ star_smul r (f x)

end Semiring

section Ring

variable {X R : Type*} [TopologicalSpace X] [Zero X]
variable [TopologicalSpace R] [CommRing R] [TopologicalRing R]

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

end Ring
