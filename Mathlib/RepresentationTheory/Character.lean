/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.RepresentationTheory.FdRep
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Invariants

#align_import representation_theory.character from "leanprover-community/mathlib"@"55b3f8206b8596db8bb1804d8a92814a0b6670c9"

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

A key result is the orthogonality of characters for irreducible representations of finite group
over an algebraically closed field whose characteristic doesn't divide the order of the group. It
is the theorem `char_orthonormal`

# Implementation notes

Irreducible representations are implemented categorically, using the `Simple` class defined in
`Mathlib.CategoryTheory.Simple`

# TODO
* Once we have the monoidal closed structure on `FdRep k G` and a better API for the rigid
structure, `char_dual` and `char_linHom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/


noncomputable section

universe u

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation FiniteDimensional

open scoped BigOperators

variable {k : Type u} [Field k]

namespace FdRep
set_option linter.uppercaseLean3 false -- `fdRep`

section Monoid

variable {G : Type u} [Monoid G]

/-- The character of a representation `V : FdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`. -/
def character (V : FdRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)
#align fdRep.character FdRep.character

def character' (V : FdRep k G) [Fintype G] : MonoidAlgebra k G →ₗ[k] k where
  toFun := fun x ↦ ∑ g, x g * (V.character g)
  map_add' := by
    intros x y
    simp only
    have (g : G) : (x + y) g = x g + y g := by exact rfl
    simp_rw [this]
    have : ∑ g, x g * V.character g + ∑ g, y g * V.character g = ∑ g, (x g * V.character g + y g * V.character g) := by
      simp only [Finset.sum_add_distrib]
    simp_rw [this]
    congr
    funext g
    rw [add_mul]
  map_smul' := by
    intros c x
    simp only
    have (g : G) : (c • x) g = c * x g := by exact rfl
    simp_rw [this]
    have : ∑ g, c * x g * V.character g = c * ∑ g, x g * V.character g := by
      simp only [Finset.mul_sum]
      congr
      funext g
      rw [mul_assoc]
    simp_rw [this]
    congr

theorem char_mul_comm (V : FdRep k G) (g : G) (h : G) : V.character (h * g) = V.character (g * h) :=
  by simp only [trace_mul_comm, character, map_mul]
#align fdRep.char_mul_comm FdRep.char_mul_comm

@[simp]
theorem char_one (V : FdRep k G) : V.character 1 = FiniteDimensional.finrank k V := by
  simp only [character, map_one, trace_one]
#align fdRep.char_one FdRep.char_one

/-- The character is multiplicative under the tensor product. -/
theorem char_tensor (V W : FdRep k G) : (V ⊗ W).character = V.character * W.character := by
  ext g; convert trace_tensorProduct' (V.ρ g) (W.ρ g)
#align fdRep.char_tensor FdRep.char_tensor

-- Porting note: adding variant of `char_tensor` to make the simp-set confluent
@[simp]
theorem char_tensor' (V W : FdRep k G) :
    character (Action.FunctorCategoryEquivalence.inverse.obj
    (Action.FunctorCategoryEquivalence.functor.obj V ⊗
     Action.FunctorCategoryEquivalence.functor.obj W)) = V.character * W.character := by
  simp [← char_tensor]

/-- The character of isomorphic representations is the same. -/
theorem char_iso {V W : FdRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g; simp only [character, FdRep.Iso.conj_ρ i]; exact (trace_conj' (V.ρ g) _).symm
#align fdRep.char_iso FdRep.char_iso

end Monoid

section Group

variable {G : Type u} [Group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
theorem char_conj (V : FdRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]
#align fdRep.char_conj FdRep.char_conj

@[simp]
theorem char_dual (V : FdRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)
#align fdRep.char_dual FdRep.char_dual

@[simp]
theorem char_linHom (V W : FdRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dualTensorIsoLinHom _ _), char_tensor, Pi.mul_apply, char_dual]
#align fdRep.char_lin_hom FdRep.char_linHom

variable [Fintype G] [Invertible (Fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : FdRep k G) :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  erw [← (isProj_averageMap V.ρ).trace] -- Porting note: Changed `rw` to `erw`
  simp [character, GroupAlgebra.average, _root_.map_sum]
#align fdRep.average_char_eq_finrank_invariants FdRep.average_char_eq_finrank_invariants

end Group

namespace MonoidAlgebra

universe u₁ u₂

instance {k : Type u₁} {G : Type u₂} [Semiring k] :
    Coe G (MonoidAlgebra k G) where
  coe g := MonoidAlgebra.single g 1

def std_basis (k : Type u₁) (G : Type u₂) [Semiring k] :
    Basis G k (MonoidAlgebra k G) :=
  .ofRepr (LinearEquiv.refl _ _)

instance my_inst {k : Type u₁} {G : Type u₂} [Semiring k] :
    CoeDep (Type u₂) G (Basis G k (MonoidAlgebra k G)) where
  coe := std_basis k G

instance {k : Type u₁} {G : Type u₂} [Semiring k] :
    Inhabited (Basis G k (MonoidAlgebra k G)) :=
  ⟨std_basis k G⟩

instance {k : Type u₁} {G : Type u₂} [Semiring k] :
    Module.Free k (MonoidAlgebra k G) where
  exists_basis := ⟨G, std_basis k G⟩

end MonoidAlgebra


def is_conj_inv (f : MonoidAlgebra k G →ₗ[k] k) := ∀ g h : G, f (h * g * h⁻¹) = f g

def ClassFuntion := {f : MonoidAlgebra k G →ₗ[k] k // is_conj_inv f}

lemma char_is_class_func (V : FdRep k G) :
    is_conj_inv (Basis.constr (MonoidAlgebra.my_inst.coe : Basis G k (MonoidAlgebra k G)) k V.character) := by
  intro g h
  have foo := Basis.constr_basis G k V.character h
  have (g : G) : B g = MonoidAlgebra.single g 1 := B.repr_self g
  repeat rw [← this]
  sorry

section Orthogonality

variable {G : GroupCat.{u}} [IsAlgClosed k]
variable [Fintype G] [Invertible (Fintype.card G : k)]

-- Move to MonoidAlgebra
namespace MonoidAlgebra

universe u₁ u₂

instance CoeBasisElem {k : Type u₁} {G : Type u₂} [Semiring k] :
    Coe G (MonoidAlgebra k G) where
  coe g := MonoidAlgebra.single g 1

-- fix
@[simp]
theorem CoeBasisElem.mul {k : Type u₁} {G : Type u₂} [Semiring k] [Semigroup G] (a : G) (b : G):
    (↑(a * b) : MonoidAlgebra k G) = ↑a * ↑b := by
  simp only [MonoidAlgebra.single_mul_single, mul_one]

def std_basis (k : Type u₁) (G : Type u₂) [Semiring k] :
    Basis G k (MonoidAlgebra k G) :=
  .ofRepr (LinearEquiv.refl _ _)

-- Check this coercion
instance CoeBasis {k : Type u₁} {G : Type u₂} [Semiring k] :
    CoeDep (Type u₂) G (Basis G k (MonoidAlgebra k G)) where
  coe := std_basis k G

instance {k : Type u₁} {G : Type u₂} [Semiring k] :
    Inhabited (Basis G k (MonoidAlgebra k G)) :=
  ⟨std_basis k G⟩

-- G in Type u₂
instance {k : Type u₁} {G : Type u₁} [Semiring k] :
    Module.Free k (MonoidAlgebra k G) where
  exists_basis := ⟨G, std_basis k G⟩

end MonoidAlgebra


def is_conj_inv (f : MonoidAlgebra k G →ₗ[k] k) := ∀ g h : G, f (h * g * h⁻¹) = f g

def ClassFuntion := {f : MonoidAlgebra k G →ₗ[k] k // is_conj_inv f}

lemma char_is_class_func (V : FdRep k G) :
    is_conj_inv ((MonoidAlgebra.std_basis k G).constr k V.character) := by
  intro g h
  rw [← MonoidAlgebra.CoeBasisElem.mul]
  rw [← MonoidAlgebra.CoeBasisElem.mul]
  have (g : G) :
      (MonoidAlgebra.std_basis k G) g = MonoidAlgebra.single g 1 :=
    (MonoidAlgebra.std_basis k G).repr_self g
  rw [← this]
  rw [← this]
  have (g : G) :=
    (MonoidAlgebra.std_basis k G).constr_basis k V.character g
  rw [this]
  rw [this]
  simp only [char_conj]


-- Use coercion (G -> (MonoidAlgebra.std_basis k G)) for better syntax
/-
lemma char_is_class_func (V : FdRep k G) :
    is_conj_inv (Basis.constr MonoidAlgebra.my_inst.coe k V.character) := by
  intro g h
  have foo := Basis.constr_basis MonoidAlgebra.my_inst.coe k V.character h
  have (g : G) : B g = MonoidAlgebra.single g 1 := B.repr_self g
  repeat rw [← this]
  sorry
-/

open scoped Classical

variable [Fintype G] [Invertible (Fintype.card G : k)]

def IsClassFunction (f : MonoidAlgebra k G →ₗ[k] k) : Prop :=
  ∀ (g h : G), f (MonoidAlgebra.single (h * g * h⁻¹) 1) = f (MonoidAlgebra.single g 1)

def ClassFunction : Type u :=
  { f : MonoidAlgebra k G →ₗ[k] k // IsClassFunction f }

-- def linearLift (f : G → k) : MonoidAlgebra k G →ₗ[k] k where
--   toFun := fun x ↦ ∑ g, f g * x g
--   map_add' := by
--     intros x y
--     sorry
--   map_smul' := sorry

def liftNC (f : k →+ R) (g : G → R) : MonoidAlgebra k G →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g x)).comp f

def linearLiftNC {R : Type*} [Module k R] (f : k →+ R) (g : G → R) : MonoidAlgebra k G →+ R :=
  liftAddHom fun x : G => (AddMonoidHom.mulRight (g x)).comp f

theorem char_isClassFunction (V : FdRep k G) : IsClassFunction (linearLift V.character) := by sorry

/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
theorem char_orthonormal (V W : FdRep k G) [Simple V] [Simple W] :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  -- First, we can rewrite the summand `V.character g * W.character g⁻¹` as the character
  -- of the representation `V ⊗ W* ≅ Hom(W, V)` applied to `g`.
  -- Porting note: Originally `conv in V.character _ * W.character _ =>`
  conv_lhs =>
    enter [2, 2, g]
    rw [mul_comm, ← char_dual, ← Pi.mul_apply, ← char_tensor]
    rw [char_iso (FdRep.dualTensorIsoLinHom W.ρ V)]
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants.
  rw [average_char_eq_finrank_invariants]
  rw [show (of (linHom W.ρ V.ρ)).ρ = linHom W.ρ V.ρ from FdRep.of_ρ (linHom W.ρ V.ρ)]
  -- The space of invariants of `Hom(W, V)` is the subspace of `G`-equivariant linear maps,
  -- `Hom_G(W, V)`.
  erw [(linHom.invariantsEquivFdRepHom W V).finrank_eq] -- Porting note: Changed `rw` to `erw`
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` is `V ≅ W` and `0` otherwise.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
#align fdRep.char_orthonormal FdRep.char_orthonormal

end Orthogonality

end FdRep
