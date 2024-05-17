/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import Mathlib.Algebra.Function.Indicator
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Set.Finite

#align_import data.finsupp.defs from "leanprover-community/mathlib"@"842328d9df7e96fd90fc424e115679c15fb23a71"

/-!
# Type of functions with finite support

For any type `α` and any type `M` with zero, we define the type `Finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `MonoidAlgebra R M` and `AddMonoidAlgebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `AddMonoidAlgebra`s, hence they use
  `Finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `LinearIndependent`) is defined as a map
  `Finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `Multiset α ≃+ α →₀ ℕ`;
* `FreeAbelianGroup α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `Finsupp` elements, which is defined in
`Algebra/BigOperators/Finsupp`.

-- Porting note: the semireducibility remark no longer applies in Lean 4, afaict.
Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `MonoidAlgebra`, `AddMonoidAlgebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `Finsupp`: The type of finitely supported functions from `α` to `β`.
* `Finsupp.single`: The `Finsupp` which is nonzero in exactly one point.
* `Finsupp.update`: Changes one value of a `Finsupp`.
* `Finsupp.erase`: Replaces one value of a `Finsupp` by `0`.
* `Finsupp.onFinset`: The restriction of a function to a `Finset` as a `Finsupp`.
* `Finsupp.mapRange`: Composition of a `ZeroHom` with a `Finsupp`.
* `Finsupp.embDomain`: Maps the domain of a `Finsupp` by an embedding.
* `Finsupp.zipWith`: Postcomposition of two `Finsupp`s with a function `f` such that `f 0 0 = 0`.

## Notations

This file adds `α →₀ M` as a global notation for `Finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `Finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `Zero` or `(Add)(Comm)Monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## TODO

* Expand the list of definitions and important lemmas to the module docstring.

-/


open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

/-- A function `α → M` with finite support, with notation `α →₀ M`.

Note that `Finsupp.support` is the preferred API for accessing the support of the function,
`Finsupp.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure Finsupp (α : Type*) (M : Type*) [Zero M] where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `Finsupp`). -/
  toFun : α → M
  /-- The support of a dependent function with finite support (aka `Finsupp`). -/
  support' : Trunc { s : Multiset α // ∀ a, a ∈ s ∨ toFun a = 0 }
#align finsupp Finsupp
#align finsupp.on_finset Finsupp.mk'
#align finsupp.to_fun Finsupp.toFun

@[inherit_doc]
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `Finsupp` -/


section Basic

variable [DecidableEq α] [Zero M]

instance instFunLike : FunLike (α →₀ M) α M :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    apply Subsingleton.elim ⟩
#align finsupp.fun_like Finsupp.instFunLike

/-- Helper instance for when there are too many metavariables to apply the `DFunLike` instance
directly. -/
instance instCoeFun : CoeFun (α →₀ M) fun _ => α → M :=
  inferInstance
#align finsupp.has_coe_to_fun Finsupp.instCoeFun

@[simp]
theorem toFun_eq_coe (f : α →₀ M) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h
#align finsupp.ext Finsupp.ext

@[deprecated DFunLike.ext_iff]
theorem ext_iff {f g : α →₀ M} : f = g ↔ ∀ a, f a = g a :=
  DFunLike.ext_iff
#align finsupp.ext_iff Finsupp.ext_iff

lemma ne_iff {f g : α →₀ M} : f ≠ g ↔ ∃ a, f a ≠ g a := DFunLike.ne_iff

@[deprecated DFunLike.coe_fn_eq]
theorem coeFn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
  DFunLike.coe_fn_eq
#align finsupp.coe_fn_inj Finsupp.coeFn_inj

@[deprecated DFunLike.coe_injective]
theorem coeFn_injective : @Function.Injective (α →₀ M) (α → M) (⇑) :=
  DFunLike.coe_injective
#align finsupp.coe_fn_injective Finsupp.coeFn_injective

@[deprecated DFunLike.congr_fun]
theorem congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
  DFunLike.congr_fun h _
#align finsupp.congr_fun Finsupp.congr_fun

@[simp, norm_cast]
theorem coe_mk' (f : α → M) (s) : ⇑(⟨f, s⟩ : α →₀ M) = f :=
  rfl
#align finsupp.coe_mk Finsupp.coe_mk'
#align finsupp.on_finset_apply Finsupp.coe_mk'

instance instZero : Zero (α →₀ M) :=
  ⟨⟨0, Trunc.mk <| ⟨∅, fun _ => Or.inr rfl⟩⟩⟩
#align finsupp.has_zero Finsupp.instZero

@[simp, norm_cast] lemma coe_zero : ⇑(0 : α →₀ M) = 0 := rfl
#align finsupp.coe_zero Finsupp.coe_zero

theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl
#align finsupp.zero_apply Finsupp.zero_apply

instance instInhabited : Inhabited (α →₀ M) :=
  ⟨0⟩
#align finsupp.inhabited Finsupp.instInhabited

@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]
#align finsupp.coe_eq_zero Finsupp.coe_eq_zero

/-- Given `Fintype α`, `equivFunOnFintype` is the `Equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype α] : (α →₀ M) ≃ (α → M) where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl
  right_inv _ := rfl
#align finsupp.equiv_fun_on_finite Finsupp.equivFunOnFintype
#align finsupp.equiv_fun_on_finite_apply Finsupp.equivFunOnFintype_apply

@[simp]
theorem equivFunOnFintype_symm_coe {α} [Fintype α] (f : α →₀ M) : equivFunOnFintype.symm f = f :=
  equivFunOnFintype.symm_apply_apply f
#align finsupp.equiv_fun_on_finite_symm_coe Finsupp.equivFunOnFintype_symm_coe

/--
If `α` has a unique term, the type of finitely supported functions `α →₀ β` is equivalent to `β`.
-/
@[simps! apply symm_apply_toFun]
def _root_.Equiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFintype.trans (Equiv.funUnique ι M)
#align equiv.finsupp_unique Equiv.finsuppUnique
#align equiv.finsupp_unique_symm_apply_to_fun Equiv.finsuppUnique_symm_apply_toFun
#align equiv.finsupp_unique_apply Equiv.finsuppUnique_apply

@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by rwa [Unique.eq_default a]
#align finsupp.unique_ext Finsupp.unique_ext

theorem unique_ext_iff [Unique α] {f g : α →₀ M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩
#align finsupp.unique_ext_iff Finsupp.unique_ext_iff

/-- Create an element of `α →₀ M` from a finset `s` and a function `x`
defined on this `Finset`. -/
def mk (s : Finset α) (x : (↑s : Set α) → M) : α →₀ M :=
  ⟨fun a => if H : a ∈ s then x ⟨a, H⟩ else 0,
    Trunc.mk ⟨s.1, fun a => if H : a ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩
#align finsupp.mk Finsupp.mk

variable {s : Finset α} {x : (↑s : Set α) → M} {a : α}

@[simp]
theorem mk_apply : (mk s x : α → M) a = if H : a ∈ s then x ⟨a, H⟩ else 0 :=
  rfl

theorem mk_of_mem (ha : a ∈ s) : (mk s x : α → M) a = x ⟨a, ha⟩ :=
  dif_pos ha

theorem mk_of_not_mem (hi : a ∉ s) : (mk s x : α → M) a = 0 :=
  dif_neg hi

theorem mk_injective (s : Finset α) : Function.Injective (@mk α M _ _ s) := by
  intro x y H
  ext i
  have h1 : (mk s x : α → M) i = (mk s y : α → M) i := by rw [H]
  obtain ⟨i, hi : i ∈ s⟩ := i
  dsimp only [mk_apply, Subtype.coe_mk] at h1
  simpa only [dif_pos hi] using h1

end Basic

/-! ### Declarations about `support` -/


section SupportBasic

variable [DecidableEq α] [Zero M] [(x : M) → Decidable (x ≠ 0)]

/-- Set `{ a | f a ≠ 0 }` as a `Finset`. -/
def support (f : α →₀ M) : Finset α :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun a => f a ≠ 0) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩
#align finsupp.support Finsupp.support

@[simp]
theorem support_mk_subset {s : Finset α} {x : (↑s : Set α) → M} : (mk s x).support ⊆ s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]
theorem support_mk'_subset {f : α → M} {s : Multiset α} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1
#align finsupp.support_on_finset_subset Finsupp.support_mk'_subset

@[local simp]
theorem mem_support_toFun (f : α →₀ M) (a) : a ∈ f.support ↔ f a ≠ 0 := by
  cases' f with f s
  induction' s using Trunc.induction_on with s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  exact and_iff_right_of_imp (s.prop a).resolve_right
#align finsupp.mem_support_to_fun Finsupp.mem_support_toFun

theorem eq_mk_support (f : α →₀ M) : f = mk f.support fun i => f i := by aesop

/-- Equivalence between dependent functions with finite support `s : Finset α` and functions
`s → { x : M // x ≠ 0 }`. -/
@[simps]
def subtypeSupportEqEquiv (s : Finset α) :
    { f : α →₀ M // f.support = s } ≃ (s → { x : M // x ≠ 0 }) where
  toFun | ⟨f, hf⟩ => fun ⟨a, ha⟩ ↦ ⟨f a, (f.mem_support_toFun a).1 <| hf.symm ▸ ha⟩
  invFun f := ⟨mk s fun a ↦ (f a).1, Finset.ext fun a ↦ by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      a ∈ support (mk s fun i ↦ (f i).1) ↔ ∃ h : a ∈ s, (f ⟨a, h⟩).1 ≠ 0 := by simp
      _ ↔ ∃ _ : a ∈ s, True := exists_congr fun h ↦ (iff_true _).mpr (f _).2
      _ ↔ a ∈ s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    ext1
    simp [Subtype.eta]

/-- Equivalence between all dependent finitely supported functions `f : α →₀ M` and type
of pairs `⟨s : Finset α, f : s → { x : M // x ≠ 0 }⟩`. -/
@[simps! apply_fst apply_snd_coe]
def sigmaFinsetFunEquiv : (α →₀ M) ≃ Σ s : Finset α, s → { x : M // x ≠ 0 } :=
  (Equiv.sigmaFiberEquiv Finsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]
theorem support_zero : (0 : α →₀ M).support = ∅ :=
  rfl
#align finsupp.support_zero Finsupp.support_zero

@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.support ↔ f a ≠ 0 :=
  @(f.mem_support_toFun)
#align finsupp.mem_support_iff Finsupp.mem_support_iff

@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.support f = f.support :=
  Set.ext fun _x => mem_support_iff.symm
#align finsupp.fun_support_eq Finsupp.fun_support_eq

theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm
#align finsupp.not_mem_support_iff Finsupp.not_mem_support_iff

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.support = g.support ∧ ∀ x ∈ f.support, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a => by
      exact if h : a ∈ f.support then h₂ a h else by
        have hf : f a = 0 := not_mem_support_iff.1 h
        have hg : g a = 0 := by rwa [h₁, not_mem_support_iff] at h
        rw [hf, hg]⟩
#align finsupp.ext_iff' Finsupp.ext_iff'

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.support = ∅ ↔ f = 0 :=
  mod_cast @Function.support_eq_empty_iff _ _ _ f
#align finsupp.support_eq_empty Finsupp.support_eq_empty

theorem support_nonempty_iff {f : α →₀ M} : f.support.Nonempty ↔ f ≠ 0 := by
  simp only [Finsupp.support_eq_empty, Finset.nonempty_iff_ne_empty, Ne]
#align finsupp.support_nonempty_iff Finsupp.support_nonempty_iff

#align finsupp.nonzero_iff_exists Finsupp.ne_iff

theorem card_support_eq_zero {f : α →₀ M} : card f.support = 0 ↔ f = 0 := by simp
#align finsupp.card_support_eq_zero Finsupp.card_support_eq_zero

theorem finite_support (f : α →₀ M) : Set.Finite (Function.support f) :=
  f.fun_support_eq.symm ▸ f.support.finite_toSet
#align finsupp.finite_support Finsupp.finite_support

theorem support_subset_iff {s : Set α} {f : α →₀ M} :
    ↑f.support ⊆ s ↔ ∀ a ∉ s, f a = 0 := by
  simp only [Set.subset_def, mem_coe, mem_support_iff]; exact forall_congr' fun a => not_imp_comm
#align finsupp.support_subset_iff Finsupp.support_subset_iff

theorem support_mk' (f : α → M) (s : Multiset α) (h) :
    (mk' f <| Trunc.mk ⟨s, h⟩).support = s.toFinset.filter fun a => f a ≠ 0 :=
  rfl
#align finsupp.support_on_finset Finsupp.support_mk'

theorem mem_support_mk' {f : α → M} {s : Multiset α} {h} {a : α} :
    a ∈ (mk' f <| Trunc.mk ⟨s, h⟩).support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.coe_mk']
#align finsupp.mem_support_on_finset Finsupp.mem_support_mk'

end SupportBasic

instance instDecidableEq [DecidableEq α] [Zero M] [DecidableEq M] : DecidableEq (α →₀ M) :=
  fun f g =>
    decidable_of_iff (f.support = g.support ∧ ∀ a ∈ f.support, f a = g a) ext_iff'.symm
#align finsupp.decidable_eq Finsupp.instDecidableEq

/-! ### Declarations about `single` -/


section Single

variable [DecidableEq α] [Zero M] [(x : M) → Decidable (x ≠ 0)] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function with value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M :=
  ⟨Pi.single a b,
    Trunc.mk
      ⟨{a}, fun a' => (Decidable.eq_or_ne a' a).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩
#align finsupp.single Finsupp.single

theorem single_eq_pi_single {a b} : ⇑(single a b : α →₀ M) = Pi.single a b :=
  rfl
#align finsupp.single_eq_pi_single Finsupp.single_eq_pi_single

theorem single_apply : single a b a' = if a = a' then b else 0 := by
  rw [single_eq_pi_single, Pi.single, Function.update]
  simp [@eq_comm _ a a']
#align finsupp.single_apply Finsupp.single_apply

theorem single_eq_set_indicator : ⇑(single a b) = Set.indicator {a} fun _ => b := by
  ext
  simp [single_apply, Set.indicator, @eq_comm _ a]
#align finsupp.single_eq_set_indicator Finsupp.single_eq_set_indicator

theorem single_apply_left [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x z : α)
    (y : M) : single (f x) y (f z) = single x y z := by
  simp only [single_apply, hf.eq_iff]
#align finsupp.single_apply_left Finsupp.single_apply_left

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b := by
  exact Pi.single_eq_same (f := fun _ ↦ M) a b
#align finsupp.single_eq_same Finsupp.single_eq_same

@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 := by
  exact Pi.single_eq_of_ne' h _
#align finsupp.single_eq_of_ne Finsupp.single_eq_of_ne

theorem single_eq_update (a : α) (b : M) : ⇑(single a b) = Function.update (0 : _) a b :=
  by rw [single_eq_set_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]
#align finsupp.single_eq_update Finsupp.single_eq_update


@[simp]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  DFunLike.coe_injective <| by
    simpa only [single_eq_update, coe_zero] using Function.update_eq_self a (0 : α → M)
#align finsupp.single_zero Finsupp.single_zero

theorem single_of_single_apply (a a' : α) (b : M) :
    single a ((single a' b) a) = single a' (single a' b) a := by
  rw [single_apply, single_apply]
  ext
  split_ifs with h
  · rw [h]
  · rw [zero_apply, single_apply, ite_self]
#align finsupp.single_of_single_apply Finsupp.single_of_single_apply

theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).support = {a} := by
  ext a'; by_cases h : a = a'
  · subst h
    simp [hb]
  simp [Ne.symm h, h]
#align finsupp.support_single_ne_zero Finsupp.support_single_ne_zero

theorem support_single_subset : (single a b).support ⊆ {a} :=
  support_mk'_subset
#align finsupp.support_single_subset Finsupp.support_single_subset

theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp; simp [single_eq_of_ne hx]]
#align finsupp.single_apply_mem Finsupp.single_apply_mem

theorem range_single_subset : Set.range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem
#align finsupp.range_single_subset Finsupp.range_single_subset

/-- `Finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`Finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by rw [eq]
  rwa [single_eq_same, single_eq_same] at this
#align finsupp.single_injective Finsupp.single_injective

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [single_eq_set_indicator]
#align finsupp.single_apply_eq_zero Finsupp.single_apply_eq_zero

theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [single_apply_eq_zero]
#align finsupp.single_apply_ne_zero Finsupp.single_apply_ne_zero

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).support ↔ a = a' ∧ b ≠ 0 := by
  simp [single_apply_eq_zero, not_or]
#align finsupp.mem_support_single Finsupp.mem_support_single

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.support ⊆ {a} ∧ f a = b := by
  refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases hx : a = x <;> simp only [hx, single_eq_same, single_eq_of_ne, Ne, not_false_iff]
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)
#align finsupp.eq_single_iff Finsupp.eq_single_iff

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  constructor
  · intro eq
    by_cases h : a₁ = a₂
    · refine' Or.inl ⟨h, _⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
    · rw [DFunLike.ext_iff] at eq
      have h₁ := eq a₁
      have h₂ := eq a₂
      simp only [single_eq_same, single_eq_of_ne h, single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · rw [single_zero, single_zero]
#align finsupp.single_eq_single_iff Finsupp.single_eq_single_iff

/-- `Finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`Finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b :=
  fun _a _a' H => (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left
#align finsupp.single_left_injective Finsupp.single_left_injective

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff
#align finsupp.single_left_inj Finsupp.single_left_inj

theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).support ≠ ⊥ := by
  simpa only [support_single_ne_zero _ h] using singleton_ne_empty _
#align finsupp.support_single_ne_bot Finsupp.support_single_ne_bot

theorem support_single_disjoint {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).support (single j b').support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]
#align finsupp.support_single_disjoint Finsupp.support_single_disjoint

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  simp [DFunLike.ext_iff, single_eq_set_indicator]
#align finsupp.single_eq_zero Finsupp.single_eq_zero

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  simp only [single_apply, eq_comm]
#align finsupp.single_swap Finsupp.single_swap

instance instNontrivial [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)
#align finsupp.nontrivial Finsupp.instNontrivial

theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm
#align finsupp.unique_single Finsupp.unique_single

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]
#align finsupp.unique_single_eq_iff Finsupp.unique_single_eq_iff

theorem support_eq_singleton {f : α →₀ M} {a : α} :
    f.support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h =>
    ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a,
      eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩,
    fun h => h.2.symm ▸ support_single_ne_zero _ h.1⟩
#align finsupp.support_eq_singleton Finsupp.support_eq_singleton

theorem support_eq_singleton' {f : α →₀ M} {a : α} :
    f.support = {a} ↔ ∃ b ≠ 0, f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨_b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩
#align finsupp.support_eq_singleton' Finsupp.support_eq_singleton'

theorem card_support_eq_one {f : α →₀ M} : card f.support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) :=
  by simp only [card_eq_one, support_eq_singleton]
#align finsupp.card_support_eq_one Finsupp.card_support_eq_one

theorem card_support_eq_one' {f : α →₀ M} :
    card f.support = 1 ↔ ∃ a, ∃ b ≠ 0, f = single a b := by
  simp only [card_eq_one, support_eq_singleton']
#align finsupp.card_support_eq_one' Finsupp.card_support_eq_one'

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩
#align finsupp.support_subset_singleton Finsupp.support_subset_singleton

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩
#align finsupp.support_subset_singleton' Finsupp.support_subset_singleton'

theorem card_support_le_one [Nonempty α] {f : α →₀ M} :
    card f.support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton]
#align finsupp.card_support_le_one Finsupp.card_support_le_one

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} :
    card f.support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [card_le_one_iff_subset_singleton, support_subset_singleton']
#align finsupp.card_support_le_one' Finsupp.card_support_le_one'

@[simp]
theorem equivFunOnFintype_single [Fintype α] (x : α) (m : M) :
    Finsupp.equivFunOnFintype (Finsupp.single x m) = Pi.single x m := by
  ext
  simp [Finsupp.single_eq_pi_single, equivFunOnFintype]
#align finsupp.equiv_fun_on_finite_single Finsupp.equivFunOnFintype_single

@[simp]
theorem equivFunOnFintype_symm_single [Fintype α] (x : α) (m : M) :
    Finsupp.equivFunOnFintype.symm (Pi.single x m) = Finsupp.single x m := by
  rw [← equivFunOnFintype_single, Equiv.symm_apply_apply]
#align finsupp.equiv_fun_on_finite_symm_single Finsupp.equivFunOnFintype_symm_single

end Single

/-! ### Declarations about `erase` -/


section Erase

variable [DecidableEq α] [Zero M]

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase (a : α) (f : α →₀ M) : α →₀ M :=
  ⟨fun a' ↦ if a' = a then 0 else f.1 a',
    f.support'.map fun xs ↦ ⟨xs.1, fun a ↦ (xs.prop a).imp_right (by simp only [·, ite_self])⟩⟩
#align finsupp.erase Finsupp.erase

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 := by
  simp only [erase, coe_mk', ite_true]
#align finsupp.erase_same Finsupp.erase_same

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' := by
  simp only [erase, coe_mk', h, ite_false, toFun_eq_coe]
#align finsupp.erase_ne Finsupp.erase_ne

theorem erase_apply {a a' : α} {f : α →₀ M} :
    f.erase a a' = if a' = a then 0 else f a' := by
  rw [erase, coe_mk', toFun_eq_coe]

@[simp]
theorem support_erase [(x : M) → Decidable (x ≠ 0)] {a : α} {f : α →₀ M} :
    (f.erase a).support = f.support.erase a := by
  ext a'
  by_cases h1 : a' = a
  · simp only [h1, mem_support_toFun, erase_apply, ite_true, ne_eq, not_true, not_not,
      Finset.mem_erase, false_and]
  by_cases h2 : f a' ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align finsupp.support_erase Finsupp.support_erase

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same]
    rfl
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)
#align finsupp.erase_single Finsupp.erase_single

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  ext s; by_cases hs : s = a
  · rw [hs, erase_same, single_eq_of_ne h.symm]
  · rw [erase_ne hs]
#align finsupp.erase_single_ne Finsupp.erase_single_ne

@[simp]
theorem erase_of_not_mem_support [(x : M) → Decidable (x ≠ 0)] {f : α →₀ M} {a}
    (haf : a ∉ f.support) : erase a f = f := by
  ext b; by_cases hab : b = a
  · rwa [hab, erase_same, eq_comm, ← not_mem_support_iff]
  · rw [erase_ne hab]
#align finsupp.erase_of_not_mem_support Finsupp.erase_of_not_mem_support

@[simp, nolint simpNF] -- Porting note: simpNF linter claims simp can prove this, it can not
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  classical rw [← support_eq_empty, support_erase, support_zero, erase_empty]
#align finsupp.erase_zero Finsupp.erase_zero

end Erase

/-! ### Declarations about `update` -/


section Update

variable [DecidableEq α] [Zero M] [(x : M) → Decidable (x ≠ 0)]
variable (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `Finsupp.support`.
Otherwise, if `a` was not in the `Finsupp.support`, it is added to it.

This is the finitely-supported version of `Function.update`. -/
def update (f : α →₀ M) (a : α) (b : M) : α →₀ M :=
  ⟨Function.update f a b,
    f.support'.map fun s =>
      ⟨a ::ₘ s.1, fun a' => by
        rcases eq_or_ne a a' with (rfl | hi)
        · simp
        · obtain ha' | (ha' : f a' = 0) := s.prop a'
          · exact Or.inl (Multiset.mem_cons_of_mem ha')
          · exact Or.inr ((Function.update_noteq hi.symm b _).trans ha')⟩⟩
#align finsupp.update Finsupp.update

@[simp, norm_cast]
theorem coe_update : (f.update a b : α → M) = Function.update f a b :=
  rfl
#align finsupp.coe_update Finsupp.coe_update

@[simp]
theorem update_self : f.update a (f a) = f := by
  ext
  simp
#align finsupp.update_self Finsupp.update_self

@[simp]
theorem zero_update : update 0 a b = single a b := by
  ext
  rw [single_eq_update]
  rfl
#align finsupp.zero_update Finsupp.zero_update

theorem support_update_ne_zero (f : α →₀ M) (a : α) {b : M}
    (h : b ≠ 0) : support (f.update a b) = insert a f.support := by
  ext a'
  rcases eq_or_ne a a' with (rfl | ha)
  · simp [h]
  · simp [ha.symm]
#align finsupp.support_update_ne_zero Finsupp.support_update_ne_zero

@[simp]
theorem update_eq_erase : f.update a 0 = f.erase a := by
  ext a'
  rcases eq_or_ne a a' with (rfl | ha)
  · simp
  · simp [ha.symm]

theorem update_comm (f : α →₀ M) {a₁ a₂ : α} (h : a₁ ≠ a₂) (m₁ m₂ : M) :
    update (update f a₁ m₁) a₂ m₂ = update (update f a₂ m₂) a₁ m₁ :=
  DFunLike.coe_injective <| Function.update_comm h _ _ _

@[simp] theorem update_idem (f : α →₀ M) (a : α) (b c : M) :
    update (update f a b) a c = update f a c :=
  DFunLike.coe_injective <| Function.update_idem _ _ _

-- The name matches `Finset.erase_insert_of_ne`
theorem erase_update_of_ne (f : α →₀ M) {a a' : α} (ha : a ≠ a') (b : M) :
    erase a (update f a' b) = update (erase a f) a' b := by
  rw [← update_eq_erase, ← update_eq_erase, update_comm _ ha]

-- not `simp` as `erase_of_not_mem_support` can prove this
theorem erase_idem (f : α →₀ M) (a : α) :
    erase a (erase a f) = erase a f := by
  rw [← update_eq_erase, ← update_eq_erase, update_idem]

@[simp] theorem update_erase_eq_update (f : α →₀ M) (a : α) (b : M) :
    update (erase a f) a b = update f a b := by
  rw [← update_eq_erase, update_idem]

@[simp] theorem erase_update_eq_erase (f : α →₀ M) (a : α) (b : M) :
    erase a (update f a b) = erase a f := by
  rw [← update_eq_erase, ← update_eq_erase, update_idem]

theorem support_update [Decidable (b = 0)] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  ext a'
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]
#align finsupp.support_update Finsupp.support_update

theorem support_update_zero :
    support (f.update a 0) = f.support.erase a := by
  simp
#align finsupp.support_update_zero Finsupp.support_update_zero

theorem support_update_subset {b} [DecidableEq M] :
    support (f.update a b) ⊆ insert a f.support := by
  rw [support_update]
  split_ifs
  · exact (erase_subset _ _).trans (subset_insert _ _)
  · rfl

end Update

section OfSupportFinite

variable [Zero M]

/-- The natural `Finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.support f).Finite) : α →₀ M where
  toFun := f
  support' := Trunc.mk ⟨hf.toFinset.val, by simp [em']⟩
#align finsupp.of_support_finite Finsupp.ofSupportFinite

theorem ofSupportFinite_coe {f : α → M} {hf : (Function.support f).Finite} :
    (ofSupportFinite f hf : α → M) = f :=
  rfl
#align finsupp.of_support_finite_coe Finsupp.ofSupportFinite_coe

instance instCanLift : CanLift (α → M) (α →₀ M) (⇑) fun f => (Function.support f).Finite where
  prf f hf := ⟨ofSupportFinite f hf, rfl⟩
#align finsupp.can_lift Finsupp.instCanLift

end OfSupportFinite

/-! ### Declarations about `mapRange` -/


section MapRange

variable [DecidableEq α] [Zero M] [Zero N] [Zero P]
variable [(x : M) → Decidable (x ≠ 0)] [(x : N) → Decidable (x ≠ 0)]

/-- The composition of `f : M → N` and `g : α →₀ M` is `mapRange f hf g : α →₀ N`,
which is well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled (defined in `Mathlib/Data/Finsupp/Basic.lean`):

* `Finsupp.mapRange.equiv`
* `Finsupp.mapRange.zeroHom`
* `Finsupp.mapRange.addMonoidHom`
* `Finsupp.mapRange.addEquiv`
* `Finsupp.mapRange.linearMap`
* `Finsupp.mapRange.linearEquiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  ⟨f ∘ g,
    g.support'.map fun s => ⟨s.1, fun a => (s.2 a).imp_right fun h : g a = 0 => by
      rw [comp_apply, h, hf]⟩⟩
#align finsupp.map_range Finsupp.mapRange

@[simp]
theorem mapRange_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} :
    mapRange f hf g a = f (g a) :=
  rfl
#align finsupp.map_range_apply Finsupp.mapRange_apply

@[simp]
theorem mapRange_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun _ => by simp only [hf, zero_apply, mapRange_apply]
#align finsupp.map_range_zero Finsupp.mapRange_zero

@[simp]
theorem mapRange_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl
#align finsupp.map_range_id Finsupp.mapRange_id

theorem mapRange_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0)
    (g : α →₀ M) : mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl
#align finsupp.map_range_comp Finsupp.mapRange_comp

theorem mapRange_def {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
    mapRange f hf g = mk g.support (fun a => f (g a.1)) := by
  ext i
  by_cases h : g i ≠ 0 <;> simp at h <;> simp [h, hf]

theorem support_mapRange {f : M → N} {hf : f 0 = 0} {g : α →₀ M} :
    (mapRange f hf g).support ⊆ g.support := by
  simp [mapRange_def]
#align finsupp.support_map_range Finsupp.support_mapRange

@[simp]
theorem mapRange_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} :
    mapRange f hf (single a b) = single a (f b) :=
  ext fun a' => by
    simpa only [single_eq_pi_single] using Pi.apply_single _ (fun _ => hf) a _ a'
#align finsupp.map_range_single Finsupp.mapRange_single

theorem support_mapRange_of_injective [DecidableEq ι] {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M)
    (he : Function.Injective e) : (Finsupp.mapRange e he0 f).support = f.support := by
  ext
  simp only [Finsupp.mem_support_iff, Ne, Finsupp.mapRange_apply]
  exact he.ne_iff' he0
#align finsupp.support_map_range_of_injective Finsupp.support_mapRange_of_injective

end MapRange

/-! ### Declarations about `embDomain` -/


section EmbDomain

variable [Zero M] [Zero N] [DecidableEq β] [(x : M) → Decidable (x ≠ 0)]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `Finsupp.embDomain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M := by
  refine v.support'.lift
    (fun s =>
      { toFun := fun b =>
          if h : b ∈ s.val.map f then
            v (s.val.choose (fun a => f a = b) ?hff) else 0
        support' := Trunc.mk ⟨s.val.map f, fun a => ?hfs⟩ }) ?hv
  case hff =>
    rcases Multiset.mem_map.1 h with ⟨a, ha, rfl⟩
    exact ExistsUnique.intro a ⟨ha, rfl⟩ fun a' ⟨_, ha'⟩ => f.injective ha'
  case hfs =>
    beta_reduce
    split_ifs with h <;> simp [h]
  case hv =>
    classical
    rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩
    ext b; dsimp
    by_cases hb : b ∈ s₂.map f
    case pos =>
      rw [s₂.mem_map] at hb; rcases hb with ⟨a, ha, rfl⟩
      simpa [ha, Multiset.choose_property (· = a),
        ← Classical.or_iff_not_imp_left, eq_comm (a := (0 : M))] using hs₁ a
    case neg =>
      simp [hb]
      rintro a ⟨ha, rfl⟩
      simp at hb
      simpa [Multiset.choose_property (· = a)] using (hs₂ a).resolve_left hb
#align finsupp.emb_domain Finsupp.embDomain

@[simp]
theorem embDomain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl
#align finsupp.emb_domain_zero Finsupp.embDomain_zero

@[simp]
theorem embDomain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  classical
  cases' v with v s; induction' s using Trunc.ind with s; cases' s with s hs
  simpa [embDomain, Trunc.lift_mk, Multiset.choose_property (· = a), eq_comm (a := (0 : M)),
    ← Classical.or_iff_not_imp_left] using hs a
#align finsupp.emb_domain_apply Finsupp.embDomain_apply

theorem embDomain_notin_range (f : α ↪ β) (v : α →₀ M) (b : β) (h : b ∉ Set.range f) :
    embDomain f v b = 0 := by
  cases' v with v s; induction' s using Trunc.ind with s; cases' s with s hs
  simp at h
  simp [embDomain, Trunc.lift_mk, h]
#align finsupp.emb_domain_notin_range Finsupp.embDomain_notin_range

@[simp]
theorem support_embDomain [DecidableEq α] (f : α ↪ β) (v : α →₀ M) :
    (embDomain f v).support = v.support.map f := by
  ext b
  by_cases hb : b ∈ Set.range f
  case pos =>
    rcases hb with ⟨a, rfl⟩
    simp
  case neg =>
    have hb' := hb; simp at hb'
    simp [embDomain_notin_range, embDomain_notin_range f v b hb, hb']
#align finsupp.support_emb_domain Finsupp.support_embDomain

theorem embDomain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) :=
  fun l₁ l₂ h => ext fun a => by simpa only [embDomain_apply] using DFunLike.ext_iff.1 h (f a)
#align finsupp.emb_domain_injective Finsupp.embDomain_injective

@[simp]
theorem embDomain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (embDomain_injective f).eq_iff
#align finsupp.emb_domain_inj Finsupp.embDomain_inj

@[simp]
theorem embDomain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (embDomain_injective f).eq_iff' <| embDomain_zero f
#align finsupp.emb_domain_eq_zero Finsupp.embDomain_eq_zero

theorem embDomain_mapRange (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a', rfl⟩
    rw [mapRange_apply, embDomain_apply, embDomain_apply, mapRange_apply]
  · rw [mapRange_apply, embDomain_notin_range, embDomain_notin_range, ← hg] <;> assumption
#align finsupp.emb_domain_map_range Finsupp.embDomain_mapRange

theorem single_of_embDomain_single [DecidableEq α] (l : α →₀ M) (f : α ↪ β) (a : β) (b : M)
    (hb : b ≠ 0) (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  have h_map_support : Finset.map f l.support = {a} := by
    rw [← support_embDomain, h, support_single_ne_zero _ hb]
  have ha : a ∈ Finset.map f l.support := by simp only [h_map_support, Finset.mem_singleton]
  rcases Finset.mem_map.1 ha with ⟨c, _hc₁, hc₂⟩
  use c
  constructor
  · ext d
    rw [← embDomain_apply f l, h]
    by_cases h_cases : c = d
    · simp only [Eq.symm h_cases, hc₂, single_eq_same]
    · rw [single_apply, single_apply, if_neg, if_neg h_cases]
      by_contra hfd
      exact h_cases (f.injective (hc₂.trans hfd))
  · exact hc₂
#align finsupp.single_of_emb_domain_single Finsupp.single_of_embDomain_single

@[simp]
theorem embDomain_single [DecidableEq α] (f : α ↪ β) (a : α) (m : M) :
    embDomain f (single a m) = single (f a) m := by
  ext b
  by_cases h : b ∈ Set.range f
  · rcases h with ⟨a', rfl⟩
    simp [single_apply]
  · simp only [embDomain_notin_range, h, single_apply, not_false_iff]
    rw [if_neg]
    rintro rfl
    simp at h
#align finsupp.emb_domain_single Finsupp.embDomain_single

end EmbDomain

/-! ### Declarations about `zipWith` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P] [DecidableEq α]
variable [(x : M) → Decidable (x ≠ 0)] [(x : N) → Decidable (x ≠ 0)] [(x : P) → Decidable (x ≠ 0)]

/-- Given finitely supported functions `g₁ : α →₀ M` and `g₂ : α →₀ N` and function `f : M → N → P`,
`Finsupp.zipWith f hf g₁ g₂` is the finitely supported function `α →₀ P` satisfying
`zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, which is well-defined when `f 0 0 = 0`. -/
def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  ⟨fun a => f (g₁ a) (g₂ a), by
    refine' g₁.support'.bind fun xs => _
    refine' g₂.support'.map fun ys => _
    refine' ⟨xs + ys, fun a => _⟩
    obtain h1 | (h1 : g₁ a = 0) := xs.prop a
    · left
      rw [Multiset.mem_add]
      left
      exact h1
    obtain h2 | (h2 : g₂ a = 0) := ys.prop a
    · left
      rw [Multiset.mem_add]
      right
      exact h2
    right; rw [← hf, ← h1, ← h2]⟩
#align finsupp.zip_with Finsupp.zipWith

@[simp]
theorem zipWith_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl
#align finsupp.zip_with_apply Finsupp.zipWith_apply

theorem zipWith_def {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} :
    zipWith f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun a => f (g₁ a.1) (g₂ a.1) := by
  ext a
  by_cases h1 : g₁ a ≠ 0 <;> by_cases h2 : g₂ a ≠ 0 <;> simp only [not_not, Ne] at h1 h2 <;>
    simp [h1, h2, hf]

theorem support_zipWith {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M}
    {g₂ : α →₀ N} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [zipWith_def]
#align finsupp.support_zip_with Finsupp.support_zipWith

@[simp]
theorem zipWith_single_single (f : M → N → P) (hf : f 0 0 = 0) (a : α) (m : M) (n : N) :
    zipWith f hf (single a m) (single a n) = single a (f m n) := by
  ext a'
  rw [zipWith_apply]
  obtain rfl | ha' := eq_or_ne a a'
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne ha', single_eq_of_ne ha', single_eq_of_ne ha', hf]

end ZipWith

/-! ### Additive monoid structure on `α →₀ M` -/


section AddZeroClass

variable [AddZeroClass M] [DecidableEq α]

instance instAdd : Add (α →₀ M) :=
  ⟨zipWith (· + ·) (add_zero 0)⟩
#align finsupp.has_add Finsupp.instAdd

@[simp, norm_cast] lemma coe_add (f g : α →₀ M) : ⇑(f + g) = f + g := rfl
#align finsupp.coe_add Finsupp.coe_add

theorem add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a :=
  rfl
#align finsupp.add_apply Finsupp.add_apply

theorem support_add [(x : M) → Decidable (x ≠ 0)] {g₁ g₂ : α →₀ M} :
    (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zipWith
#align finsupp.support_add Finsupp.support_add

theorem support_add_eq [(x : M) → Decidable (x ≠ 0)] {g₁ g₂ : α →₀ M}
    (h : Disjoint g₁.support g₂.support) : (g₁ + g₂).support = g₁.support ∪ g₂.support :=
  le_antisymm support_zipWith fun a ha =>
    (Finset.mem_union.1 ha).elim
      (fun ha => by
        have : a ∉ g₂.support := disjoint_left.1 h ha
        simp only [mem_support_iff, not_not] at *; simpa only [add_apply, this, add_zero] )
      fun ha => by
      have : a ∉ g₁.support := disjoint_right.1 h ha
      simp only [mem_support_iff, not_not] at *; simpa only [add_apply, this, zero_add]
#align finsupp.support_add_eq Finsupp.support_add_eq

@[simp]
theorem single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  (zipWith_single_single _ _ _ _ _).symm
#align finsupp.single_add Finsupp.single_add

instance instAddZeroClass : AddZeroClass (α →₀ M) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add
#align finsupp.add_zero_class Finsupp.instAddZeroClass

instance instIsLeftCancelAdd [IsLeftCancelAdd M] : IsLeftCancelAdd (α →₀ M) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x

/-- When ι is finite and M is an `AddMonoid`,
  then `Finsupp.equivFunOnFintype` gives an `AddEquiv` -/
def addEquivFunOnFintype {ι : Type*} [Fintype ι] : (ι →₀ M) ≃+ (ι → M) where
  __ := Finsupp.equivFunOnFintype
  map_add' _ _ := rfl

/-- AddEquiv between (ι →₀ M) and M, when ι has a unique element -/
def _root_.AddEquiv.finsuppUnique {ι : Type*} [Unique ι] : (ι →₀ M) ≃+ M where
  __ := Equiv.finsuppUnique
  map_add' _ _ := rfl

lemma _root_.AddEquiv.finsuppUnique_symm {M : Type*} [AddZeroClass M] (d : M) :
    AddEquiv.finsuppUnique.symm d = single () d := by
  rw [Finsupp.unique_single (AddEquiv.finsuppUnique.symm d), Finsupp.unique_single_eq_iff]
  simp [AddEquiv.finsuppUnique]

instance instIsRightCancelAdd [IsRightCancelAdd M] : IsRightCancelAdd (α →₀ M) where
  add_right_cancel _ _ _ h := ext fun x => add_right_cancel <| DFunLike.congr_fun h x

instance instIsCancelAdd [IsCancelAdd M] : IsCancelAdd (α →₀ M) where

/-- `Finsupp.single` as an `AddMonoidHom`.

See `Finsupp.lsingle` in `LinearAlgebra/Finsupp` for the stronger version as a linear map. -/
@[simps]
def singleAddHom (a : α) : M →+ α →₀ M where
  toFun := single a
  map_zero' := single_zero a
  map_add' := single_add a
#align finsupp.single_add_hom Finsupp.singleAddHom

theorem singleAddHom_coe (a : α) : ⇑(singleAddHom a : M →+ α →₀ M) = single a :=
  rfl

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `Finsupp.lapply` in `LinearAlgebra/Finsupp` for the stronger version as a linear map. -/
@[simps apply]
def applyAddHom (a : α) : (α →₀ M) →+ M where
  toFun g := g a
  map_zero' := zero_apply
  map_add' _ _ := add_apply _ _ _
#align finsupp.apply_add_hom Finsupp.applyAddHom
#align finsupp.apply_add_hom_apply Finsupp.applyAddHom_apply

/-- Coercion from a `Finsupp` to a function type is an `AddMonoidHom`. -/
@[simps]
def coeFnAddHom : (α →₀ M) →+ α → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align finsupp.coe_fn_add_hom Finsupp.coeFnAddHom
#align finsupp.coe_fn_add_hom_apply Finsupp.coeFnAddHom_apply

theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) :
    f.update a b = single a b + f.erase a := by
  ext j
  rcases eq_or_ne a j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
#align finsupp.update_eq_single_add_erase Finsupp.update_eq_single_add_erase

theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) :
    f.update a b = f.erase a + single a b := by
  ext j
  rcases eq_or_ne a j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, single_apply, h, erase_ne, h.symm]
#align finsupp.update_eq_erase_add_single Finsupp.update_eq_erase_add_single

theorem single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]
#align finsupp.single_add_erase Finsupp.single_add_erase

theorem erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]
#align finsupp.erase_add_single Finsupp.erase_add_single

@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s; by_cases hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zero]
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]
#align finsupp.erase_add Finsupp.erase_add

/-- `Finsupp.erase` as an `AddMonoidHom`. -/
@[simps]
def eraseAddHom (a : α) : (α →₀ M) →+ α →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a
#align finsupp.erase_add_hom Finsupp.eraseAddHom

@[elab_as_elim]
protected theorem induction [(x : M) → Decidable (x ≠ 0)] {p : (α →₀ M) → Prop} (f : α →₀ M)
    (h0 : p 0) (ha : ∀ (a b) (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices p (single a (f a) + f.erase a) by rwa [single_add_erase] at this
    classical
      apply ha
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]
#align finsupp.induction Finsupp.induction

theorem induction₂ [(x : M) → Decidable (x ≠ 0)] {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.support → b ≠ 0 → p f → p (f + single a b)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices p (f.erase a + single a (f a)) by rwa [erase_add_single] at this
    classical
      apply ha
      · rw [support_erase, mem_erase]
        exact fun H => H.1 rfl
      · rw [← mem_support_iff, hf]
        exact mem_cons_self _ _
      · apply ih _ _
        rw [support_erase, hf, Finset.erase_cons]
#align finsupp.induction₂ Finsupp.induction₂

theorem induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g)) (hsingle : ∀ a b, p (single a b)) : p f := by
  classical exact induction₂ f h0 fun _a _b _f _ _ w => hadd _ _ w (hsingle _ _)
#align finsupp.induction_linear Finsupp.induction_linear

@[simp]
theorem add_closure_setOf_eq_single :
    AddSubmonoid.closure { f : α →₀ M | ∃ a b, f = single a b } = ⊤ := by
  classical exact top_unique fun x _hx =>
    Finsupp.induction x (AddSubmonoid.zero_mem _) fun a b _f _ha _hb hf =>
      AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure <| ⟨a, b, rfl⟩) hf
#align finsupp.add_closure_set_of_eq_single Finsupp.add_closure_setOf_eq_single

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal. -/
theorem addHom_ext [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x y, f (single x y) = g (single x y)) : f = g := by
  refine' AddMonoidHom.eq_of_eqOn_denseM add_closure_setOf_eq_single _
  rintro _ ⟨x, y, rfl⟩
  apply H
#align finsupp.add_hom_ext Finsupp.addHom_ext

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`,
then they are equal.

We formulate this using equality of `AddMonoidHom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext high]
theorem addHom_ext' [AddZeroClass N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)
#align finsupp.add_hom_ext' Finsupp.addHom_ext'

theorem mulHom_ext [MulOneClass N] ⦃f g : Multiplicative (α →₀ M) →* N⦄
    (H : ∀ x y, f (Multiplicative.ofAdd <| single x y) = g (Multiplicative.ofAdd <| single x y)) :
    f = g :=
  MonoidHom.ext <|
    DFunLike.congr_fun <| by
      have := @addHom_ext α M (Additive N) _ _ _
        (MonoidHom.toAdditive'' f) (MonoidHom.toAdditive'' g) H
      ext
      rw [DFunLike.ext_iff] at this
      apply this
#align finsupp.mul_hom_ext Finsupp.mulHom_ext

@[ext]
theorem mulHom_ext' [MulOneClass N] {f g : Multiplicative (α →₀ M) →* N}
    (H : ∀ x, f.comp (AddMonoidHom.toMultiplicative (singleAddHom x)) =
              g.comp (AddMonoidHom.toMultiplicative (singleAddHom x))) :
    f = g :=
  mulHom_ext fun x => DFunLike.congr_fun (H x)
#align finsupp.mul_hom_ext' Finsupp.mulHom_ext'

theorem mapRange_add [AddZeroClass N] {f : M → N} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x + y) = f x + f y) (v₁ v₂ : α →₀ M) :
    mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', add_apply, mapRange_apply]
#align finsupp.map_range_add Finsupp.mapRange_add

theorem mapRange_add' [AddZeroClass N] [FunLike β M N] [AddMonoidHomClass β M N]
    {f : β} (v₁ v₂ : α →₀ M) :
    mapRange f (map_zero f) (v₁ + v₂) = mapRange f (map_zero f) v₁ + mapRange f (map_zero f) v₂ :=
  mapRange_add (map_add f) v₁ v₂
#align finsupp.map_range_add' Finsupp.mapRange_add'

/-- Bundle `Finsupp.embDomain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps]
def embDomain.addMonoidHom [DecidableEq β] (f : α ↪ β) : (α →₀ M) →+ β →₀ M where
  toFun v := embDomain f v
  map_zero' := by simp
  map_add' v w := by
    ext b
    by_cases h : b ∈ Set.range f
    · rcases h with ⟨a, rfl⟩
      simp
    · simp only [Set.mem_range, not_exists, coe_add, Pi.add_apply,
        embDomain_notin_range _ _ _ h, add_zero]
#align finsupp.emb_domain.add_monoid_hom Finsupp.embDomain.addMonoidHom

@[simp]
theorem embDomain_add [DecidableEq β] (f : α ↪ β) (v w : α →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w :=
  (embDomain.addMonoidHom f).map_add v w
#align finsupp.emb_domain_add Finsupp.embDomain_add

end AddZeroClass

section AddMonoid

variable [AddMonoid M]

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance instNatSMul : SMul ℕ (α →₀ M) :=
  ⟨fun n v => v.mapRange (n • ·) (nsmul_zero _)⟩
#align finsupp.has_nat_scalar Finsupp.instNatSMul

instance instAddMonoid : AddMonoid (α →₀ M) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl
#align finsupp.add_monoid Finsupp.instAddMonoid

end AddMonoid

instance instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (α →₀ M) :=
  --TODO: add reference to library note in PR #7432
  { DFunLike.coe_injective.addCommMonoid (↑) coe_zero coe_add (fun _ _ => rfl) with
    toAddMonoid := Finsupp.instAddMonoid }
#align finsupp.add_comm_monoid Finsupp.instAddCommMonoid

instance instNeg [NegZeroClass G] : Neg (α →₀ G) :=
  ⟨mapRange Neg.neg neg_zero⟩
#align finsupp.has_neg Finsupp.instNeg

@[simp, norm_cast] lemma coe_neg [NegZeroClass G] (g : α →₀ G) : ⇑(-g) = -g := rfl
#align finsupp.coe_neg Finsupp.coe_neg

theorem neg_apply [NegZeroClass G] (g : α →₀ G) (a : α) : (-g) a = -g a :=
  rfl
#align finsupp.neg_apply Finsupp.neg_apply

theorem mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : α →₀ G) : mapRange f hf (-v) = -mapRange f hf v :=
  ext fun _ => by simp only [hf', neg_apply, mapRange_apply]
#align finsupp.map_range_neg Finsupp.mapRange_neg

theorem mapRange_neg' [AddGroup G] [SubtractionMonoid H] [FunLike β G H] [AddMonoidHomClass β G H]
    {f : β} (v : α →₀ G) :
    mapRange f (map_zero f) (-v) = -mapRange f (map_zero f) v :=
  mapRange_neg (map_neg f) v
#align finsupp.map_range_neg' Finsupp.mapRange_neg'

instance instSub [SubNegZeroMonoid G] : Sub (α →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩
#align finsupp.has_sub Finsupp.instSub

@[simp, norm_cast] lemma coe_sub [SubNegZeroMonoid G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ := rfl
#align finsupp.coe_sub Finsupp.coe_sub

theorem sub_apply [SubNegZeroMonoid G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl
#align finsupp.sub_apply Finsupp.sub_apply

theorem mapRange_sub [SubNegZeroMonoid G] [SubNegZeroMonoid H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x y, f (x - y) = f x - f y) (v₁ v₂ : α →₀ G) :
    mapRange f hf (v₁ - v₂) = mapRange f hf v₁ - mapRange f hf v₂ :=
  ext fun _ => by simp only [hf', sub_apply, mapRange_apply]
#align finsupp.map_range_sub Finsupp.mapRange_sub

theorem mapRange_sub' [AddGroup G] [SubtractionMonoid H] [FunLike β G H] [AddMonoidHomClass β G H]
    {f : β} (v₁ v₂ : α →₀ G) :
    mapRange f (map_zero f) (v₁ - v₂) = mapRange f (map_zero f) v₁ - mapRange f (map_zero f) v₂ :=
  mapRange_sub (map_sub f) v₁ v₂
#align finsupp.map_range_sub' Finsupp.mapRange_sub'

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance instIntSMul [AddGroup G] : SMul ℤ (α →₀ G) :=
  ⟨fun n v => v.mapRange (n • ·) (zsmul_zero _)⟩
#align finsupp.has_int_scalar Finsupp.instIntSMul

instance instAddGroup [AddGroup G] : AddGroup (α →₀ G) :=
  --TODO: add reference to library note in PR #7432
  { DFunLike.coe_injective.addGroup (↑) coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl)
      fun _ _ => rfl with
    toAddMonoid := Finsupp.instAddMonoid }
#align finsupp.add_group Finsupp.instAddGroup

instance instAddCommGroup [AddCommGroup G] : AddCommGroup (α →₀ G) :=
  --TODO: add reference to library note in PR #7432
  { DFunLike.coe_injective.addCommGroup (↑) coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl)
      fun _ _ => rfl with
    toAddGroup := Finsupp.instAddGroup }
#align finsupp.add_comm_group Finsupp.instAddCommGroup

theorem single_add_single_eq_single_add_single [AddCommMonoid M] [DecidableEq α] {k l m n : α}
    {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      (k = m ∧ l = n) ∨ (u = v ∧ k = n ∧ l = m) ∨ (u + v = 0 ∧ k = l ∧ m = n) := by
  classical
    simp_rw [DFunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
    exact Pi.single_add_single_eq_single_add_single hu hv
#align finsupp.single_add_single_eq_single_add_single Finsupp.single_add_single_eq_single_add_single

@[simp]
theorem support_neg [AddGroup G] [DecidableEq α] [(x : G) → Decidable (x ≠ 0)] (f : α →₀ G) :
    support (-f) = support f :=
  Finset.Subset.antisymm support_mapRange
    (calc
      support f = support (- -f) := congr_arg support (neg_neg _).symm
      _ ⊆ support (-f) := support_mapRange
      )
#align finsupp.support_neg Finsupp.support_neg

theorem support_sub [AddGroup G] [DecidableEq α] [(x : G) → Decidable (x ≠ 0)] {f g : α →₀ G} :
    support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add
#align finsupp.support_sub Finsupp.support_sub

theorem erase_eq_sub_single [AddGroup G] [DecidableEq α] (f : α →₀ G) (a : α) :
    f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a a' with (rfl | h)
  · simp
  · simp [erase_ne h.symm, single_eq_of_ne h]
#align finsupp.erase_eq_sub_single Finsupp.erase_eq_sub_single

theorem update_eq_sub_add_single [AddGroup G] [DecidableEq α] (f : α →₀ G) (a : α) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]
#align finsupp.update_eq_sub_add_single Finsupp.update_eq_sub_add_single

end Finsupp
