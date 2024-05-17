/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.DFinsupp.Basic
import Mathlib.Data.Finsupp.Basic

#align_import data.finsupp.to_dfinsupp from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Conversion between `Finsupp` and homogenous `DFinsupp`

This module provides conversions between `Finsupp` and `DFinsupp`.
It is in its own file since neither `Finsupp` or `DFinsupp` depend on each other.

## Main definitions

* "identity" maps between `Finsupp` and `DFinsupp`:
  * `Finsupp.toDFinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
  * `DFinsupp.toFinsupp : (Π₀ i : ι, M) → (ι →₀ M)`
  * Bundled equiv versions of the above:
    * `finsuppEquivDFinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
    * `finsuppAddEquivDFinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
    * `finsuppLequivDFinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`
* stronger versions of `Finsupp.split`:
  * `sigmaFinsuppEquivDFinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppAddEquivDFinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppLequivDFinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `Finsupp.toDFinsupp_coe`
* `Finsupp.toDFinsupp_support`
* `DFinsupp.toFinsupp_coe`
* `DFinsupp.toFinsupp_support`

and therefore map `Finsupp.single` to `DFinsupp.single` and vice versa:

* `Finsupp.toDFinsupp_single`
* `DFinsupp.toFinsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `Finsupp.toDFinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

-/


variable {ι : Type*} {R : Type*} {M : Type*}

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret a `Finsupp` as a homogenous `DFinsupp`. -/
def Finsupp.toDFinsupp [Zero M] (f : ι →₀ M) : Π₀ _ : ι, M where
  toFun := f.toFun
  support' := f.support'
#align finsupp.to_dfinsupp Finsupp.toDFinsupp

@[simp]
theorem Finsupp.toDFinsupp_coe [Zero M] (f : ι →₀ M) : ⇑f.toDFinsupp = f :=
  rfl
#align finsupp.to_dfinsupp_coe Finsupp.toDFinsupp_coe

section

variable [DecidableEq ι] [Zero M]

@[simp]
theorem Finsupp.toDFinsupp_single (i : ι) (m : M) :
    (Finsupp.single i m).toDFinsupp = DFinsupp.single i m :=
  rfl
#align finsupp.to_dfinsupp_single Finsupp.toDFinsupp_single

variable [∀ m : M, Decidable (m ≠ 0)]

@[simp]
theorem toDFinsupp_support (f : ι →₀ M) : f.toDFinsupp.support = f.support :=
  rfl
#align to_dfinsupp_support toDFinsupp_support

/-- Interpret a homogenous `DFinsupp` as a `Finsupp`.

Note that the elaborator has a lot of trouble with this definition - it is often necessary to
write `(DFinsupp.toFinsupp f : ι →₀ M)` instead of `f.toFinsupp`, as for some unknown reason
using dot notation or omitting the type ascription prevents the type being resolved correctly. -/
def DFinsupp.toFinsupp (f : Π₀ _ : ι, M) : ι →₀ M where
  toFun := f.toFun
  support' := f.support'
#align dfinsupp.to_finsupp DFinsupp.toFinsupp

@[simp]
theorem DFinsupp.toFinsupp_coe (f : Π₀ _ : ι, M) : ⇑f.toFinsupp = f :=
  rfl
#align dfinsupp.to_finsupp_coe DFinsupp.toFinsupp_coe

@[simp]
theorem DFinsupp.toFinsupp_support (f : Π₀ _ : ι, M) : f.toFinsupp.support = f.support :=
  rfl
#align dfinsupp.to_finsupp_support DFinsupp.toFinsupp_support

@[simp]
theorem DFinsupp.toFinsupp_single (i : ι) (m : M) :
    (DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m :=
  rfl
#align dfinsupp.to_finsupp_single DFinsupp.toFinsupp_single

@[simp]
theorem Finsupp.toDFinsupp_toFinsupp (f : ι →₀ M) : f.toDFinsupp.toFinsupp = f :=
  rfl
#align finsupp.to_dfinsupp_to_finsupp Finsupp.toDFinsupp_toFinsupp

@[simp]
theorem DFinsupp.toFinsupp_toDFinsupp (f : Π₀ _ : ι, M) : f.toFinsupp.toDFinsupp = f :=
  rfl
#align dfinsupp.to_finsupp_to_dfinsupp DFinsupp.toFinsupp_toDFinsupp

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace Finsupp

@[simp]
theorem toDFinsupp_zero [Zero M] : (0 : ι →₀ M).toDFinsupp = 0 :=
  rfl
#align finsupp.to_dfinsupp_zero Finsupp.toDFinsupp_zero

@[simp]
theorem toDFinsupp_add [AddZeroClass M] (f g : ι →₀ M) :
    (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp :=
  rfl
#align finsupp.to_dfinsupp_add Finsupp.toDFinsupp_add

@[simp]
theorem toDFinsupp_neg [AddGroup M] (f : ι →₀ M) : (-f).toDFinsupp = -f.toDFinsupp :=
  rfl
#align finsupp.to_dfinsupp_neg Finsupp.toDFinsupp_neg

@[simp]
theorem toDFinsupp_sub [AddGroup M] (f g : ι →₀ M) :
    (f - g).toDFinsupp = f.toDFinsupp - g.toDFinsupp :=
  rfl
#align finsupp.to_dfinsupp_sub Finsupp.toDFinsupp_sub

@[simp]
theorem toDFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f : ι →₀ M) :
    (r • f).toDFinsupp = r • f.toDFinsupp :=
  rfl
#align finsupp.to_dfinsupp_smul Finsupp.toDFinsupp_smul

end Finsupp

namespace DFinsupp

variable [DecidableEq ι]

@[simp]
theorem toFinsupp_zero [Zero M] : toFinsupp 0 = (0 : ι →₀ M) :=
  rfl
#align dfinsupp.to_finsupp_zero DFinsupp.toFinsupp_zero

@[simp]
theorem toFinsupp_add [AddZeroClass M] (f g : Π₀ _ : ι, M) :
    (toFinsupp (f + g) : ι →₀ M) = toFinsupp f + toFinsupp g :=
  rfl
#align dfinsupp.to_finsupp_add DFinsupp.toFinsupp_add

@[simp]
theorem toFinsupp_neg [AddGroup M] (f : Π₀ _ : ι, M) :
    (toFinsupp (-f) : ι →₀ M) = -toFinsupp f :=
  rfl
#align dfinsupp.to_finsupp_neg DFinsupp.toFinsupp_neg

@[simp]
theorem toFinsupp_sub [AddGroup M] (f g : Π₀ _ : ι, M) :
    (toFinsupp (f - g) : ι →₀ M) = toFinsupp f - toFinsupp g :=
  rfl
#align dfinsupp.to_finsupp_sub DFinsupp.toFinsupp_sub

@[simp]
theorem toFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M]
    (r : R) (f : Π₀ _ : ι, M) : (toFinsupp (r • f) : ι →₀ M) = r • toFinsupp f :=
  rfl
#align dfinsupp.to_finsupp_smul DFinsupp.toFinsupp_smul

end DFinsupp

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `Finsupp.toDFinsupp` and `DFinsupp.toFinsupp` together form an equiv. -/
@[simps (config := .asFn)]
def finsuppEquivDFinsupp [Zero M] : (ι →₀ M) ≃ Π₀ _ : ι, M where
  toFun := Finsupp.toDFinsupp
  invFun := DFinsupp.toFinsupp
  left_inv := Finsupp.toDFinsupp_toFinsupp
  right_inv := DFinsupp.toFinsupp_toDFinsupp
#align finsupp_equiv_dfinsupp finsuppEquivDFinsupp

/-- The additive version of `Finsupp.toDFinsupp`. -/
@[simps (config := .asFn)]
def finsuppAddEquivDFinsupp [AddZeroClass M] :
    (ι →₀ M) ≃+ Π₀ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_add' := Finsupp.toDFinsupp_add }
#align finsupp_add_equiv_dfinsupp finsuppAddEquivDFinsupp

variable (R)

/-- The additive version of `Finsupp.toDFinsupp`. -/
-- Porting note: `simps` generated lemmas that did not pass `simpNF` lints, manually added below
--@[simps? (config := .asFn)]
def finsuppLequivDFinsupp [Semiring R] [AddCommMonoid M]  [Module R M] :
    (ι →₀ M) ≃ₗ[R] Π₀ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_smul' := Finsupp.toDFinsupp_smul
    map_add' := Finsupp.toDFinsupp_add }
#align finsupp_lequiv_dfinsupp finsuppLequivDFinsupp

-- Porting note: `simps` generated as `↑(finsuppLequivDFinsupp R).toLinearMap = Finsupp.toDFinsupp`
@[simp]
theorem finsuppLequivDFinsupp_apply_apply [Semiring R] [AddCommMonoid M] [Module R M] :
    (↑(finsuppLequivDFinsupp (M := M) R) : (ι →₀ M) → _) = Finsupp.toDFinsupp := by
  simp only [@LinearEquiv.coe_coe]; rfl

@[simp]
theorem finsuppLequivDFinsupp_symm_apply [Semiring R] [AddCommMonoid M] [Module R M] :
    ↑(LinearEquiv.symm (finsuppLequivDFinsupp (ι := ι) (M := M) R)) = DFinsupp.toFinsupp :=
  rfl

section Sigma

/-! ### Stronger versions of `Finsupp.split` -/

variable {η : ι → Type*} {N : Type*} [Semiring R] [DecidableEq ι]

open Finsupp

/-- `Finsupp.split` is an equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
def sigmaFinsuppEquivDFinsupp [Zero N] : ((Σ i, η i) →₀ N) ≃ Π₀ i, η i →₀ N where
  toFun f :=
    { toFun := split f
      support' :=
        f.support'.map fun ⟨s, hs⟩ => ⟨s.map Sigma.fst, fun i => by
          rw [Classical.or_iff_not_imp_right]
          simp [DFunLike.ext_iff, split_apply]
          exact fun a ha => ⟨a, (hs ⟨i, a⟩).resolve_right ha⟩⟩ }
  invFun f :=
    { toFun := fun ji => f ji.1 ji.2
      support' :=
        f.support'.bind fun ⟨s, hs⟩ =>
          (Trunc.finChoice (fun j : ↥s.toFinset => (f j).support')).map fun sp =>
            ⟨s.toFinset.attach.val.bind fun t => (sp t).val.map (Sigma.mk t.val), fun ⟨i, a⟩ => by
              rw [Classical.or_iff_not_imp_right]
              simp [- Sigma.mk.inj_iff]
              exact fun hia =>
                have hi : i ∈ s := (hs i).resolve_right (mt (DFunLike.congr_fun · _) hia)
                ⟨i, hi, Multiset.mem_attach s.dedup ⟨i, Multiset.mem_dedup.mpr hi⟩,
                  a, ((sp ⟨i, Multiset.mem_toFinset.mpr hi⟩).prop a).resolve_right hia, rfl⟩⟩ }
  left_inv f := by ext; simp [split_apply]
  right_inv f := by ext; simp [split_apply]
#align sigma_finsupp_equiv_dfinsupp sigmaFinsuppEquivDFinsupp

@[simp]
theorem sigmaFinsuppEquivDFinsupp_apply [Zero N] (f : (Σi, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f : ∀ i, η i →₀ N) = Finsupp.split f :=
  rfl
#align sigma_finsupp_equiv_dfinsupp_apply sigmaFinsuppEquivDFinsupp_apply

@[simp]
theorem sigmaFinsuppEquivDFinsupp_symm_apply [Zero N] (f : Π₀ i, η i →₀ N) (s : Σi, η i) :
    (sigmaFinsuppEquivDFinsupp.symm f : (Σi, η i) →₀ N) s = f s.1 s.2 :=
  rfl
#align sigma_finsupp_equiv_dfinsupp_symm_apply sigmaFinsuppEquivDFinsupp_symm_apply

@[simp]
theorem sigmaFinsuppEquivDFinsupp_support [DecidableEq ι] [Zero N] [(x : N) → Decidable (x ≠ 0)]
    [∀ (i : ι) (x : η i →₀ N), Decidable (x ≠ 0)] (f : (Σi, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f).support = Finsupp.splitSupport f := by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm
#align sigma_finsupp_equiv_dfinsupp_support sigmaFinsuppEquivDFinsupp_support

@[simp]
theorem sigmaFinsuppEquivDFinsupp_single [DecidableEq ι] [(i : ι) → DecidableEq (η i)]
    [Zero N] (a : Σi, η i) (n : N) :
    sigmaFinsuppEquivDFinsupp (Finsupp.single a n) =
      @DFinsupp.single _ (fun i => η i →₀ N) _ _ a.1 (Finsupp.single a.2 n) := by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases h : i = j
  · subst h
    simp [split_apply, Finsupp.single_apply]
  suffices Finsupp.single (⟨i, a⟩ : Σ i, η i) n ⟨j, b⟩ = 0 by simp [split_apply, dif_neg h, this]
  have H : (⟨i, a⟩ : Σi, η i) ≠ ⟨j, b⟩ := by simp [h]
  rw [Finsupp.single_apply, if_neg H]
#align sigma_finsupp_equiv_dfinsupp_single sigmaFinsuppEquivDFinsupp_single

-- Without this Lean fails to find the `AddZeroClass` instance on `Π₀ i, (η i →₀ N)`.
attribute [-instance] Finsupp.instZero

@[simp]
theorem sigmaFinsuppEquivDFinsupp_add [AddZeroClass N] (f g : (Σi, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (f + g) =
      (sigmaFinsuppEquivDFinsupp f + sigmaFinsuppEquivDFinsupp g : Π₀ i : ι, η i →₀ N) := by
  ext
  rfl
#align sigma_finsupp_equiv_dfinsupp_add sigmaFinsuppEquivDFinsupp_add

/-- `Finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
def sigmaFinsuppAddEquivDFinsupp [AddZeroClass N] : ((Σ i, η i) →₀ N) ≃+ Π₀ i, η i →₀ N :=
  { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add }
#align sigma_finsupp_add_equiv_dfinsupp sigmaFinsuppAddEquivDFinsupp

attribute [-instance] Finsupp.instAddZeroClass

@[simp]
theorem sigmaFinsuppEquivDFinsupp_smul {R} [Monoid R] [AddMonoid N] [DistribMulAction R N] (r : R)
    (f : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (r • f) = r • sigmaFinsuppEquivDFinsupp f := by
  ext
  rfl
#align sigma_finsupp_equiv_dfinsupp_smul sigmaFinsuppEquivDFinsupp_smul

attribute [-instance] Finsupp.instAddMonoid

/-- `Finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
def sigmaFinsuppLequivDFinsupp [AddCommMonoid N] [Module R N] :
    ((Σ i, η i) →₀ N) ≃ₗ[R] Π₀ i, η i →₀ N :=
    -- Porting note: was
    -- sigmaFinsuppAddEquivDFinsupp with map_smul' := sigmaFinsuppEquivDFinsupp_smul
    -- but times out
  { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add
    map_smul' := sigmaFinsuppEquivDFinsupp_smul }
#align sigma_finsupp_lequiv_dfinsupp sigmaFinsuppLequivDFinsupp

end Sigma

end Equivs
