/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Simon Hudon
-/
import Mathlib.Control.Random
import Mathlib.Control.ULiftable
import Mathlib.Data.List.Perm
import Mathlib.Data.Subtype
import Mathlib.Data.Nat.Basic

#align_import testing.slim_check.gen from "leanprover-community/mathlib"@"fdc286cc6967a012f41b87f76dcd2797b53152af"

/-!
# `Gen` Monad

This monad is used to formulate randomized computations with a parameter
to specify the desired size of the result.
This is a port of the Haskell QuickCheck library.

## Main definitions

* `Gen` monad

## Tags

random testing

## References

* https://hackage.haskell.org/package/QuickCheck
-/

namespace SlimCheck

open Random

/-- Monad to generate random examples to test properties with.
It has a `Nat` parameter so that the caller can decide on the
size of the examples. -/
abbrev Gen (m : Type u → Type u) (α : Type u) := ReaderT (ULift Nat) (Rand m) α

instance [MonadLift m n] : MonadLiftT (Gen m) (Gen n) where
  monadLift x := fun s => x s

namespace Gen

variable [Monad m]

/-- Lift `Random.random` to the `Gen` monad. -/
def chooseAny (α : Type u) [Random α] : Gen m α :=
  λ _ => rand α

/-- Lift `BoundedRandom.randomR` to the `Gen` monad. -/
def choose (α : Type u) [Preorder α] [BoundedRandom α] (lo hi : α) (h : lo ≤ hi) :
    Gen m {a // lo ≤ a ∧ a ≤ hi} :=
  λ _ => randBound α lo hi h

lemma chooseNatLt_aux {lo hi : Nat} (a : Nat) (h : Nat.succ lo ≤ a ∧ a ≤ hi) :
    lo ≤ Nat.pred a ∧ Nat.pred a < hi :=
  And.intro (Nat.le_pred_of_lt (Nat.lt_of_succ_le h.left)) <|
    show a.pred.succ ≤ hi by
       rw [Nat.succ_pred_eq_of_pos]
       exact h.right
       exact lt_of_le_of_lt (Nat.zero_le lo) h.left

/-- Generate a `Nat` example between `x` and `y` (exclusively). -/
def chooseNatLt (lo hi : Nat) (h : lo < hi) : Gen m {a // lo ≤ a ∧ a < hi} :=
  Subtype.map Nat.pred chooseNatLt_aux <$> choose Nat (lo.succ) hi (Nat.succ_le_of_lt h)

/-- Get access to the size parameter of the `Gen` monad. -/
def getSize : Gen m Nat :=
  return (← read).down

/-- Apply a function to the size parameter. -/
def resize (f : Nat → Nat) (x : Gen m α) : Gen m α :=
  withReader (ULift.up ∘ f ∘ ULift.down) x

variable {α : Type u}

/-- Create an `Array` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def arrayOf (x : Gen m α) : Gen m (Array α) := do
  let ⟨sz⟩ ← (ULiftable.up <| do choose Nat 0 (←getSize) (Nat.zero_le _) : Gen m (ULift ℕ))
  let mut res := #[]
  for _ in [0:sz] do
    res := res.push (← x)
  pure res

/-- Create a `List` of examples using `x`. The size is controlled
by the size parameter of `Gen`. -/
def listOf (x : Gen m α) : Gen m (List α) :=
  arrayOf x >>= pure ∘ Array.toList

/-- Given a list of example generators, choose one to create an example. -/
def oneOf (xs : Array (Gen m α)) (pos : 0 < xs.size := by decide) : Gen m α := do
  let ⟨x, _, h2⟩ ← ULiftable.up <| chooseNatLt 0 xs.size pos
  xs.get ⟨x, h2⟩

/-- Given a list of examples, choose one to create an example. -/
def elements (xs : List α) (pos : 0 < xs.length) : Gen m α := do
  let ⟨x, _, h2⟩ ← ULiftable.up <| chooseNatLt 0 xs.length pos
  pure $ xs.get ⟨x, h2⟩

open List in
/-- Generate a random permutation of a given list. -/
def permutationOf : (xs : List α) → Gen m { ys // ys ~ xs }
  | [] => pure ⟨[], Perm.nil⟩
  | x::xs => do
    let ⟨ys, h1⟩ ← permutationOf xs
    let ⟨n, _, h3⟩ ← ULiftable.up <| choose Nat 0 ys.length (Nat.zero_le _)
    pure ⟨insertNth n x ys, Perm.trans (Perm.cons _ h1) (perm_insertNth _ _ h3).symm⟩

/-- Given two generators produces a tuple consisting out of the result of both -/
def prodOf {α β : Type u} (x : Gen m α) (y : Gen m β) : Gen m (α × β) := do
  let ⟨a⟩ ← (ULiftable.up x : Gen m (ULift.{max u v} α))
  let ⟨b⟩ ← (ULiftable.up y : Gen m (ULift.{max u v} β))
  pure (a, b)

end Gen

variable {m : Type _ → Type _} [Monad m] [MonadLiftT (ST IO.RealWorld) m]

/-- Execute a `Gen` inside the monad using `size` as the example size-/
def Gen.run (x : Gen m α) (size : Nat) : m α :=
  runRand $ ReaderT.run x ⟨size⟩

end SlimCheck
