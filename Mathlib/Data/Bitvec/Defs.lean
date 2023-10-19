/-
Copyright (c) 2023 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harun Khan, Alex Keizer, Abdalrhman M Mohamed
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs
import Std.Data.BitVec


/-!
# Basic operations on bitvectors
We define bitvectors. We choose the `Fin` representation over others for its relative efficiency
(Lean has special support for `Nat`), alignment with `UIntXY` types which are also represented
with `Fin`, and the fact that bitwise operations on `Fin` are already defined. Some other possible
representations are `List Bool`, `{ l : List Bool // l.length = w}`, `Fin w → Bool`.

We also define many bitvector operations from the
[`QF_BV` logic](https://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV).
of SMT-LIBv2.
-/

variable {w v : Nat}

namespace Std.BitVec

#align bitvec Std.BitVec
#align bitvec.zero Std.BitVec.zero
#align bitvec.cong Std.BitVec.cast
#align bitvec.append Std.BitVec.append
#align bitvec.shl Std.BitVec.shiftLeft
#align bitvec.ushr Std.BitVec.ushiftRight
#align bitvec.sshr Std.BitVec.sshiftRight
#align bitvec.not Std.BitVec.not
#align bitvec.and Std.BitVec.and
#align bitvec.or Std.BitVec.or
#align bitvec.xor Std.BitVec.xor
#align bitvec.neg Std.BitVec.neg
#align bitvec.add Std.BitVec.add
#align bitvec.sub Std.BitVec.sub
#align bitvec.mul Std.BitVec.mul
#align bitvec.ult Std.BitVec.ult
#align bitvec.ule Std.BitVec.ule
#align bitvec.slt Std.BitVec.slt
#align bitvec.sle Std.BitVec.sle
#align bitvec.of_nat Std.BitVec.ofNat
#align bitvec.add_lsb Nat.bit
#align bitvec.to_nat Std.BitVec.toNat
#align bitvec.of_fin Std.BitVec.ofFin
#align bitvec.to_fin Std.BitVec.toFin
#align bitvec.to_int Std.BitVec.toInt

#noalign bitvec.one
#noalign bitvec.adc
#noalign bitvec.sbb
#noalign bitvec.uborrow
#noalign bitvec.sborrow
#noalign bitvec.bits_to_nat



/-!
## Bitwise operations
-/

/-- Signed greater than for bitvectors. -/
protected def sgt (x y : BitVec w) : Prop := BitVec.slt y x
#align bitvec.sgt Std.BitVec.sgt

/-- Signed greater than or equal to for bitvectors. -/
protected def sge (x y : BitVec w) : Prop := BitVec.sle y x
#align bitvec.sge Std.BitVec.sge

/-- Unsigned greater than for bitvectors. -/
protected def ugt (x y : BitVec w) : Prop := BitVec.ult y x
#align bitvec.ugt Std.BitVec.ugt

/-- Signed greater than or equal to for bitvectors. -/
protected def uge (x y : BitVec w) : Prop := BitVec.ule y x
#align bitvec.uge Std.BitVec.uge

/-! We add simp-lemmas that rewrite bitvector operations into the equivalent notation -/
@[simp] lemma append_eq (x : BitVec w) (y : BitVec v)   : BitVec.append x y = x ++ y        := rfl
@[simp] lemma shiftLeft_eq (x : BitVec w) (n: Nat)      : BitVec.shiftLeft x n = x <<< n    := rfl
@[simp] lemma ushiftRight_eq (x : BitVec w) (n: Nat)    : BitVec.ushiftRight x n = x >>> n  := rfl
@[simp] lemma not_eq (x : BitVec w)                     : BitVec.not x = ~~~x               := rfl
@[simp] lemma and_eq (x y : BitVec w)                   : BitVec.and x y = x &&& y          := rfl
@[simp] lemma or_eq (x y : BitVec w)                    : BitVec.or x y = x ||| y           := rfl
@[simp] lemma xor_eq (x y : BitVec w)                   : BitVec.xor x y = x ^^^ y          := rfl
@[simp] lemma neg_eq (x : BitVec w)                     : BitVec.neg x = -x                 := rfl
@[simp] lemma add_eq (x y : BitVec w)                   : BitVec.add x y = x + y            := rfl
@[simp] lemma sub_eq (x y : BitVec w)                   : BitVec.sub x y = x - y            := rfl
@[simp] lemma mul_eq (x y : BitVec w)                   : BitVec.mul x y = x * y            := rfl

/-- Convert a list of booleans to a bitvector. -/
def ofList (bs : List Bool) : BitVec bs.length :=
  ⟨Nat.ofBits (λ i => bs[i]!) 0 bs.length, @Nat.ofBits_lt _ (bs.length)⟩


end Std.BitVec
