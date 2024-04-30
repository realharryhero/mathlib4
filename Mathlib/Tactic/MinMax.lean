/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Lean.Elab.Command
import Mathlib.Order.Notation
/-!
#  `toTop` a command to convert from `Bot` to `Top`

If `thm` is a theorem about `WithBot`, then `toTop thm` tries to add to the
environment the analogous result about `WithTop`.
-/

open Lean Elab Command

namespace Mathlib.ToNatDegree

/-- the core of the string translation.  These replacements are applied to individual "segments"
after grouping words and splitting further at uppercase letter. -/
abbrev segmentReplacements : HashMap String String := HashMap.empty
  |>.insert "⊥"      "⊤"
  |>.insert "max"    "min"
  |>.insert "Sup"    "Inf"
  |>.insert "sup"    "inf"
  |>.insert "Bot"    "Top"
  |>.insert "bot"    "top"
  |>.insert "unbot"  "untop"
  |>.insert "union"  "inter"
  |>.insert "inter"  "union"

/-- splits a string into maximal substrings consisting of either `[uppercase]*[lowercase]*` or
`[non-alpha]*`. -/
def splitUpper (s : String) : List String :=
  s.toList.groupBy (fun a b => a.isUpper || (a.isLower && b.isLower)) |>.map (⟨·⟩)

/-- replaces "words" in a string using `segmentReplacements`.  It breaks the string into "words"
grouping together maximal consecutive substrings consisting of
either `[uppercase]*[lowercase]*` or `[non-alpha]*`. -/
def stringReplacements (str : String) : String :=
  let strs := (splitUpper str).map fun s => (segmentReplacements.find? s).getD s
  String.join <| strs

/-- some binary operations need to be reversed in the change `Bot` to `Top`, others stay unchanged.
`binopReplacements` performs some of these changes. -/
partial
def binopReplacements {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] (stx : Syntax) :
    m Syntax :=
  stx.replaceM fun s => do
    match s with
      | `(term| antisymm $ha $hb) => return some (← `($(mkIdent `antisymm) $hb $ha))
      | `(term| le_trans $ha $hb) => return some (← `($(mkIdent `le_trans) $hb $ha))
      | `(term| lt_trans $ha $hb) => return some (← `($(mkIdent `lt_trans) $hb $ha))
      | `(term| $ha ⊔ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ⊓ $hb'))
      | `(term| $ha ∪ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ∩ $hb'))
      | `(term| $ha ∩ $hb) =>
        let ha' := ⟨← binopReplacements ha⟩
        let hb' := ⟨← binopReplacements hb⟩
        return some (← `(term| $ha' ∪ $hb'))
      | _ => return none

/-- some names have consecutive parts that should be transposed.
`lelt` is one of the two parts. -/
abbrev lelt : HashSet String := { "le", "lt" }

/-- some names have consecutive parts that should be transposed.
`leftRight` is one of the two parts. -/
abbrev leftRight : HashSet String := { "left", "right", "sup", "inf", "inter", "union", "none" }

/-- `swapWords` uses `lelt` and `leftRight` to perform the swap in names.
E.g. it replaces `["none", "le"]` with `["le", "none"]`. -/
def swapWords : List String → List String
  | le::left::ls =>
    if ((lelt.contains le) && (leftRight.contains left)) ||
       ((lelt.contains left) && (leftRight.contains le))
    then left::le::(swapWords ls)
    else le::swapWords (left :: ls)
  | e => e

/-- converts a name involving `WithBot` to a name involving `WithTop`. -/
def nameToTop : Name → Name
  | .str a b => .str (nameToTop a) (stringReplacements b)
  | _ => default

/-- converts a statement involving `WithBot` to a name involving `WithTop`. -/
def toTop (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s.getId with
      | .anonymous => return none
      | v => return some (mkIdent (nameToTop v))

/-- converts `WithBot _` to `ℕ∞` and `⊥` to `⊤`.
Useful when converting a `degree` with values in `WithBot ℕ` to a `trailingDegree` with values
in `ℕ∞`. -/
def MaxToMin (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    match s with
--      | .node _ ``Lean.Parser.Term.app #[.ident _ _ `WithBot _, _] =>
--        return some (← `(ℕ∞))
      | .node _ ``Lean.Parser.Term.app #[.ident _ _ na _, .node _ _ #[hb]] =>
        match na with
          | .str ha "antisymm" => return some (← `($(mkIdent `antisymm) $(mkIdent ha) $(⟨hb⟩)))
          | .str ha "trans_le" => return some (← `($(mkIdent `lt_of_le_of_lt) $(⟨hb⟩) $(mkIdent ha)))
          | _ => return none
--      | .node _ `«term⊔» #[.atom _ "⊔"] => return some (← `(⊓))
      | .node _ `«term⊥» #[.atom _ "⊥"] => return some (← `((⊤ : $(mkIdent `WithTop) _)))
      | .atom _ s =>
        if s.contains '⊥' then return some (mkAtom (s.replace "⊥" "⊤")) else return none
      | .node _ `«term_≤_» #[a, _, b] => return some (← `($(⟨b⟩) ≤ $(⟨a⟩)))
      | .node _ `«term_<_» #[a, _, b] => return some (← `($(⟨b⟩) < $(⟨a⟩)))
      | .node _ ``Lean.Parser.Command.docComment #[init, .atom _ docs] =>
        let newDocs := stringReplacements docs
        let newDocs :=
          if newDocs == docs
          then "[recycled by `toTop`] " ++ docs
          else "[autogenerated by `toTop`] " ++ newDocs
        let nd := mkNode ``Lean.Parser.Command.docComment #[init, mkAtom newDocs]
        return some nd
      | _ => return none

/--
If `thm` is a theorem about `WithBot`, then `toTop thm` tries to add to the
environment the analogous result about `WithTop`.

Writing `toTop?` also prints the extra declaration added by `toTop`.
-/
elab (name := toTopCmd) "toTop " tk:"?"? cmd:command : command => do
  let newCmd ← binopReplacements <| ← MaxToMin <| ← toTop cmd
  if tk.isSome then logInfo m!"-- adding\n{newCmd}"
  elabCommand cmd
  let currNS ← getCurrNamespace

  withScope (fun s => { s with currNamespace := nameToTop currNS } ) <| elabCommand newCmd

@[inherit_doc toTopCmd]
macro "toTop? " cmd:command : command => return (← `(toTop ? $cmd))
