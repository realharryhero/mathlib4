/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib
import Mathlib.Tactic.LibraryRewrite

/-!
# Saving the library rewrites cache.

After importing of mathlib, we build a library rewrites cache and pickle it to disk.
This file will be distributed via our Azure storage.
-/

open Lean.Elab.Command
open Mathlib.Tactic.LibraryRewrite

run_cmd liftTermElabM do
  let path ← cachePath
  _ ← path.parent.mapM fun p => IO.FS.createDirAll p
  pickle path (← (← RewriteCache.mk).get) `LibraryRewrites
