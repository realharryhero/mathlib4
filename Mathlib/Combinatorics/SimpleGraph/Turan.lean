/-
Copyright (c) 2024 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Partition.Equipartition
import Mathlib.Tactic.Linarith

/-!
# Turán's theorem

Pass

## Main declarations

* 1NT - 2♣
* 2♠ - 4♠
-/


open Finset

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {s t u : V}

theorem aux1 (hn : ¬G.Adj s t) (hd : G.degree t < G.degree s) :
    G.edgeFinset.card < (G.replaceVertex s t).edgeFinset.card := by
  rw [G.card_edgeFinset_replaceVertex_of_not_adj hn, add_tsub_assoc_of_le hd.le]
  exact Nat.lt_add_of_pos_right <| tsub_pos_iff_lt.mpr hd

theorem aux2 (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) (htu : G.Adj t u)
    (hdt : G.degree s = G.degree t) (hdu : G.degree s = G.degree u) :
    G.edgeFinset.card < ((G.replaceVertex s t).replaceVertex s u).edgeFinset.card := by
  have ntu : t ≠ u := G.ne_of_adj htu
  have nst : s ≠ t := fun a => by subst a; contradiction
  have := (G.adj_replaceVertex_iff_of_ne s t nst ntu.symm).not.mpr hsu
  rw [card_edgeFinset_replaceVertex_of_not_adj _ this,
    card_edgeFinset_replaceVertex_of_not_adj _ hst, hdt, Nat.add_sub_cancel]
  have de1 : (G.replaceVertex s t).degree s = G.degree s := by
    unfold degree; congr 1; ext v
    simp only [mem_neighborFinset, SimpleGraph.irrefl, ite_self]
    by_cases eq : v = t <;> simp_all
  have de2 : (G.replaceVertex s t).degree u = G.degree u - 1 := by
    unfold degree
    rw [← card_singleton t, ← card_sdiff (by simp [htu.symm])]
    congr 1; ext v
    simp only [mem_neighborFinset, mem_sdiff, mem_singleton]
    split_ifs with hu hv hv
    · simp_all
    · simp_all
    · simp [adj_comm, hsu, hv]
    · simp [adj_comm, hsu, hv]
  have dpos : 0 < G.degree u := by
    rw [G.degree_pos_iff_exists_adj u]
    use t
    exact htu.symm
  have dmp : G.degree u - 1 + 1 = G.degree u := Nat.succ_pred_eq_of_pos dpos
  nth_rw 1 [de1, de2, hdu, ← dmp, add_tsub_assoc_of_le (by simp), add_tsub_cancel_left]
  linarith

/-- An `r + 1`-cliquefree graph is `r`-Turán-maximal if any other `r + 1`-cliquefree graph on
the same vertex set has the same or fewer number of edges. -/
def IsTuranMaximal (r : ℕ) :=
  G.CliqueFree (r + 1) ∧ ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
    H.CliqueFree (r + 1) → H.edgeFinset.card ≤ G.edgeFinset.card

variable {r : ℕ}

theorem not_adj_transitive (hmax : G.IsTuranMaximal r) (hst : ¬G.Adj s t) (hsu : ¬G.Adj s u) :
    ¬G.Adj t u := by
  by_cases z : G.degree s = G.degree t ∧ G.degree s = G.degree u <;>
    (contrapose! hmax; unfold IsTuranMaximal; push_neg; intro cf)
  · use (G.replaceVertex s t).replaceVertex s u, inferInstance
    exact ⟨cliqueFree_of_replaceVertex_cliqueFree s u
      (cliqueFree_of_replaceVertex_cliqueFree s t cf), aux2 _ hst hsu hmax z.1 z.2⟩
  · rw [Decidable.not_and] at z
    cases' z with st su
    · cases' lt_or_gt_of_ne st with less more
      · use G.replaceVertex t s, inferInstance
        rw [adj_comm] at hst
        exact ⟨cliqueFree_of_replaceVertex_cliqueFree t s cf, G.aux1 hst less⟩
      · use G.replaceVertex s t, inferInstance
        exact ⟨cliqueFree_of_replaceVertex_cliqueFree s t cf, G.aux1 hst more⟩
    · cases' lt_or_gt_of_ne su with less more
      · use G.replaceVertex u s, inferInstance
        rw [adj_comm] at hsu
        exact ⟨cliqueFree_of_replaceVertex_cliqueFree u s cf, G.aux1 hsu less⟩
      · use G.replaceVertex s u, inferInstance
        exact ⟨cliqueFree_of_replaceVertex_cliqueFree s u cf, G.aux1 hsu more⟩

variable {G} (hmax : G.IsTuranMaximal r)

theorem notAdjEquivalence : Equivalence fun x y => ¬G.Adj x y where
  refl x := by simp
  symm xy := by simp [xy, adj_comm]
  trans xy yz := by
    rw [adj_comm] at xy
    exact G.not_adj_transitive hmax xy yz

/-- In a Turán-maximal graph, non-adjacency is an equivalence relation. -/
def notAdjSetoid : Setoid V := ⟨_, (notAdjEquivalence hmax)⟩

instance : DecidableRel (notAdjSetoid hmax).r :=
  inferInstanceAs <| DecidableRel fun v w => ¬G.Adj v w

/-- The finpartition derived from `notAdjSetoid`. -/
def notAdjFinpartition : Finpartition (univ : Finset V) :=
  Finpartition.ofSetoid (notAdjSetoid hmax)

theorem degree_eq_fintype_card_sub_part_card : G.degree s = Fintype.card V -
    ((notAdjFinpartition hmax).part (mem_univ s)).card := by
  calc
    G.degree s = (univ.filter (fun b => G.Adj s b)).card := by
      simp [← card_neighborFinset_eq_degree, neighborFinset]
    _ = Fintype.card V - (univ.filter (fun b => ¬G.Adj s b)).card :=
      eq_tsub_of_add_eq (filter_card_add_filter_neg_card_eq_card _)
    _ = _ := by
      congr; ext; rw [mem_filter]
      convert (Finpartition.mem_part_ofSetoid_iff_rel).symm
      simp [notAdjSetoid]

theorem notAdj_equipartition : (notAdjFinpartition hmax).IsEquipartition := by
  let fp := notAdjFinpartition hmax
  by_contra hn
  rw [Finpartition.not_isEquipartition] at hn
  obtain ⟨large, hl, small, hs, ineq⟩ := hn
  obtain ⟨w, hw⟩ := fp.nonempty_of_mem_parts hl
  obtain ⟨v, hv⟩ := fp.nonempty_of_mem_parts hs
  have large_eq : large = fp.part (a := w) (mem_univ _) :=
    (fp.existsUnique_mem (a := w) (mem_univ _)).unique
      ⟨hl, hw⟩ ⟨fp.part_mem _, fp.mem_part _⟩
  have small_eq : small = fp.part (a := v) (mem_univ _) :=
    (fp.existsUnique_mem (a := v) (mem_univ _)).unique
      ⟨hs, hv⟩ ⟨fp.part_mem _, fp.mem_part _⟩
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro cf
    use G.replaceVertex v w, inferInstance
    refine' ⟨cliqueFree_of_replaceVertex_cliqueFree v w cf, _⟩
    have ha : G.Adj v w := by
      have lsn : large ≠ small := fun _ => by simp_all only [add_lt_iff_neg_left, not_lt_zero']
      contrapose! lsn
      have : _ ∈ fp.part _ ↔ ¬G.Adj v w := Finpartition.mem_part_ofSetoid_iff_rel
      exact fp.eq_of_mem_parts hl hs hw (small_eq ▸ this.mpr lsn)
    rw [G.card_edgeFinset_replaceVertex_of_adj ha]
    have large_le : large.card ≤ Fintype.card V := by
      simpa using card_le_of_subset large.subset_univ
    have small_le : small.card ≤ Fintype.card V := by
      simpa using card_le_of_subset small.subset_univ
    rw [degree_eq_fintype_card_sub_part_card, ← small_eq,
      degree_eq_fintype_card_sub_part_card, ← large_eq,
      Nat.add_sub_assoc (by rw [tsub_le_tsub_iff_left small_le]; linarith),
      tsub_tsub_tsub_cancel_left large_le, Nat.add_sub_assoc (lt_tsub_iff_left.mpr ineq).le]
    linarith [tsub_pos_iff_lt.mpr (lt_tsub_iff_left.mpr ineq)]
  contradiction

theorem notAdj_card_parts_le : (notAdjFinpartition hmax).parts.card ≤ r := by
  let fp := notAdjFinpartition hmax
  by_contra! h
  -- `z` is an `r + 1`-clique in `G`, contradicting Turán-maximality
  let z := fp.reprs
  have ncf : ¬G.CliqueFree z.card := by
    apply IsNClique.not_cliqueFree (s := z)
    constructor
    swap; · rfl
    intro v hv w hw hn
    norm_cast at hv hw
    contrapose! hn
    exact fp.reprs_injective hv hw (fp.eq_of_mem_parts (fp.part_mem _) (fp.part_mem _)
      (Finpartition.mem_part_ofSetoid_iff_rel.mpr hn) (fp.mem_part _))
  rw [Finpartition.card_reprs] at ncf
  exact absurd (CliqueFree.mono (Nat.succ_le_of_lt h) hmax.1) ncf

theorem notAdj_card_parts : (notAdjFinpartition hmax).parts.card = min (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  apply le_antisymm (le_min fp.card_parts_le_card (notAdj_card_parts_le _))
  by_contra! h
  rw [lt_min_iff] at h
  obtain ⟨x, _, y, _, hn, he⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
    (f := fun a => fp.part (a := a) (by simp)) univ fp.parts h.1 (fun _ _ => fp.part_mem _)
  have : ¬IsTuranMaximal G r := by
    rw [IsTuranMaximal]; push_neg; intro
    use G.addEdge x y, inferInstance
    have cf : G.CliqueFree r := by
      simp_rw [← cliqueFinset_eq_empty_iff, cliqueFinset, filter_eq_empty_iff, mem_univ,
        forall_true_left, isNClique_iff, and_comm, not_and, isClique_iff]
      intro z zc
      obtain ⟨x', xm, y', ym, hn', he'⟩ := @exists_ne_map_eq_of_card_lt_of_maps_to
        (f := fun a => fp.part (a := a) (by simp)) z fp.parts (zc.symm ▸ h.2)
        (fun _ _ => fp.part_mem _)
      unfold Set.Pairwise; push_neg; norm_cast
      use x', xm, y', ym, hn'
      change (notAdjSetoid hmax).r x' y'
      apply Finpartition.mem_part_ofSetoid_iff_rel.mp
      exact he' ▸ fp.mem_part _
    refine' ⟨G.cliqueFree_of_addEdge_cliqueFree x y cf, _⟩
    rw [G.card_edgeFinset_addEdge _ hn]; · linarith
    change (notAdjSetoid hmax).r x y
    apply Finpartition.mem_part_ofSetoid_iff_rel.mp
    exact he ▸ fp.mem_part _
  contradiction

/-- The canonical `r + 1`-cliquefree Turán graph on `n` vertices. -/
def turanGraph (n r : ℕ) : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

/-- **Turán's theorem**. Any `r + 1`-cliquefree Turán-maximal graph on `n` vertices is
isomorphic to `turanGraph n r`. -/
noncomputable def isTuranMaximalIsoTuranGraph : G ≃g turanGraph (Fintype.card V) r := by
  let fp := notAdjFinpartition hmax
  obtain ⟨zm, zp⟩ := (notAdj_equipartition hmax).partPreservingEquiv
  use (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans zm
  intro a b
  simp_rw [turanGraph, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply]
  rw [← not_iff_not]
  change _ ↔ (notAdjSetoid hmax).r a b
  rw [← Finpartition.mem_part_ofSetoid_iff_rel]
  change _ ↔ b ∈ fp.part _
  have pe : b ∈ fp.part (mem_univ a) ↔ fp.part (mem_univ a) = fp.part (mem_univ b) := by
    constructor <;> intro h
    · exact fp.eq_of_mem_parts (fp.part_mem _) (fp.part_mem _) h (fp.mem_part _)
    · rw [h]; exact fp.mem_part _
  rw [pe, zp ⟨a, mem_univ _⟩ ⟨b, mem_univ _⟩, notAdj_card_parts, not_not, min_comm]
  rcases le_or_lt r (Fintype.card V) with h | h
  · rw [min_eq_left h]; rfl
  · rw [min_eq_right h.le]
    have lc : ∀ x, zm ⟨x, _⟩ < Fintype.card V := fun x ↦ (zm ⟨x, mem_univ _⟩).2
    have cn0 : Fintype.card V ≠ 0 := by by_contra h; exact absurd (h ▸ lc a) not_lt_zero'
    have rn0 : r ≠ 0 := by linarith
    rw [(Nat.mod_eq_iff_lt cn0).mpr (lc a), (Nat.mod_eq_iff_lt cn0).mpr (lc b),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc a).trans h),
      ← (Nat.mod_eq_iff_lt rn0).mpr ((lc b).trans h)]
    rfl
