/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic

/-!
# Dominating Sets in Simple Graphs

A set `D` is a dominating set of a graph `G` if every vertex is either in `D`
or adjacent to some vertex in `D`.

An independent dominating set additionally satisfies Mathlib's
`SimpleGraph.IsIndepSet` predicate.  For girth we deliberately reuse Mathlib's
`SimpleGraph.egirth : ℕ∞`: it is the length of a shortest cycle and is `⊤`
exactly for acyclic graphs (`SimpleGraph.egirth_eq_top`).
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A set `D` is a dominating set if every vertex is in `D` or adjacent to some vertex in `D`. -/
def IsDominatingSet (D : Set V) : Prop :=
  ∀ v : V, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

/-- An **independent dominating set** is both dominating and independent. -/
def IsIndependentDominatingSet (D : Set V) : Prop :=
  G.IsDominatingSet D ∧ G.IsIndepSet D

variable {G}

theorem IsDominatingSet.univ : G.IsDominatingSet Set.univ :=
  fun v ↦ Or.inl (Set.mem_univ v)

theorem IsDominatingSet.mono {D D' : Set V} (hD : G.IsDominatingSet D)
    (h : D ⊆ D') : G.IsDominatingSet D' :=
  fun v ↦ (hD v).elim
    (fun hv ↦ Or.inl (h hv))
    (fun ⟨w, hw, hadj⟩ ↦ Or.inr ⟨w, h hw, hadj⟩)

/-- An independent dominating set is a dominating set. -/
theorem IsIndependentDominatingSet.isDominatingSet {D : Set V}
    (hD : G.IsIndependentDominatingSet D) : G.IsDominatingSet D :=
  hD.1

/-- An independent dominating set is an independent set. -/
theorem IsIndependentDominatingSet.isIndepSet {D : Set V}
    (hD : G.IsIndependentDominatingSet D) : G.IsIndepSet D :=
  hD.2

theorem isDominatingSet_iff_forall_not_mem {D : Set V} :
    G.IsDominatingSet D ↔ ∀ v : V, v ∉ D → ∃ w ∈ D, G.Adj v w :=
  Iff.intro
    (fun hD v hv ↦ (hD v).elim (fun h ↦ absurd h hv) id)
    (fun hD v ↦ Classical.or_iff_not_imp_left.mpr (hD v))

theorem isDominatingSet_iff_inter_closedNbhd {D : Set V} :
    G.IsDominatingSet D ↔
      ∀ v : V, (D ∩ ({v} ∪ G.neighborSet v)).Nonempty :=
  Iff.intro
    (fun hD v ↦ (hD v).elim
      (fun hv ↦ ⟨v, hv, Set.mem_union_left _ rfl⟩)
      (fun ⟨w, hw, hadj⟩ ↦ ⟨w, hw, Set.mem_union_right _ hadj⟩))
    (fun hD v ↦
      Exists.elim (hD v) fun w p ↦
        p.2.elim
          (fun h ↦ Or.inl (h.subst p.1))
          (fun h ↦ Or.inr ⟨w, p.1, h⟩))

end SimpleGraph
