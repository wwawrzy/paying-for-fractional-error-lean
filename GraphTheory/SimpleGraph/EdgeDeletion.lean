/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Edge Deletion Lemmas for Simple Graphs

Basic lemmas about how edge deletion affects adjacency, degree, and edge count
in finite simple graphs.

## Main results

* `deleteEdges_adj` (re-exported from Mathlib): adjacency characterization
* `degree_deleteEdges_le`: degree can only decrease after edge deletion
* `deleteEdge_degree_of_not_adj`: degree unchanged for non-incident vertices
* `deleteEdge_degree_of_adj`: degree decreases by 1 for incident vertices
* `edgeFinset_card_deleteEdge`: edge count decreases by 1
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ### Adjacency after deletion

`SimpleGraph.deleteEdges_adj` is already a `@[simp]` lemma in Mathlib:
  `(G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s`

We re-export it here for discoverability.
-/

-- Mathlib already provides:
-- @[simp] lemma deleteEdges_adj :
--   (G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ s(v, w) ∉ s

/-! ### Degree monotonicity -/

section Degree

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

open Classical in
/-- Deleting edges can only decrease the degree of any vertex. -/
theorem degree_deleteEdges_le (s : Set (Sym2 V)) (v : V) :
    (G.deleteEdges s).degree v ≤ G.degree v :=
  degree_le_of_le (deleteEdges_le s)

/-- Deleting a single edge {u, w} does not change the degree of a vertex v
    that is different from both u and w. -/
theorem deleteEdge_degree_of_not_adj {u w v : V} (hvu : v ≠ u) (hvw : v ≠ w) :
    (G.deleteEdges {s(u, w)}).degree v = G.degree v := by
  simp only [degree, neighborFinset]
  congr 1
  ext x
  simp only [Set.mem_toFinset, mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · exact fun ⟨hadj, _⟩ => hadj
  · intro hadj
    refine ⟨hadj, ?_⟩
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> contradiction

/-- Deleting an edge {u, w} where G.Adj u w decreases the degree of u by 1. -/
theorem deleteEdge_degree_of_adj {u w : V} (hadj : G.Adj u w) :
    (G.deleteEdges {s(u, w)}).degree u = G.degree u - 1 := by
  have h_finset : (G.deleteEdges {s(u, w)}).neighborFinset u =
      G.neighborFinset u \ {w} := by
    ext x
    simp only [mem_neighborFinset, deleteEdges_adj, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨hx.1, fun heq => by subst heq; exact hx.2 rfl⟩
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro hmem
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
      rcases hmem with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
      · exact hx.2 rfl
      · exact hx.1.ne rfl
  simp only [degree, h_finset]
  rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem]
  rwa [G.mem_neighborFinset]

end Degree

/-! ### Edge count after deletion -/

section EdgeCount

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Deleting a single edge from the edge set decreases the edge count by 1. -/
theorem edgeFinset_card_deleteEdge {e : Sym2 V} (he : e ∈ G.edgeSet) :
    (G.deleteEdges (↑({e} : Finset (Sym2 V)))).edgeFinset.card =
    G.edgeFinset.card - 1 := by
  rw [edgeFinset_deleteEdges, Finset.sdiff_singleton_eq_erase,
    Finset.card_erase_of_mem (mem_edgeFinset.mpr he)]

end EdgeCount

end SimpleGraph
