/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Vertex Deletion Lemmas for Simple Graphs (Diestel 1.1)

Basic lemmas about how deleting a vertex `v` from a graph `G` affects
the induced subgraph `G - v`, degrees, and edge counts.

We model `G - v` as the subgraph of `G` induced on the complement of `{v}`,
using `SimpleGraph.Subgraph.induce` on the top subgraph.

## Main results

* `vertexDeletion_verts`: vertex set of `G.vertexDeletion v` is `{v}ᶜ`
* `vertexDeletion_adj`: adjacency in `G.vertexDeletion v`
* `vertexDeletion_neighborSet`: neighbor set in `G.vertexDeletion v` for `u ≠ v`
* `degree_vertexDeletion_le`: degree in G-v is at most degree in G
* `degree_vertexDeletion_of_not_adj`: degree unchanged for non-neighbors of `v`
* `degree_vertexDeletion_of_adj`: degree decreases by 1 for neighbors of `v`
* `edgeFinset_card_vertexDeletion`: edge count decreases by `deg(v)`
-/

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-! ### Definition of G - v -/

/-- The graph obtained by deleting vertex `v` from `G`:
    the subgraph of `G` induced on all vertices except `v`. -/
noncomputable def vertexDeletion (G : SimpleGraph V) (v : V) : G.Subgraph :=
  (⊤ : G.Subgraph).induce {v}ᶜ

/-! ### Basic properties -/

/-- The vertex set of `G.vertexDeletion v` is `{v}ᶜ`. -/
@[simp]
theorem vertexDeletion_verts (G : SimpleGraph V) (v : V) :
    (G.vertexDeletion v).verts = {v}ᶜ :=
  Subgraph.induce_verts _ _

/-- Adjacency in `G.vertexDeletion v`: both endpoints must differ from `v`
    and be adjacent in `G`. -/
@[simp]
theorem vertexDeletion_adj {v u w : V} :
    (G.vertexDeletion v).Adj u w ↔ u ≠ v ∧ w ≠ v ∧ G.Adj u w := by
  simp only [vertexDeletion, Subgraph.induce_adj, Subgraph.top_adj,
             Set.mem_compl_iff, Set.mem_singleton_iff]

/-- The neighbor set of `u ≠ v` in `G.vertexDeletion v` equals
    the neighbors of `u` in `G` minus `{v}`. -/
theorem vertexDeletion_neighborSet {v u : V} (huv : u ≠ v) :
    (G.vertexDeletion v).neighborSet u = G.neighborSet u \ {v} := by
  ext w
  simp only [Subgraph.mem_neighborSet, vertexDeletion_adj, Set.mem_diff,
             Set.mem_singleton_iff, mem_neighborSet]
  constructor
  · intro h; exact ⟨h.2.2, h.2.1⟩
  · intro h; exact ⟨huv, h.2, h.1⟩

/-- `v` is not in its own deletion. -/
theorem not_mem_vertexDeletion_verts (G : SimpleGraph V) (v : V) :
    v ∉ (G.vertexDeletion v).verts := by
  simp [Set.mem_compl_iff]

/-- Any vertex `u ≠ v` is in the vertex set of `G.vertexDeletion v`. -/
theorem mem_vertexDeletion_verts {v u : V} (huv : u ≠ v) :
    u ∈ (G.vertexDeletion v).verts := by
  simp [Set.mem_compl_iff, huv]

/-- Adjacency in `G` between vertices different from `v` implies adjacency
    in `G.vertexDeletion v`. -/
theorem adj_vertexDeletion_of_adj {v u w : V} (huv : u ≠ v) (hwv : w ≠ v)
    (hadj : G.Adj u w) : (G.vertexDeletion v).Adj u w := by
  rw [vertexDeletion_adj]
  exact ⟨huv, hwv, hadj⟩

/-- Adjacency in `G.vertexDeletion v` implies adjacency in `G`. -/
theorem adj_of_adj_vertexDeletion {v u w : V}
    (h : (G.vertexDeletion v).Adj u w) : G.Adj u w := by
  rw [vertexDeletion_adj] at h
  exact h.2.2

/-! ### Degree after vertex deletion -/

section Degree

variable [Fintype V] [DecidableRel G.Adj]

-- Provide Fintype instance for neighborSet of vertexDeletion via Classical.
private noncomputable instance fintypeVertexDeletionNeighborSet
    (v u : V) : Fintype ↑((G.vertexDeletion v).neighborSet u) := by
  classical
  infer_instance

/-- The degree of any vertex in `G.vertexDeletion v` is at most its degree in `G`.
    This follows directly from Mathlib's `Subgraph.degree_le`. -/
theorem degree_vertexDeletion_le (v u : V) :
    (G.vertexDeletion v).degree u ≤ G.degree u :=
  Subgraph.degree_le _ _

/-- If `u ≠ v` is not adjacent to `v` in `G`, deleting `v` does not change
    the degree of `u`. -/
theorem degree_vertexDeletion_of_not_adj {v u : V} (huv : u ≠ v)
    (hnadj : ¬G.Adj u v) :
    (G.vertexDeletion v).degree u = G.degree u := by
  have hv_not_in : v ∉ G.neighborSet u := by
    simp only [mem_neighborSet]; exact hnadj
  have heq : (G.vertexDeletion v).neighborSet u = G.neighborSet u := by
    rw [vertexDeletion_neighborSet huv]
    exact Set.diff_singleton_eq_self hv_not_in
  unfold Subgraph.degree
  rw [show Fintype.card ↑((G.vertexDeletion v).neighborSet u) =
      Fintype.card ↑(G.neighborSet u) from Fintype.card_congr (Equiv.setCongr heq)]
  rw [← Set.toFinset_card]
  exact (card_neighborFinset_eq_degree G u).symm

/-- If `G.Adj u v`, then deleting `v` decreases the degree of `u` by 1. -/
theorem degree_vertexDeletion_of_adj {v u : V} (hadj : G.Adj u v) :
    (G.vertexDeletion v).degree u = G.degree u - 1 := by
  have huv : u ≠ v := hadj.ne
  have hset : (G.vertexDeletion v).neighborSet u = G.neighborSet u \ {v} :=
    vertexDeletion_neighborSet huv
  have hmem : v ∈ G.neighborSet u := by
    simp only [mem_neighborSet]; exact hadj
  unfold Subgraph.degree
  rw [show Fintype.card ↑((G.vertexDeletion v).neighborSet u) =
      Fintype.card ↑(G.neighborSet u \ {v}) from Fintype.card_congr (Equiv.setCongr hset)]
  rw [← Set.toFinset_card (G.neighborSet u \ {v})]
  rw [Set.toFinset_diff, Set.toFinset_singleton]
  rw [Finset.card_sdiff]
  have hinter : {v} ∩ (G.neighborSet u).toFinset = {v} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Set.mem_toFinset]
    constructor
    · intro ⟨h, _⟩; exact h
    · intro h; exact ⟨h, h ▸ hmem⟩
  rw [hinter, Finset.card_singleton]
  rw [← card_neighborFinset_eq_degree, neighborFinset_def]

end Degree

/-! ### Edge count after vertex deletion -/

section EdgeCount

variable [Fintype V] [DecidableRel G.Adj]

/-- The edge set of `G.vertexDeletion v` equals the edge set of
    `G.deleteIncidenceSet v`. -/
private theorem vertexDeletion_edgeSet_eq (v : V) :
    (G.vertexDeletion v).edgeSet = (G.deleteIncidenceSet v).edgeSet := by
  ext e
  refine e.ind ?_
  intro a b
  simp only [Subgraph.mem_edgeSet, vertexDeletion_adj, mem_edgeSet,
    deleteIncidenceSet_adj]
  tauto

/-- The number of edges in `G.vertexDeletion v` equals `|E(G)| - deg(v)`. -/
theorem edgeFinset_card_vertexDeletion (v : V) :
    (G.vertexDeletion v).edgeSet.toFinset.card = G.edgeFinset.card - G.degree v := by
  have heq : (G.vertexDeletion v).edgeSet = (G.deleteIncidenceSet v).edgeSet :=
    vertexDeletion_edgeSet_eq v
  have h1 : (G.vertexDeletion v).edgeSet.toFinset.card =
      (G.deleteIncidenceSet v).edgeFinset.card := by
    congr 1
    ext e
    simp only [Set.mem_toFinset, mem_edgeFinset]
    exact heq ▸ Iff.rfl
  rw [h1, card_edgeFinset_deleteIncidenceSet]

end EdgeCount

end SimpleGraph
