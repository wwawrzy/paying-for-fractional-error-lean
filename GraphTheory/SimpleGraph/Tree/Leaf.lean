/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.CycleExistence

/-!
# Leaves in Acyclic Graphs (Diestel Corollary 1.5.3)

We prove that every finite acyclic graph (forest) on a nonempty vertex set
has a vertex of degree ≤ 1. For trees with ≥ 2 vertices, this gives a leaf
(vertex of degree exactly 1).

The proof is by contraposition using `not_isAcyclic_of_two_le_minDegree`:
if every vertex had degree ≥ 2, then the graph would contain a cycle.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-- **Forest minimum degree bound**: A finite acyclic graph has minimum degree ≤ 1. -/
theorem IsAcyclic.minDegree_le_one [Nonempty V] (hac : G.IsAcyclic) :
    G.minDegree ≤ 1 := by
  by_contra h
  push Not at h
  exact not_isAcyclic_of_two_le_minDegree (by omega) hac

/-- **Diestel Corollary 1.5.3 (weak form)**:
    Every finite acyclic graph has a vertex of degree ≤ 1. -/
theorem IsAcyclic.exists_degree_le_one [Nonempty V] (hac : G.IsAcyclic) :
    ∃ v : V, G.degree v ≤ 1 := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  exact ⟨v, hv ▸ hac.minDegree_le_one⟩

/-- **Diestel Section 1.5, leaf deletion**:
    Removing a leaf from a finite tree leaves a tree. -/
theorem IsTree.induce_compl_singleton_of_degree_eq_one
    (hT : G.IsTree) {v : V} (hv : G.degree v = 1) :
    (G.induce {v}ᶜ).IsTree :=
  ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
    hT.isAcyclic.induce _⟩

end SimpleGraph
