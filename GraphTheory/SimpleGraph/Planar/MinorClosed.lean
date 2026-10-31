/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Planar.Basic
import GraphTheory.SimpleGraph.Minor.Closed
import GraphTheory.SimpleGraph.VertexDeletion
import GraphTheory.SimpleGraph.EdgeDeletion
import GraphTheory.SimpleGraph.Minor.Contraction
import Mathlib.Tactic

/-!
# Planarity is Closed under Minors and Subgraphs

This file collects and re-exports the closure properties of planarity under
the standard graph operations: subgraphs, induced subgraphs, edge deletion,
vertex deletion, edge contraction, and minors.

Most of these results are proved from the axioms in `Planar.lean` and
`MinorClosed.lean`. The new results here are:

* `IsPlanar.deleteEdges` — planarity is closed under edge deletion (from `mono`)
* `IsPlanar.deleteVertex` — planarity is closed under vertex deletion (from `induce`)
* `IsPlanar.contractEdge` — planarity is closed under edge contraction (axiomatized)

## Re-exported results

* `SimpleGraph.IsPlanar.mono` — planarity closed under subgraphs (from `Planar.lean`)
* `SimpleGraph.IsPlanar.induce` — planarity closed under induced subgraphs (from `Planar.lean`)
* `SimpleGraph.IsPlanar.minor` — planarity closed under minors (from `MinorClosed.lean`)
* `SimpleGraph.isPlanar_isMinorClosed` — planarity is a minor-closed property (from `MinorClosed.lean`)

## References

* Diestel, *Graph Theory*, 5th ed., Proposition 4.4.6
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-! ### Planarity closed under edge deletion -/

/-- Planarity is closed under edge deletion: if `G` is planar and we delete
any set of edges, the resulting graph is still planar.

**Proof:** `G.deleteEdges s ≤ G` (fewer edges), so this follows from `IsPlanar.mono`. -/
theorem IsPlanar.deleteEdges {G : SimpleGraph V} (hG : IsPlanar G)
    (s : Set (Sym2 V)) : IsPlanar (G.deleteEdges s) :=
  hG.mono (deleteEdges_le s)

/-- Planarity is closed under deleting a single edge. -/
theorem IsPlanar.deleteEdge {G : SimpleGraph V} (hG : IsPlanar G)
    (e : Sym2 V) : IsPlanar (G.deleteEdges {e}) :=
  hG.deleteEdges {e}

/-! ### Planarity closed under vertex deletion -/

/-- Planarity is closed under vertex deletion: if `G` is planar, then the
induced subgraph on `{v}ᶜ` is also planar.

**Proof:** `G.induce {v}ᶜ` is an induced subgraph of `G`, so this follows
from `IsPlanar.induce`. -/
theorem IsPlanar.deleteVertex {G : SimpleGraph V} (hG : IsPlanar G)
    (v : V) : IsPlanar (G.induce ({v}ᶜ : Set V)) :=
  hG.induce {v}ᶜ

/-- Planarity is closed under deleting any set of vertices. -/
theorem IsPlanar.deleteVertices {G : SimpleGraph V} (hG : IsPlanar G)
    (s : Set V) : IsPlanar (G.induce sᶜ) :=
  hG.induce sᶜ

/-! ### Planarity closed under edge contraction -/

/-- Planarity is closed under edge contraction: if `G` is planar and `{u, v}`
is an edge, then the contracted graph `G / {u,v}` is also planar.

**Proof:** We construct a minor model of `contrGraph G u v` in `G`. Each quotient
class `q` maps to its preimage `{ w | contrMk u v w = q }`. These preimages are
nonempty (quotient surjectivity), pairwise disjoint (trivially), connected (each
class is either a singleton or `{u,v}` which are adjacent), and adjacency is
preserved by the definition of `contrGraph`. Then `IsPlanar` transfers via
`IsHMinorFree.minor`. -/
theorem IsPlanar.contractEdge {G : SimpleGraph V} [DecidableEq V]
    (hG : IsPlanar G) {u v : V} (hadj : G.Adj u v) :
    IsPlanar (EdgeContraction.contrGraph G u v) := by
  -- Helper: elements in the same EqvGen class are equal or are {u, v}
  have pairRel_cases : ∀ {a b : V},
      Relation.EqvGen (EdgeContraction.PairRel u v) a b → a ≠ b →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
    intro a b h hab
    induction h with
    | rel x y hxy =>
      unfold EdgeContraction.PairRel at hxy
      exact hxy
    | refl => exact absurd rfl hab
    | symm _ _ _ ih =>
      rcases ih (Ne.symm hab) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    | trans x y z _ _ ih₁ ih₂ =>
      by_cases hxy : x = y
      · subst hxy; exact ih₂ hab
      · by_cases hyz : y = z
        · subst hyz; exact ih₁ hxy
        · -- x ≠ y and y ≠ z, both are {u,v} pairs
          rcases ih₁ hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          rcases ih₂ hyz with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · -- x=u,y=v,y=u,z=v => v=u contradiction (G.Adj is irrefl)
            exfalso; exact hadj.ne (h2.symm.trans h3).symm
          · -- x=u,y=v,y=v,z=u => x=z contradiction
            exfalso; exact hab (h1 ▸ h4 ▸ rfl)
          · -- x=v,y=u,y=u,z=v => x=z contradiction
            exfalso; exact hab (h1 ▸ h4 ▸ rfl)
          · -- x=v,y=u,y=v,z=u => u=v contradiction
            exfalso; exact hadj.ne (h2.symm.trans h3)
  -- Helper: contrMk u v w = ⟦w⟧ under the contrSetoid
  have contrMk_eq_mk : ∀ w : V,
      EdgeContraction.contrMk u v w =
      @Quotient.mk V (EdgeContraction.contrSetoid u v) w := by
    intro w; rfl
  -- Build the minor model
  have hminor : EdgeContraction.contrGraph G u v ≤m G := ⟨{
    branchSet := fun q => { w : V | EdgeContraction.contrMk u v w = q }
    nonempty := by
      intro q
      obtain ⟨w, rfl⟩ := q.exists_rep
      exact ⟨w, by simp [Set.mem_setOf_eq, contrMk_eq_mk]⟩
    disjoint := by
      intro q₁ q₂ hne
      rw [Set.disjoint_left]
      intro w hw₁ hw₂
      simp only [Set.mem_setOf_eq] at hw₁ hw₂
      exact hne (hw₁ ▸ hw₂)
    connected := by
      intro q
      obtain ⟨rep, hrep⟩ := q.exists_rep
      have hrep' : EdgeContraction.contrMk u v rep = q := by
        rw [contrMk_eq_mk]; exact hrep
      rw [connected_iff_exists_forall_reachable]
      refine ⟨⟨rep, by simp [Set.mem_setOf_eq, hrep']⟩, ?_⟩
      intro ⟨w, hw⟩
      simp only [Set.mem_setOf_eq] at hw
      by_cases hwrep : w = rep
      · subst hwrep; exact Reachable.refl _
      · -- w ≠ rep but same class
        have heqv : EdgeContraction.contrMk u v w =
            EdgeContraction.contrMk u v rep := by rw [hw, hrep']
        rw [contrMk_eq_mk, contrMk_eq_mk] at heqv
        have hequiv := Quotient.exact heqv
        rcases pairRel_cases hequiv hwrep with ⟨hwu, hrepv⟩ | ⟨hwv, hrepu⟩
        · -- w = u, rep = v: they are adjacent via hadj
          have hadj_ind : (G.induce
              { w | EdgeContraction.contrMk u v w = q }).Adj
              ⟨rep, hrep'⟩ ⟨w, hw⟩ := by
            change G.Adj rep w
            rw [hwu, hrepv]; exact hadj.symm
          exact ⟨Walk.cons hadj_ind Walk.nil⟩
        · -- w = v, rep = u: they are adjacent via hadj.symm
          have hadj_ind : (G.induce
              { w | EdgeContraction.contrMk u v w = q }).Adj
              ⟨rep, hrep'⟩ ⟨w, hw⟩ := by
            change G.Adj rep w
            rw [hwv, hrepu]; exact hadj
          exact ⟨Walk.cons hadj_ind Walk.nil⟩
    adjacent := by
      intro q₁ q₂ hadj_c
      obtain ⟨_, a, b, ha, hb, hadj_ab⟩ := hadj_c
      exact ⟨a, ha, b, hb, hadj_ab⟩
  }⟩
  exact ⟨IsHMinorFree.minor hG.1 hminor, IsHMinorFree.minor hG.2 hminor⟩

/-! ### Summary: all closure properties -/

section Summary

/-
The following results are available (proved or axiomatized in this file or imports):

1. **Subgraph closure:**       `IsPlanar.mono`        (Planar.lean)
2. **Induced subgraph:**       `IsPlanar.induce`      (Planar.lean)
3. **Edge deletion:**          `IsPlanar.deleteEdges`  (this file, from mono)
4. **Single edge deletion:**   `IsPlanar.deleteEdge`   (this file, from deleteEdges)
5. **Vertex deletion:**        `IsPlanar.deleteVertex`  (this file, from induce)
6. **Vertex set deletion:**    `IsPlanar.deleteVertices` (this file, from induce)
7. **Edge contraction:**       `IsPlanar.contractEdge`  (this file, axiomatized)
8. **Minor closure:**          `IsPlanar.minor`         (MinorClosed.lean)
9. **Minor-closed property:**  `isPlanar_isMinorClosed` (MinorClosed.lean)
-/

end Summary

end SimpleGraph
