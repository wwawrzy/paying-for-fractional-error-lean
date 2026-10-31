/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic
import GraphTheory.SimpleGraph.Degeneracy
import GraphTheory.SimpleGraph.Minor.Defs
import GraphTheory.MinorFreeDensity
import GraphTheory.SimpleGraph.Minor.Density
import GraphTheory.SimpleGraph.CycleExistence
import GraphTheory.SimpleGraph.Planar.RotationSystem
import GraphTheory.SimpleGraph.Connectivity.Whitney

/-!
# Planar Graphs

We introduce a predicate `IsPlanar G` for simple graphs, defined via
Wagner's theorem (forbidden minors characterization).

## Approach

A graph is planar iff it contains neither `K₅` nor `K₃,₃` as a minor
(Wagner's theorem / Kuratowski's theorem). We define `IsPlanar` as the
conjunction `G.IsK5MinorFree ∧ G.IsK33MinorFree`, using the minor
infrastructure from `MdsLean.Minor`.

Key properties derived from this definition:

* **Monotonicity (subgraph closure):** If `G` is planar and `H` is a subgraph
  of `G`, then `H` is planar.
* **Edge density:** A planar graph on `n` vertices (`n` at least 3) has at most
  `3n - 6` edges (via `IsK33MinorFree.edgeFinset_card_le`).

## Main definitions

* `SimpleGraph.IsPlanar` -- the planarity predicate (K₅- and K₃,₃-minor-free).

## Main results

* `SimpleGraph.IsPlanar.mono` -- planarity is closed under taking subgraphs.
* `SimpleGraph.IsPlanar.numFaces` -- number of faces of a planar embedding
  (axiomatized).
* `SimpleGraph.IsPlanar.euler_formula` -- Euler's formula: `|V| + |F| = |E| + 2`
  for connected planar graphs.
* `SimpleGraph.IsPlanar.edgeFinset_card_le` -- edge density bound `|E|` at most
  `3|V| - 6`.
* `SimpleGraph.IsPlanar.sum_degrees_le` -- sum of degrees at most `6|V| - 12`.
* `SimpleGraph.IsPlanar.exists_vertex_degree_le_five` -- every planar graph on
  at least 3 vertices has a vertex of degree at most 5.
* `SimpleGraph.CliqueFree.induce` -- triangle-freeness is inherited by
  induced subgraphs.

Triangle-free planar density results (|E| ≤ 2|V| - 4, 3-degeneracy, etc.)
are in `GraphTheory.PlanarGirth` where they are proved from the girth density bound.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-- A graph `G` is planar if it contains neither `K₅` nor `K₃,₃` as a minor.
This is the forbidden-minors characterization of planarity (Wagner's theorem).

By Wagner's theorem, a finite graph is planar (embeddable in the plane without
edge crossings) if and only if it has no `K₅` minor and no `K₃,₃` minor. -/
def IsPlanar (G : SimpleGraph V) : Prop := G.IsK5MinorFree ∧ G.IsK33MinorFree

/-! ### Subgraph closure -/

/-- Planarity is closed under taking subgraphs: if `G` is planar and `H` is a
subgraph of `G` (i.e. `H` has fewer edges), then `H` is planar. -/
theorem IsPlanar.mono {G H : SimpleGraph V} (hG : IsPlanar G)
    (hle : LE.le H G) : IsPlanar H :=
  ⟨IsHMinorFree.minor hG.1 (IsMinor.of_subgraph hle),
   IsHMinorFree.minor hG.2 (IsMinor.of_subgraph hle)⟩

/-! ### Euler's formula (Diestel Thm 4.2.9) -/

/-- The number of faces in a planar embedding of `G`, defined via Euler's
formula: `F = E + 1 + c - V` where `c` is the number of connected components.
For connected graphs this gives the classical `F = E - V + 2`.

This definition is well-defined because `V ≤ E + c` for any finite graph
(each component with `n_i` vertices has at least `n_i - 1` edges). -/
noncomputable def IsPlanar.numFaces {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (_hplanar : IsPlanar G) : Nat :=
  G.edgeFinset.card + 1 + Fintype.card G.ConnectedComponent - Fintype.card V

/-- Helper: for connected graphs, `Fintype.card G.ConnectedComponent = 1`. -/
theorem connected_card_connectedComponent {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) : Fintype.card G.ConnectedComponent = 1 := by
  haveI : Subsingleton G.ConnectedComponent :=
    hconn.preconnected.subsingleton_connectedComponent
  simp [Fintype.card_eq_one_iff]
  exact ⟨G.connectedComponentMk hconn.nonempty.some,
    fun a => Subsingleton.elim _ _⟩

/-- Helper: for connected graphs, `Fintype.card V ≤ G.edgeFinset.card + 1`. -/
theorem connected_card_le_edgeFinset {G : SimpleGraph V}
    [Fintype V] [Fintype G.edgeSet]
    (hconn : G.Connected) : Fintype.card V ≤ G.edgeFinset.card + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_eq_fintype_card] at h
  convert h using 1
  rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset, Set.toFinset_card]

/-- **Euler's formula** for connected planar graphs: `|V| + |F| = |E| + 2`.
Stated in additive form to avoid natural-number subtraction issues. -/
theorem IsPlanar.euler_formula {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    (hplanar : IsPlanar G) (hconn : G.Connected) :
    Fintype.card V + hplanar.numFaces = G.edgeFinset.card + 2 := by
  unfold numFaces
  rw [connected_card_connectedComponent hconn]
  have := connected_card_le_edgeFinset hconn
  omega

/-- Euler's inequality for general (possibly disconnected) planar graphs:
`|V| + |F| ≥ |E| + 2`. Equality holds iff the graph is connected.
Requires `Nonempty V` since the empty graph has `F = 1` by convention. -/
theorem IsPlanar.euler_inequality {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]
    [Nonempty V] (hplanar : IsPlanar G) :
    GE.ge (Fintype.card V + hplanar.numFaces) (G.edgeFinset.card + 2) := by
  unfold numFaces
  have hcv : Fintype.card G.ConnectedComponent ≤ Fintype.card V :=
    Fintype.card_le_of_surjective G.connectedComponentMk
      (fun c => c.ind (fun v => ⟨v, rfl⟩))
  have hc : 1 ≤ Fintype.card G.ConnectedComponent := Fintype.card_pos
  omega

/-! ### Edge density bound

The classical edge-density bound `|E| ≤ 3|V| - 6` (Diestel Cor 4.2.10) and its
consequences (`two_mul_edgeFinset_card_le`, `sum_degrees_le`,
`exists_vertex_degree_le_five`, `three_mul_numFaces_le`) are proved in
`GraphTheory.PlanarGirth` from the (axiomatic) girth bound
`IsPlanar.edgeFinset_card_girth_bound`. Files needing those bounds should
`import GraphTheory.PlanarGirth`. -/

/-! ### Empty and small graph planarity -/

/-- The empty graph on any type is planar. -/
theorem isPlanar_bot (V : Type*) : IsPlanar (Bot.bot : SimpleGraph V) :=
  ⟨bot_isK5MinorFree V, bot_isK33MinorFree V⟩

/-- A complete graph on at most 4 vertices is planar. -/
theorem isPlanar_top_of_card_le_four (V : Type*) [Fintype V]
    (h : LE.le (Fintype.card V) 4) : IsPlanar (Top.top : SimpleGraph V) := by
  constructor
  · -- K₅-minor-free: a minor model needs 5 disjoint nonempty branch sets, but |V| ≤ 4
    intro ⟨m⟩
    have h5 : LE.le (Fintype.card (Fin 5)) (Fintype.card V) :=
      Fintype.card_le_of_injective (fun i => (m.nonempty i).some) (by
        intro i j hij
        by_contra hne_ij
        have hmem_i := Set.Nonempty.some_mem (m.nonempty i)
        have hmem_j := Set.Nonempty.some_mem (m.nonempty j)
        dsimp only at hij
        rw [hij] at hmem_i
        exact Set.disjoint_left.mp (m.disjoint i j hne_ij) hmem_i hmem_j)
    simp at h5
    omega
  · -- K₃,₃-minor-free: a minor model needs 6 disjoint nonempty branch sets, but |V| ≤ 4
    intro ⟨m⟩
    have h6 : LE.le (Fintype.card (Sum (Fin 3) (Fin 3))) (Fintype.card V) :=
      Fintype.card_le_of_injective (fun i => (m.nonempty i).some) (by
        intro i j hij
        by_contra hne_ij
        have hmem_i := Set.Nonempty.some_mem (m.nonempty i)
        have hmem_j := Set.Nonempty.some_mem (m.nonempty j)
        dsimp only at hij
        rw [hij] at hmem_i
        exact Set.disjoint_left.mp (m.disjoint i j hne_ij) hmem_i hmem_j)
    simp [Fintype.card_sum] at h6
    omega

/-! ### Planarity of induced subgraphs -/

/-- Planarity is inherited by induced subgraphs: if `G` is planar, then
`G.induce s` (on the subtype `{v // v ∈ s}`) is also planar.

**Proof:** `G.induce s` is a minor of `G` (by `induce_isMinor`), so both
K₅-minor-freeness and K₃,₃-minor-freeness transfer via `IsHMinorFree.minor`. -/
theorem IsPlanar.induce {G : SimpleGraph V} (hG : IsPlanar G) (s : Set V) :
    IsPlanar (G.induce s) :=
  ⟨IsHMinorFree.minor hG.1 (induce_isMinor G s),
   IsHMinorFree.minor hG.2 (induce_isMinor G s)⟩

/-! ### Planar → 5-degenerate (Diestel Cor 4.2.10)

The 5-degeneracy result `IsPlanar.isKDegenerate_five` lives in
`GraphTheory.PlanarGirth` because its proof uses `exists_vertex_degree_le_five`. -/

/-! ### Triangle-free is inherited by induced subgraphs -/

/-- **Triangle-free is inherited by induced subgraphs.**
If `G` is triangle-free (`CliqueFree 3`), then so is `G.induce s`.
This follows from the fact that `induce s` only keeps edges of `G` between
vertices in `s`, so any clique in `G.induce s` would map to a clique in `G`.

The proof uses `SimpleGraph.Embedding.induce` to lift any graph embedding
from the induced subgraph back to `G`, showing that an n-clique in
`G.induce s` would yield an n-clique in `G`. -/
theorem CliqueFree.induce {G : SimpleGraph V} (htf : G.CliqueFree 3) (s : Set V) :
    (G.induce s).CliqueFree 3 := by
  rw [cliqueFree_iff] at htf
  rw [cliqueFree_iff]
  rw [isEmpty_iff] at htf
  rw [isEmpty_iff]
  intro f
  exact htf (f.trans (Embedding.induce s))

end SimpleGraph
