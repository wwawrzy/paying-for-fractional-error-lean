/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Block.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! # The block-cut graph (Diestel Proposition 3.1.1)

The block-cut graph is bipartite, with blocks on one side and cut vertices
on the other. A block and a cut vertex are adjacent exactly when the vertex
belongs to the block. Here a cut vertex is defined operationally as a vertex
belonging to at least two blocks.

The ambient type is `G.Block ⊕ V`, so it also contains isolated entries:
vertices that are not cut vertices, and block classes not represented by an
edge. The induced graph on `coreVertices` discards these entries. This file
proves preconnectedness of that induced graph when `G` is connected; its
acyclicity and counting consequences are developed separately.

Reference: Diestel, Graph Theory, 5th edition, §3.1, p. 44. -/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section Defs

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
/-- A cut vertex in the block-incidence sense belongs to at least two
blocks. This operational definition fits the equivalence relation on edges
used to define blocks; for connected graphs it agrees with the usual
vertex-deletion characterization. -/
def IsCutVertex (v : V) : Prop := 2 ≤ (G.blocksAt v).card

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Positive cut-vertex multiplicity is equivalent to being a cut vertex. -/
theorem IsCutVertex.iff_one_le_mult {v : V} :
    G.IsCutVertex v ↔ 1 ≤ G.cutVertexMultiplicity v := by
  classical
  unfold IsCutVertex cutVertexMultiplicity
  omega

open Classical in
omit [DecidableRel G.Adj] in
/-- A cut vertex belongs to at least one block, hence to nontrivBlockVertices. -/
theorem IsCutVertex.mem_nontrivBlockVertices {v : V}
    (hv : G.IsCutVertex v) : v ∈ G.nontrivBlockVertices := by
  classical
  unfold nontrivBlockVertices
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  unfold IsCutVertex at hv
  omega

open Classical in
/-- The finset of cut vertices of the graph. -/
noncomputable def cutVertices : Finset V :=
  Finset.univ.filter (fun v => G.IsCutVertex v)

open Classical in
omit [DecidableRel G.Adj] in
theorem mem_cutVertices_iff {v : V} :
    v ∈ G.cutVertices ↔ G.IsCutVertex v := by
  classical
  unfold cutVertices
  simp [Finset.mem_filter]

end Defs

/-! ## The block-cut graph

The ambient vertex type is `G.Block ⊕ V`. Edges join a block to a cut vertex
belonging to it; there are no edges within either side of the sum.
Non-cut vertices on the right remain isolated, avoiding a subtype in the
ambient definition. -/

section BlockTree

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
/-- Block-cut adjacency joins `inl b` to `inr v` exactly when `v` is a
cut vertex belonging to `b`. Other combinations are nonadjacent. -/
def blockTreeAdj : G.Block ⊕ V → G.Block ⊕ V → Prop
  | Sum.inl b, Sum.inr v => G.IsCutVertex v ∧ v ∈ G.blockVertices b
  | Sum.inr v, Sum.inl b => G.IsCutVertex v ∧ v ∈ G.blockVertices b
  | _, _ => False

open Classical in
/-- The block-cut graph on `G.Block ⊕ V`. A block is adjacent to a cut
vertex exactly when it contains that vertex. Right-hand entries that are
not cut vertices are isolated. -/
noncomputable def BlockTree : SimpleGraph (G.Block ⊕ V) where
  Adj := G.blockTreeAdj
  symm := by
    intro x y h
    cases x with
    | inl b =>
        cases y with
        | inl b' => exact h.elim
        | inr v => exact h
    | inr v =>
        cases y with
        | inl b => exact h
        | inr v' => exact h.elim
  loopless := ⟨fun x h => by cases x <;> exact h.elim⟩

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- There are no edges between two block entries. -/
theorem BlockTree.not_adj_inl_inl (b b' : G.Block) :
    ¬ (G.BlockTree).Adj (Sum.inl b) (Sum.inl b') := by
  classical
  intro h
  simp [BlockTree, blockTreeAdj] at h

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- There are no edges between two vertex entries. -/
theorem BlockTree.not_adj_inr_inr (v v' : V) :
    ¬ (G.BlockTree).Adj (Sum.inr v) (Sum.inr v') := by
  classical
  intro h
  simp [BlockTree, blockTreeAdj] at h

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A block is adjacent to a vertex exactly when the vertex is a cut
vertex belonging to that block. -/
theorem BlockTree.adj_inl_inr_iff (b : G.Block) (v : V) :
    (G.BlockTree).Adj (Sum.inl b) (Sum.inr v) ↔
      G.IsCutVertex v ∧ v ∈ G.blockVertices b := Iff.rfl

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- The symmetric vertex-to-block adjacency characterization. -/
theorem BlockTree.adj_inr_inl_iff (v : V) (b : G.Block) :
    (G.BlockTree).Adj (Sum.inr v) (Sum.inl b) ↔
      G.IsCutVertex v ∧ v ∈ G.blockVertices b := Iff.rfl

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Adjacency occurs only between a block and a cut vertex belonging to it. -/
theorem BlockTree.adj_iff {x y : G.Block ⊕ V} :
    (G.BlockTree).Adj x y ↔
      (∃ b v, x = Sum.inl b ∧ y = Sum.inr v ∧
              G.IsCutVertex v ∧ v ∈ G.blockVertices b) ∨
      (∃ b v, x = Sum.inr v ∧ y = Sum.inl b ∧
              G.IsCutVertex v ∧ v ∈ G.blockVertices b) := by
  classical
  constructor
  · intro h
    cases x with
    | inl b =>
        cases y with
        | inl b' => exact (BlockTree.not_adj_inl_inl G b b' h).elim
        | inr v =>
            refine Or.inl ⟨b, v, rfl, rfl, ?_⟩
            exact (BlockTree.adj_inl_inr_iff G b v).mp h
    | inr v =>
        cases y with
        | inl b =>
            refine Or.inr ⟨b, v, rfl, rfl, ?_⟩
            exact (BlockTree.adj_inr_inl_iff G v b).mp h
        | inr v' => exact (BlockTree.not_adj_inr_inr G v v' h).elim
  · rintro (⟨b, v, rfl, rfl, h⟩ | ⟨b, v, rfl, rfl, h⟩)
    · exact (BlockTree.adj_inl_inr_iff G b v).mpr h
    · exact (BlockTree.adj_inr_inl_iff G v b).mpr h

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Right-hand entries that are not cut vertices are isolated. -/
theorem BlockTree.isolated_inr_of_not_cutVertex {v : V}
    (hv : ¬ G.IsCutVertex v) (x : G.Block ⊕ V) :
    ¬ (G.BlockTree).Adj (Sum.inr v) x := by
  classical
  cases x with
  | inl b =>
      rw [BlockTree.adj_inr_inl_iff]
      intro ⟨h, _⟩
      exact hv h
  | inr w => exact BlockTree.not_adj_inr_inr G v w

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Symmetrically, a non-cut vertex has no adjacent entry. -/
theorem BlockTree.isolated_inr_of_not_cutVertex_right {v : V}
    (hv : ¬ G.IsCutVertex v) (x : G.Block ⊕ V) :
    ¬ (G.BlockTree).Adj x (Sum.inr v) := by
  classical
  intro h
  exact BlockTree.isolated_inr_of_not_cutVertex G hv x h.symm

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- The neighbors of a block are precisely the cut vertices it contains. -/
theorem BlockTree.neighborSet_inl (b : G.Block) :
    (G.BlockTree).neighborSet (Sum.inl b) =
      Sum.inr '' {v : V | G.IsCutVertex v ∧ v ∈ G.blockVertices b} := by
  classical
  ext x
  simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_setOf_eq]
  cases x with
  | inl b' =>
      constructor
      · intro h
        exact (BlockTree.not_adj_inl_inl G b b' h).elim
      · rintro ⟨v, _, h⟩
        exact (Sum.inr_ne_inl h).elim
  | inr v =>
      rw [BlockTree.adj_inl_inr_iff]
      refine ⟨fun h => ⟨v, h, rfl⟩, ?_⟩
      rintro ⟨w, hw, hwv⟩
      cases hwv
      exact hw

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- The neighbors of a cut vertex are precisely its incident blocks. -/
theorem BlockTree.neighborSet_inr_of_cutVertex {v : V} (hv : G.IsCutVertex v) :
    (G.BlockTree).neighborSet (Sum.inr v) =
      Sum.inl '' {b : G.Block | v ∈ G.blockVertices b} := by
  classical
  ext x
  simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_setOf_eq]
  cases x with
  | inl b =>
      rw [BlockTree.adj_inr_inl_iff]
      refine ⟨fun h => ⟨b, h.2, rfl⟩, ?_⟩
      rintro ⟨b', hb', heq⟩
      cases heq
      exact ⟨hv, hb'⟩
  | inr v' =>
      constructor
      · intro h
        exact (BlockTree.not_adj_inr_inr G v v' h).elim
      · rintro ⟨b, _, h⟩
        exact (Sum.inl_ne_inr h).elim

end BlockTree

/-! ## Preconnectedness of the core block-cut graph

The core consists of edge-containing blocks and cut vertices. A walk in `G`
induces reachability between its incident blocks, passing through a cut
vertex whenever the walk changes blocks. This proves preconnectedness of
the induced core for connected `G`.

Only classes in `G.blocks` represent edge-containing blocks. Other block
classes, and non-cut vertex entries, are isolated and excluded from the core. -/

section Preconnected

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
/-- The core vertex set contains edge-containing block entries and cut
vertex entries, excluding the isolated entries of the ambient sum type. -/
noncomputable def BlockTree.coreVertices : Set (G.Block ⊕ V) :=
  (Sum.inl '' (G.blocks : Set G.Block)) ∪
  (Sum.inr '' {v : V | G.IsCutVertex v})

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A block entry belongs to coreVertices exactly when it belongs to G.blocks. -/
theorem BlockTree.mem_coreVertices_inl_iff {b : G.Block} :
    Sum.inl b ∈ BlockTree.coreVertices G ↔ b ∈ G.blocks := by
  classical
  unfold BlockTree.coreVertices
  simp only [Set.mem_union, Set.mem_image,
    Set.mem_setOf_eq, Sum.inl.injEq]
  refine ⟨?_, ?_⟩
  · rintro (⟨b', hb', heq⟩ | ⟨v, _, h⟩)
    · cases heq; exact hb'
    · exact (Sum.inr_ne_inl h).elim
  · intro hb
    exact Or.inl ⟨b, hb, rfl⟩

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A vertex entry belongs to coreVertices exactly when it is a cut vertex. -/
theorem BlockTree.mem_coreVertices_inr_iff {v : V} :
    Sum.inr v ∈ BlockTree.coreVertices G ↔ G.IsCutVertex v := by
  classical
  unfold BlockTree.coreVertices
  simp only [Set.mem_union, Set.mem_image, Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rintro (⟨b, _, h⟩ | ⟨v', hv', heq⟩)
    · exact (Sum.inl_ne_inr h).elim
    · cases heq; exact hv'
  · intro hv
    exact Or.inr ⟨v, hv, rfl⟩

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge-containing block gives a core vertex. -/
theorem BlockTree.inl_mem_coreVertices {b : G.Block} (hb : b ∈ G.blocks) :
    Sum.inl b ∈ BlockTree.coreVertices G :=
  (BlockTree.mem_coreVertices_inl_iff G).mpr hb

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A cut vertex gives a core vertex. -/
theorem BlockTree.inr_mem_coreVertices {v : V} (hv : G.IsCutVertex v) :
    Sum.inr v ∈ BlockTree.coreVertices G :=
  (BlockTree.mem_coreVertices_inr_iff G).mpr hv

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The block containing an edge of G belongs to G.blocks. -/
theorem blockOf_mem_blocks_of_adj {a b : V} (h : G.Adj a b) :
    G.blockOf s(a, b) ∈ G.blocks := by
  classical
  unfold blocks
  refine Finset.mem_image.mpr ⟨s(a, b), ?_, rfl⟩
  rw [mem_edgeFinset]
  exact h

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- The left endpoint of an edge belongs to the vertices of its block. -/
theorem mem_blockVertices_blockOf_left {a b : V} (h : G.Adj a b) :
    a ∈ G.blockVertices (G.blockOf s(a, b)) := by
  classical
  rw [mem_blockVertices_iff]
  refine ⟨s(a, b), ?_, ?_⟩
  · unfold edgesInBlock
    refine Finset.mem_filter.mpr ⟨?_, rfl⟩
    rw [mem_edgeFinset]
    exact h
  · exact Sym2.mem_mk_left a b

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- The right endpoint of an edge belongs to the vertices of its block. -/
theorem mem_blockVertices_blockOf_right {a b : V} (h : G.Adj a b) :
    b ∈ G.blockVertices (G.blockOf s(a, b)) := by
  classical
  rw [mem_blockVertices_iff]
  refine ⟨s(a, b), ?_, ?_⟩
  · unfold edgesInBlock
    refine Finset.mem_filter.mpr ⟨?_, rfl⟩
    rw [mem_edgeFinset]
    exact h
  · exact Sym2.mem_mk_right a b

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A common vertex of two distinct edge-containing blocks is a cut vertex. -/
theorem isCutVertex_of_mem_two_blocks {v : V} {b₁ b₂ : G.Block}
    (hb₁ : b₁ ∈ G.blocks) (hb₂ : b₂ ∈ G.blocks) (hne : b₁ ≠ b₂)
    (hv₁ : v ∈ G.blockVertices b₁) (hv₂ : v ∈ G.blockVertices b₂) :
    G.IsCutVertex v := by
  classical
  unfold IsCutVertex
  -- The two distinct incident blocks give blocksAt v cardinality at least two.
  have h1 : b₁ ∈ G.blocksAt v := (G.mem_blocksAt_iff).mpr ⟨hb₁, hv₁⟩
  have h2 : b₂ ∈ G.blocksAt v := (G.mem_blocksAt_iff).mpr ⟨hb₂, hv₂⟩
  have hsub : ({b₁, b₂} : Finset G.Block) ⊆ G.blocksAt v := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact h1
    · exact h2
  have : ({b₁, b₂} : Finset G.Block).card ≤ (G.blocksAt v).card :=
    Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    at this

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Adjacency between core vertices restricts to adjacency in the induced core. -/
theorem BlockTree.induce_adj_iff {x y : G.Block ⊕ V}
    (hx : x ∈ BlockTree.coreVertices G) (hy : y ∈ BlockTree.coreVertices G) :
    ((G.BlockTree).induce (BlockTree.coreVertices G)).Adj
        ⟨x, hx⟩ ⟨y, hy⟩ ↔ (G.BlockTree).Adj x y := by
  exact SimpleGraph.induce_adj

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A block reaches any cut vertex it contains in the induced core. -/
theorem BlockTree.reachable_inl_inr_of_cutVertex
    {b : G.Block} {v : V}
    (hb : b ∈ G.blocks) (hv : G.IsCutVertex v) (hvb : v ∈ G.blockVertices b) :
    ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
      ⟨Sum.inl b, BlockTree.inl_mem_coreVertices G hb⟩
      ⟨Sum.inr v, BlockTree.inr_mem_coreVertices G hv⟩ := by
  classical
  refine ⟨?_⟩
  refine SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil
  -- Use the block-to-vertex edge in BlockTree.
  rw [SimpleGraph.induce_adj]
  exact (BlockTree.adj_inl_inr_iff G b v).mpr ⟨hv, hvb⟩

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Two edge-containing blocks sharing a vertex are reachable in the core:
use reflexivity if they coincide, otherwise pass through the common cut vertex. -/
theorem BlockTree.reachable_inl_inl_of_common_vertex
    {b₁ b₂ : G.Block} {v : V}
    (hb₁ : b₁ ∈ G.blocks) (hb₂ : b₂ ∈ G.blocks)
    (hv₁ : v ∈ G.blockVertices b₁) (hv₂ : v ∈ G.blockVertices b₂) :
    ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
      ⟨Sum.inl b₁, BlockTree.inl_mem_coreVertices G hb₁⟩
      ⟨Sum.inl b₂, BlockTree.inl_mem_coreVertices G hb₂⟩ := by
  classical
  by_cases heq : b₁ = b₂
  · subst heq
    exact SimpleGraph.Reachable.refl _
  · -- Distinct blocks sharing v make v a cut vertex.
    have hcut : G.IsCutVertex v :=
      isCutVertex_of_mem_two_blocks G hb₁ hb₂ heq hv₁ hv₂
    -- Follow the two-edge walk from the first block through v to the second.
    have h1 : ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
        ⟨Sum.inl b₁, BlockTree.inl_mem_coreVertices G hb₁⟩
        ⟨Sum.inr v, BlockTree.inr_mem_coreVertices G hcut⟩ :=
      BlockTree.reachable_inl_inr_of_cutVertex G hb₁ hcut hv₁
    have h2 : ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
        ⟨Sum.inr v, BlockTree.inr_mem_coreVertices G hcut⟩
        ⟨Sum.inl b₂, BlockTree.inl_mem_coreVertices G hb₂⟩ :=
      (BlockTree.reachable_inl_inr_of_cutVertex G hb₂ hcut hv₂).symm
    exact h1.trans h2

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A walk from `u` to `v` in G gives reachability from any incident block
of `u` to some incident block of `v` in the core. Induct on the walk, using
the block of the first edge and the shared endpoint at each step. -/
theorem BlockTree.reachable_inl_of_walk
    {u v : V} (w : G.Walk u v) :
    ∀ {b : G.Block} (hb : b ∈ G.blocks), u ∈ G.blockVertices b →
      ∃ b' : G.Block, ∃ hb' : b' ∈ G.blocks, v ∈ G.blockVertices b' ∧
        ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
          ⟨Sum.inl b, BlockTree.inl_mem_coreVertices G hb⟩
          ⟨Sum.inl b', BlockTree.inl_mem_coreVertices G hb'⟩ := by
  classical
  induction w with
  | nil =>
      intro b hb hub
      exact ⟨b, hb, hub, SimpleGraph.Reachable.refl _⟩
  | @cons u u' v hadj p ih =>
      intro b hb hub
      -- Use the first edge and the block containing it.
      set b₀ := G.blockOf s(u, u') with hb₀_def
      have hb₀ : b₀ ∈ G.blocks := blockOf_mem_blocks_of_adj G hadj
      have huu' : u ∈ G.blockVertices b₀ :=
        mem_blockVertices_blockOf_left G hadj
      have hu'u : u' ∈ G.blockVertices b₀ :=
        mem_blockVertices_blockOf_right G hadj
      -- Apply induction to the remaining walk and that block.
      obtain ⟨b', hb', hvb', hreach_b₀_b'⟩ := ih hb₀ hu'u
      refine ⟨b', hb', hvb', ?_⟩
      -- Concatenate reachability through the shared endpoint with the induction result.
      have hreach_b_b₀ :
          ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
            ⟨Sum.inl b, BlockTree.inl_mem_coreVertices G hb⟩
            ⟨Sum.inl b₀, BlockTree.inl_mem_coreVertices G hb₀⟩ :=
        BlockTree.reachable_inl_inl_of_common_vertex G hb hb₀ hub huu'
      exact hreach_b_b₀.trans hreach_b₀_b'

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- Every cut vertex lies in an edge-containing block. -/
theorem BlockTree.exists_block_of_isCutVertex {v : V} (hv : G.IsCutVertex v) :
    ∃ b : G.Block, b ∈ G.blocks ∧ v ∈ G.blockVertices b := by
  classical
  -- A cut vertex has at least two incident blocks, so its incident-block finset is nonempty.
  have hcard : 2 ≤ (G.blocksAt v).card := hv
  have hne : (G.blocksAt v).Nonempty := by
    refine Finset.card_pos.mp ?_
    omega
  obtain ⟨b, hb⟩ := hne
  rw [G.mem_blocksAt_iff] at hb
  exact ⟨b, hb.1, hb.2⟩

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- For connected `G`, the induced core block-cut graph is preconnected.
Reduce each core vertex to an incident block, then use a walk in `G` and
`reachable_inl_of_walk` to connect the corresponding blocks. -/
theorem BlockTree.preconnected (hG : G.Connected) :
    ((G.BlockTree).induce (BlockTree.coreVertices G)).Preconnected := by
  classical
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  -- Connect each endpoint to an edge-containing block,
  -- using an incident block for a cut vertex,
  -- then connect the blocks using connectedness of G.
  -- For a core vertex, choose an edge-containing incident block
  -- and a reachability step to that block entry.
  suffices h : ∀ (z : G.Block ⊕ V) (hz : z ∈ BlockTree.coreVertices G),
      ∃ (b : G.Block) (hb : b ∈ G.blocks) (w : V),
        w ∈ G.blockVertices b ∧
        ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
          ⟨z, hz⟩ ⟨Sum.inl b, BlockTree.inl_mem_coreVertices G hb⟩ by
    obtain ⟨b₁, hb₁, w₁, hw₁, hreach₁⟩ := h x hx
    obtain ⟨b₂, hb₂, w₂, hw₂, hreach₂⟩ := h y hy
    -- Connectedness of G supplies a walk between the chosen representatives.
    obtain ⟨walk⟩ := hG w₁ w₂
    -- The walk connects the first block to a block containing the second representative.
    obtain ⟨b₂', hb₂', hw₂', hreach⟩ :=
      BlockTree.reachable_inl_of_walk G walk hb₁ hw₁
    -- Obtain reachability between those block entries.
    -- The resulting block shares the second representative with the chosen second block.
    have hreach_b' : ((G.BlockTree).induce (BlockTree.coreVertices G)).Reachable
        ⟨Sum.inl b₂', BlockTree.inl_mem_coreVertices G hb₂'⟩
        ⟨Sum.inl b₂, BlockTree.inl_mem_coreVertices G hb₂⟩ :=
      BlockTree.reachable_inl_inl_of_common_vertex G hb₂' hb₂ hw₂' hw₂
    -- Concatenate the reachability steps to connect the original core endpoints.
    exact hreach₁.trans (hreach.trans (hreach_b'.trans hreach₂.symm))
  -- It remains to find an incident block for each core vertex.
  intro z hz
  rcases z with b | v
  · -- For a block entry, its core membership certifies membership in G.blocks.
    have hb : b ∈ G.blocks := (BlockTree.mem_coreVertices_inl_iff G).mp hz
    -- An edge-containing block has a vertex.
    have hne : (G.edgesInBlock b).Nonempty := by
      have := (G.block_decomposition).1 b hb
      exact this
    obtain ⟨e, he⟩ := hne
    -- Choose an endpoint of an edge as the representative.
    have he_in_block : e ∈ G.edgesInBlock b := he
    have hev : ∃ w, w ∈ e := by
      -- Every unordered pair has an endpoint.
      induction e with
      | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩
    obtain ⟨w, hwe⟩ := hev
    have hwb : w ∈ G.blockVertices b :=
      (G.mem_blockVertices_iff).mpr ⟨e, he_in_block, hwe⟩
    refine ⟨b, hb, w, hwb, ?_⟩
    exact SimpleGraph.Reachable.refl _
  · -- For a vertex entry, core membership certifies that it is a cut vertex.
    have hv : G.IsCutVertex v := (BlockTree.mem_coreVertices_inr_iff G).mp hz
    obtain ⟨b, hb, hvb⟩ := BlockTree.exists_block_of_isCutVertex G hv
    refine ⟨b, hb, v, hvb, ?_⟩
    exact (BlockTree.reachable_inl_inr_of_cutVertex G hb hv hvb).symm

end Preconnected

end SimpleGraph
