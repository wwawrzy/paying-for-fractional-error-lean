/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.Block.Defs

/-! # Every vertex of a nontrivial connected graph belongs to a block

For a connected graph with at least two vertices,
`nontrivBlockVertices = Finset.univ`. Each vertex has a neighbor, hence an
incident edge. The block containing that edge also contains the vertex.
A walk to a different vertex supplies the required first edge. -/

namespace SimpleGraph

variable {V : Type*}

/-- Every vertex in a connected graph with at least two vertices has a neighbor. -/
theorem Connected.exists_adj_of_two_le_card
    [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) (hV : 2 ≤ Fintype.card V) (v : V) :
    ∃ u, G.Adj v u := by
  classical
  -- At least two vertices give a distinct vertex w.
  have hNt : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hV
  obtain ⟨w, hw⟩ := exists_ne v
  -- Connectedness gives reachability from v to w.
  have hreach : G.Reachable v w := hG.preconnected v w
  -- Choose a walk from v to w.
  obtain ⟨p⟩ := hreach
  -- Distinct endpoints exclude a nil walk.
  cases p with
  | nil =>
      -- A nil walk would identify the distinct endpoints.
      exact (hw rfl).elim
  | cons hadj _ =>
      -- The first edge supplies a neighbor of v.
      exact ⟨_, hadj⟩

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V)
  [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
omit [DecidableRel G.Adj] in
/-- For a connected graph with at least two vertices,
`nontrivBlockVertices = Finset.univ`. An incident edge at each vertex lies
in a block containing that vertex. -/
theorem nontrivBlockVertices_eq_univ_of_connected
    (hG : G.Connected) (hV : 2 ≤ Fintype.card V) :
    G.nontrivBlockVertices = Finset.univ := by
  classical
  -- Show that every vertex belongs to nontrivBlockVertices.
  apply Finset.eq_univ_of_forall
  intro v
  -- Choose a neighbor u of v.
  obtain ⟨u, hadj⟩ := Connected.exists_adj_of_two_le_card G hG hV v
  -- Use the edge e = s(v,u).
  let e : Sym2 V := s(v, u)
  have he_mem : e ∈ G.edgeSet := hadj
  have he_fin : e ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact he_mem
  -- Take the block b containing e.
  let b : G.Block := G.blockOf e
  -- The block belongs to G.blocks because it contains an edge.
  have hb_blocks : b ∈ G.blocks := by
    unfold SimpleGraph.blocks
    exact Finset.mem_image.mpr ⟨e, he_fin, rfl⟩
  -- e ∈ G.edgesInBlock b
  have he_inblock : e ∈ G.edgesInBlock b := by
    unfold SimpleGraph.edgesInBlock
    exact Finset.mem_filter.mpr ⟨he_fin, rfl⟩
  -- The vertex v is an endpoint of e.
  have hv_in_e : v ∈ e := Sym2.mem_mk_left v u
  -- v ∈ G.blockVertices b
  have hv_block : v ∈ G.blockVertices b := by
    rw [G.mem_blockVertices_iff]
    exact ⟨e, he_inblock, hv_in_e⟩
  -- b ∈ G.blocksAt v
  have hb_at : b ∈ G.blocksAt v := by
    rw [G.mem_blocksAt_iff]
    exact ⟨hb_blocks, hv_block⟩
  -- 1 ≤ (G.blocksAt v).card
  have hcard : 1 ≤ (G.blocksAt v).card := Finset.card_pos.mpr ⟨b, hb_at⟩
  -- v ∈ G.nontrivBlockVertices
  unfold SimpleGraph.nontrivBlockVertices
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcard⟩

end SimpleGraph
