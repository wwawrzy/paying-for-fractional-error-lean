/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! # A cycle remains connected after deleting one vertex

For a cycle `c.IsCycle` and a vertex `v` on it, the subgraph
`c.toSubgraph.deleteVerts {v}` remains connected. This supplies the cycle
case in the construction of 2-connected subgraphs.

Rotate the cycle to start at `v`. Its tail is a path ending at `v`.
For remaining vertices `x,y`, concatenate the reverse of the prefix ending
at `x` with the prefix ending at `y`. Both prefixes avoid the final endpoint
`v`, and all their edges remain in the cycle. Nonemptiness follows because
a cycle has at least three vertices.

This proof uses only the standard Lean axioms `propext`, `Classical.choice`,
and `Quot.sound`, with no additional axioms or proof placeholders.

Reference: Diestel, Graph Theory, 5th edition, §3.1, pp. 43–44. -/

namespace SimpleGraph

variable {V : Type*}

/-! ## A cycle has no cut vertex -/

/-- Deleting any vertex of a cycle leaves a connected subgraph.
Rotate the cycle to the deleted vertex; prefixes of its path tail connect
any two remaining vertices while avoiding that endpoint. The resulting
walk subgraphs lie in `c.toSubgraph.deleteVerts {v}`. At least two vertices
remain, so the induced vertex type is nonempty. -/
theorem Walk.IsCycle.toSubgraph_no_cut_vertex
    {G : SimpleGraph V} {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    (v : V) (hv : v ∈ c.toSubgraph.verts) :
    (c.toSubgraph.deleteVerts {v}).coe.Connected := by
  classical
  -- Rotate the cycle to start at v.
  have hv_supp : v ∈ c.support := c.mem_verts_toSubgraph.mp hv
  set c' : G.Walk v v := c.rotate v hv_supp with hc'_def
  have hc' : c'.IsCycle := hc.rotate hv_supp
  have htoSub : c'.toSubgraph = c.toSubgraph := Walk.toSubgraph_rotate c hv_supp
  -- The tail is a path from c'.snd to v.
  have htail_path : c'.tail.IsPath := hc'.isPath_tail
  have hc'_not_nil : ¬ c'.Nil := hc'.not_nil
  -- Its support is the cycle support without the initial occurrence of v.
  have hsupp_tail_eq : c'.tail.support = c'.support.tail :=
    c'.support_tail_of_not_nil hc'_not_nil
  -- The rotated cycle starts and ends at v.
  -- In particular, v is the final endpoint of the tail walk.
  -- Every other cycle vertex belongs to the tail support.
  have hverts_eq : c.toSubgraph.verts = {w | w ∈ c.support} := c.verts_toSubgraph
  have hsupp_eq : ∀ w, w ∈ c'.support ↔ w ∈ c.support := by
    intro w
    exact c.mem_support_rotate_iff v hv_supp
  -- A cycle vertex different from v belongs to c'.tail.support.
  have hmem_tail : ∀ {x : V}, x ∈ c.toSubgraph.verts → x ≠ v →
      x ∈ c'.tail.support := by
    intro x hx hxv
    rw [hverts_eq] at hx
    have hxc' : x ∈ c'.support := (hsupp_eq x).mpr hx
    rw [hsupp_tail_eq]
    -- The support starts with v because the rotated cycle starts at v.
    have hhead : c'.support.head c'.support_ne_nil = v := c'.head_support
    have hcons : c'.support = v :: c'.support.tail := by
      have h1 := List.cons_head_tail c'.support_ne_nil
      rw [hhead] at h1
      exact h1.symm
    rw [hcons, List.mem_cons] at hxc'
    rcases hxc' with h | h
    · exact (hxv h).elim
    · exact h
  -- Construct a walk from x to y through c'.snd, avoiding v.
  -- A prefix ending before v does not contain the final endpoint v.
  have hv_not_mem_takeUntil : ∀ {x : V} (hx : x ∈ c'.tail.support), x ≠ v →
      v ∉ (c'.tail.takeUntil x hx).support := by
    intro x hx hxv hvmem
    -- For a path, endpoint_notMem_support_takeUntil excludes the final endpoint
    -- from a prefix ending at a different vertex. Apply it to the tail path.
    exact endpoint_notMem_support_takeUntil htail_path hx (Ne.symm hxv) hvmem
  -- For any remaining vertices x,y, construct a walk avoiding v
  -- whose subgraph lies in c.toSubgraph.deleteVerts {v}.
  have hexists_walk : ∀ {x y : V},
      x ∈ (c.toSubgraph.deleteVerts {v}).verts →
      y ∈ (c.toSubgraph.deleteVerts {v}).verts →
      ∃ p : G.Walk x y,
        p.toSubgraph ≤ c.toSubgraph.deleteVerts {v} := by
    intro x y hx hy
    -- Unpack membership in the cycle vertex set with v deleted.
    have hxv : x ≠ v := by
      intro h
      have : x ∉ ({v} : Set V) := hx.2
      exact this (by simp [h])
    have hyv : y ≠ v := by
      intro h
      have : y ∉ ({v} : Set V) := hy.2
      exact this (by simp [h])
    have hx_verts : x ∈ c.toSubgraph.verts := hx.1
    have hy_verts : y ∈ c.toSubgraph.verts := hy.1
    have hx_tail : x ∈ c'.tail.support := hmem_tail hx_verts hxv
    have hy_tail : y ∈ c'.tail.support := hmem_tail hy_verts hyv
    -- Take the two prefix walks.
    let pₓ : G.Walk c'.snd x := c'.tail.takeUntil x hx_tail
    let pᵧ : G.Walk c'.snd y := c'.tail.takeUntil y hy_tail
    -- Join x to y through c'.snd.
    let p : G.Walk x y := pₓ.reverse.append pᵧ
    refine ⟨p, ?_, ?_⟩
    · -- The constructed walk's vertices lie in the deleted cycle subgraph.
      intro w hw
      -- w ∈ p.toSubgraph.verts → w ∈ p.support
      rw [p.mem_verts_toSubgraph] at hw
      -- The support of the concatenation lies in the union of the two prefix supports.
      have hw_split : w ∈ pₓ.support ∨ w ∈ pᵧ.support := by
        simp only [p, Walk.mem_support_append_iff, Walk.support_reverse,
          List.mem_reverse] at hw
        exact hw
      -- Each prefix support lies in the tail support and avoids v.
      have hw_in_tail : w ∈ c'.tail.support := by
        rcases hw_split with hwx | hwy
        · exact c'.tail.support_takeUntil_subset hx_tail hwx
        · exact c'.tail.support_takeUntil_subset hy_tail hwy
      -- Neither prefix contains v.
      have hwv : w ≠ v := by
        intro h; subst h
        rcases hw_split with hwx | hwy
        · exact hv_not_mem_takeUntil hx_tail hxv hwx
        · exact hv_not_mem_takeUntil hy_tail hyv hwy
      -- Each support vertex lies on the original cycle.
      have hw_c'_supp : w ∈ c'.support := by
        rw [hsupp_tail_eq] at hw_in_tail
        exact List.mem_of_mem_tail hw_in_tail
      have hw_c_supp : w ∈ c.support := (hsupp_eq w).mp hw_c'_supp
      have hw_c_verts : w ∈ c.toSubgraph.verts :=
        c.mem_verts_toSubgraph.mpr hw_c_supp
      -- Combine cycle membership with exclusion of v.
      refine ⟨hw_c_verts, ?_⟩
      simp [hwv]
    · -- The constructed walk's edges lie in the deleted cycle subgraph.
      intro a b hab
      -- hab: p.toSubgraph.Adj a b
      -- Show the endpoints survive deletion and their original cycle edge remains.
      have ha : a ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hab
      have hb : b ∈ p.toSubgraph.verts := p.toSubgraph.edge_vert hab.symm
      -- s(a, b) ∈ p.edges.
      have hab_edges : s(a, b) ∈ p.edges :=
        p.mem_edges_toSubgraph.mp (Subgraph.mem_edgeSet.mpr hab)
      -- The walk's edges lie in the tail edges, using append and reverse.
      have hp_edges_sub : p.edges ⊆ c'.tail.edges := by
        intro e he
        simp only [p, Walk.edges_append, Walk.edges_reverse,
          List.mem_append, List.mem_reverse] at he
        rcases he with hex | hey
        · exact c'.tail.edges_takeUntil_subset hx_tail hex
        · exact c'.tail.edges_takeUntil_subset hy_tail hey
      have hab_tail_edges : s(a, b) ∈ c'.tail.edges := hp_edges_sub hab_edges
      -- The tail edges form a subset of the cycle edges.
      have hab_c'_edges : s(a, b) ∈ c'.edges := by
        -- For a nonempty walk, cons_tail_eq reconstructs it from its first edge and tail.
        -- Thus the edge list consists of the first edge followed by the tail edges.
        have heq : Walk.cons (c'.adj_snd hc'_not_nil) c'.tail = c' :=
          c'.cons_tail_eq hc'_not_nil
        have hedges_sub : c'.tail.edges ⊆ c'.edges := by
          intro e he
          rw [← heq, Walk.edges_cons, List.mem_cons]
          exact Or.inr he
        exact hedges_sub hab_tail_edges
      -- c'.edges = c.edges (rotate preserves edges as multiset / list permutation).
      have hab_c_edges : s(a, b) ∈ c.edges := by
        have hperm : (c.rotate v hv_supp).edges ~r c.edges := c.rotate_edges v hv_supp
        exact hperm.mem_iff.mp hab_c'_edges
      -- The edge therefore belongs to the original cycle subgraph.
      have hab_c_adj : c.toSubgraph.Adj a b := by
        rw [← Subgraph.mem_edgeSet, c.edgeSet_toSubgraph]
        exact hab_c_edges
      -- Both endpoints avoid v, by the established vertex membership.
      -- Use the support calculation to exclude v from the edge endpoints.
      -- Repeat that calculation for the two endpoints as needed.
      -- Vertex membership in the walk subgraph gives membership in its support.
      have ha_supp : a ∈ p.support := p.mem_verts_toSubgraph.mp ha
      have hb_supp : b ∈ p.support := p.mem_verts_toSubgraph.mp hb
      have ha_split : a ∈ pₓ.support ∨ a ∈ pᵧ.support := by
        simp only [p, Walk.mem_support_append_iff, Walk.support_reverse,
          List.mem_reverse] at ha_supp
        exact ha_supp
      have hb_split : b ∈ pₓ.support ∨ b ∈ pᵧ.support := by
        simp only [p, Walk.mem_support_append_iff, Walk.support_reverse,
          List.mem_reverse] at hb_supp
        exact hb_supp
      have hav : a ≠ v := by
        intro h; subst h
        rcases ha_split with hax | hay
        · exact hv_not_mem_takeUntil hx_tail hxv hax
        · exact hv_not_mem_takeUntil hy_tail hyv hay
      have hbv : b ≠ v := by
        intro h; subst h
        rcases hb_split with hbx | hby
        · exact hv_not_mem_takeUntil hx_tail hxv hbx
        · exact hv_not_mem_takeUntil hy_tail hyv hby
      have ha_c_verts : a ∈ c.toSubgraph.verts := by
        have ha_tail : a ∈ c'.tail.support := by
          rcases ha_split with hax | hay
          · exact c'.tail.support_takeUntil_subset hx_tail hax
          · exact c'.tail.support_takeUntil_subset hy_tail hay
        rw [hsupp_tail_eq] at ha_tail
        have ha_c'_supp : a ∈ c'.support := List.mem_of_mem_tail ha_tail
        exact c.mem_verts_toSubgraph.mpr ((hsupp_eq a).mp ha_c'_supp)
      have hb_c_verts : b ∈ c.toSubgraph.verts := by
        have hb_tail : b ∈ c'.tail.support := by
          rcases hb_split with hbx | hby
          · exact c'.tail.support_takeUntil_subset hx_tail hbx
          · exact c'.tail.support_takeUntil_subset hy_tail hby
        rw [hsupp_tail_eq] at hb_tail
        have hb_c'_supp : b ∈ c'.support := List.mem_of_mem_tail hb_tail
        exact c.mem_verts_toSubgraph.mpr ((hsupp_eq b).mp hb_c'_supp)
      -- Combine these facts to establish adjacency after deletion.
      rw [Subgraph.deleteVerts_adj]
      refine ⟨ha_c_verts, ?_, hb_c_verts, ?_, hab_c_adj⟩
      · simp [hav]
      · simp [hbv]
  -- The remaining vertex type is nonempty because a cycle has at least three vertices.
  have hverts_nonempty : (c.toSubgraph.deleteVerts {v}).verts.Nonempty := by
    -- The cycle support has length at least four, and its tail at least three.
    -- Choose a tail vertex different from v.
    -- The tail support has no repeated vertices.
    -- It suffices to find a support vertex other than v.
    -- The support length and tail distinctness provide such a vertex.
    have hlen : 3 ≤ c.length := hc.three_le_length
    have hsupp_len : c.support.length = c.length + 1 := c.length_support
    -- Use two distinct vertices from the tail support.
    -- At least one of the two distinct tail vertices differs from v.
    have htail_len : c.support.tail.length = c.length := by
      rw [List.length_tail, hsupp_len]; omega
    have hnodup_tail : c.support.tail.Nodup := hc.support_nodup
    -- Distinctness follows from the nodup tail support.
    have h0 : 0 < c.support.tail.length := by omega
    have h1 : 1 < c.support.tail.length := by omega
    set a := c.support.tail[0]'h0 with ha_def
    set b := c.support.tail[1]'h1 with hb_def
    have hab : a ≠ b := by
      intro h
      have := List.Nodup.getElem_inj_iff hnodup_tail |>.mp h
      exact absurd this (by decide)
    have ha_in_supp : a ∈ c.support := List.mem_of_mem_tail (List.getElem_mem _)
    have hb_in_supp : b ∈ c.support := List.mem_of_mem_tail (List.getElem_mem _)
    -- At least one of a,b differs from v.
    by_cases hav : a = v
    · -- If a = v, then b differs from v.
      have hbv : b ≠ v := by
        intro hbv
        exact hab (hav.trans hbv.symm)
      refine ⟨b, ?_, ?_⟩
      · exact c.mem_verts_toSubgraph.mpr hb_in_supp
      · simp [hbv]
    · refine ⟨a, ?_, ?_⟩
      · exact c.mem_verts_toSubgraph.mpr ha_in_supp
      · simp [hav]
  -- Assemble connectedness from the walks and nonemptiness.
  have hH_connected : (c.toSubgraph.deleteVerts {v}).Connected := by
    rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
    exact ⟨hverts_nonempty, fun {x y} hx hy => hexists_walk hx hy⟩
  exact hH_connected.coe

end SimpleGraph
