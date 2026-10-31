import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import GraphTheory.MaderPaths
import GraphTheory.SimpleGraph.Block.CycleHPathConstruction

/-!
# Adding an H-path preserves the absence of cut vertices

Diestel, *Graph Theory*, 5th ed., §3.1, Proposition 3.1.2, pp. 44–45. This
is the inductive step showing that a subgraph built from a cycle has no cut
vertex after adding an H-path.

## Statement

If `H` is 2-connected in the operational sense (connected and with no cut
vertex), and `p : G.Walk u v` is an H-path in `G` relative to `H`, then the
supremum `H ⊔ p.toSubgraph` also has no cut vertex.

The helper lemma `Subgraph.IsTwoConnected.no_cut_vertex_after_addHPath` proves
this preservation step.

## Proof strategy

We split into two cases for a vertex `w` of `(H ⊔ p.toSubgraph).verts`:

* **Case 1: `w ∉ H.verts`** (so `w` is an internal vertex of `p`). The graph
  `(H ⊔ p.toSubgraph) - {w}` contains all of `H`; the remaining path segments
  attach to `H` at the endpoints `u, v ∈ V(H)`.

* **Case 2: `w ∈ H.verts`** (so `w` may be an endpoint of `p` or another
  vertex of `H`). By `hH_no_cut`, `H - {w}` is connected. The internal
  vertices of `p` lie outside `V(H)`, so the surviving path segments attach
  through an endpoint in `V(H) ∖ {w}`.

## References

* Diestel, *Graph Theory*, 5th ed., Proposition 3.1.2.
* `GraphTheory.SimpleGraph.Block.CycleHPathConstruction` — definition of
  `Subgraph.IsTwoConnected` and the cycle construction.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ## Helpers for vertices and adjacency in `H ⊔ p.toSubgraph` -/

/-- The vertices of `(H ⊔ p.toSubgraph).deleteVerts {w}` are
`(H.verts ∪ p.support) \ {w}`. -/
lemma verts_deleteVerts_sup_toSubgraph
    {G : SimpleGraph V} (H : G.Subgraph) {x y : V} (p : G.Walk x y) (w : V) :
    ((H ⊔ p.toSubgraph).deleteVerts {w}).verts =
      (H.verts ∪ {z | z ∈ p.support}) \ {w} := by
  unfold Subgraph.deleteVerts
  simp [Subgraph.induce_verts, Subgraph.verts_sup]

/-! ## Main preservation lemma

This is the main preservation lemma, with conclusion
`Subgraph.IsTwoConnected.no_cut_vertex_after_addHPath`.

Assumptions:
* `hH_no_cut`: deleting any vertex from `H` leaves a connected subgraph
  (using `coe.Connected`);
* `hH_conn`: `H` is connected;
* `hp`: `p` is an H-path relative to `H`.

Conclusion: `H ⊔ p.toSubgraph` has no cut vertex.

**Note:** the assumptions use `(H.deleteVerts {w}).coe.Connected`, matching
Mathlib's definition of `Subgraph.Connected`; `Subgraph.connected_iff'` is the
bridge to that definition.

The proof avoids needing a separate Mathlib lemma for connectivity of
`(H ⊔ p.toSubgraph).deleteVerts`. For each surviving path vertex it builds a
walk to a surviving endpoint in `H`, then joins the two walks inside the
connected graph `H.deleteVerts {w}`. -/

/-- **Case 1 helper:** if the deleted vertex `w` is not in `V(H)`, then
`(H ⊔ p.toSubgraph) - {w}` contains all of `H` as a subgraph. The remaining
path segments attach to this connected subgraph.

This is Case 1 of `no_cut_vertex_after_addHPath`. -/
lemma case1_w_notin_H_aux
    {G : SimpleGraph V} {H : G.Subgraph} {x y : V} (p : G.Walk x y)
    (_hp : IsHPath G H p) {w : V} (hw_notin_H : w ∉ H.verts)
    (_hH_conn : H.coe.Connected) :
    -- In this case `H` is a subgraph of `(H ⊔ p.toSubgraph).deleteVerts {w}`.
    -- It suffices to show vertex inclusion and preservation of its edges.
    H.verts ⊆ ((H ⊔ p.toSubgraph).deleteVerts {w}).verts := by
  intro z hz
  rw [verts_deleteVerts_sup_toSubgraph]
  refine ⟨Or.inl hz, ?_⟩
  -- Since z ∈ H.verts and w ∉ H.verts, z ≠ w.
  intro hzw
  rw [Set.mem_singleton_iff] at hzw
  exact hw_notin_H (hzw ▸ hz)

/-- **Case 2 helper:** if `w ∈ V(H)`, then either an endpoint of `p` differs
from `w`, or `H` has another vertex distinct from `w`.

Both endpoints of `p` may equal `w`. In that case, use that `H` has a vertex
other than `w`, obtained from the nonempty connected graph `H - {w}`.

This lemma extracts that witness from `hH_no_cut`. -/
lemma case2_exists_other_vertex
    {G : SimpleGraph V} {H : G.Subgraph} {w : V} (_hwH : w ∈ H.verts)
    (hH_no_cut_w : (H.deleteVerts {w}).coe.Connected) :
    ∃ z ∈ H.verts, z ≠ w := by
  -- `hH_no_cut_w` makes `(H.deleteVerts {w}).verts` nonempty.
  -- This vertex set is `H.verts \ {w}`.
  haveI := hH_no_cut_w.nonempty
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (H.deleteVerts {w}).verts := by
    obtain ⟨⟨z, hz⟩⟩ := (inferInstance : Nonempty (H.deleteVerts {w}).verts)
    exact ⟨z, hz⟩
  rw [Subgraph.deleteVerts_verts] at hz
  exact ⟨z, hz.1, fun heq => hz.2 (by simp [heq])⟩

/-! ## Walks in the graph after deleting a vertex -/

/-- If `q.toSubgraph ≤ K` and `q` avoids `w`, then the walk's subgraph is
contained in `K.deleteVerts {w}`. -/
lemma Walk.toSubgraph_le_deleteVerts_of_le_of_not_mem_support
    {G : SimpleGraph V} {a b w : V} (q : G.Walk a b) {K : G.Subgraph}
    (hq : q.toSubgraph ≤ K) (hw : w ∉ q.support) :
    q.toSubgraph ≤ K.deleteVerts {w} := by
  constructor
  · intro z hz
    rw [Subgraph.deleteVerts_verts]
    refine ⟨hq.1 hz, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hzw
    subst z
    exact hw (q.mem_verts_toSubgraph.mp hz)
  · intro x y hxy
    rw [Subgraph.deleteVerts_adj]
    have hx : x ∈ q.toSubgraph.verts := q.toSubgraph.edge_vert hxy
    have hy : y ∈ q.toSubgraph.verts := q.toSubgraph.edge_vert hxy.symm
    refine ⟨hq.1 hx, ?_, hq.1 hy, ?_, hq.2 hxy⟩
    · simp only [Set.mem_singleton_iff]
      intro hxw
      subst x
      exact hw (q.mem_verts_toSubgraph.mp hx)
    · simp only [Set.mem_singleton_iff]
      intro hyw
      subst y
      exact hw (q.mem_verts_toSubgraph.mp hy)

/-- **Every vertex** that survives deleting `w` from `H ⊔ p.toSubgraph` can be
joined, by a walk avoiding `w`, to a surviving vertex of `H`.

If the vertex is already in `H`, use the trivial walk. Otherwise split `p` at
that vertex. If the prefix avoids `w`, follow it to the start of `p`; if the
prefix contains `w`, path simplicity guarantees that the suffix avoids `w`,
so follow it to the end of `p`. -/
lemma IsHPath.exists_walk_to_surviving_H
    {G : SimpleGraph V} {H : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : IsHPath G H p) {w z : V}
    (hz : z ∈ ((H ⊔ p.toSubgraph).deleteVerts {w}).verts) :
    ∃ a, a ∈ (H.deleteVerts {w}).verts ∧
      ∃ q : G.Walk z a,
        q.toSubgraph ≤ (H ⊔ p.toSubgraph).deleteVerts {w} := by
  classical
  have hzQ := hz
  rw [verts_deleteVerts_sup_toSubgraph] at hz
  obtain ⟨hz_union, hzw_set⟩ := hz
  by_cases hzH : z ∈ H.verts
  · refine ⟨z, ?_, Walk.nil, ?_⟩
    · rw [Subgraph.deleteVerts_verts]
      exact ⟨hzH, hzw_set⟩
    · simpa only [Walk.toSubgraph] using
        (singletonSubgraph_le_iff z
          ((H ⊔ p.toSubgraph).deleteVerts {w})).mpr hzQ
  · have hzP : z ∈ p.support := hz_union.resolve_left hzH
    have hzv : z ≠ v := fun h => hzH (h ▸ hp.finish_mem)
    have hzw : z ≠ w := by
      simpa only [Set.mem_singleton_iff] using hzw_set
    let pre : G.Walk u z := p.takeUntil z hzP
    let suf : G.Walk z v := p.dropUntil z hzP
    have hpre_le : pre.toSubgraph ≤ p.toSubgraph := by
      constructor
      · intro t ht
        rw [Walk.mem_verts_toSubgraph] at ht ⊢
        exact p.support_takeUntil_subset hzP ht
      · intro a b hab
        rw [Walk.adj_toSubgraph_iff_mem_edges] at hab ⊢
        exact p.edges_takeUntil_subset hzP hab
    have hsuf_le : suf.toSubgraph ≤ p.toSubgraph := by
      constructor
      · intro t ht
        rw [Walk.mem_verts_toSubgraph] at ht ⊢
        exact p.support_dropUntil_subset hzP ht
      · intro a b hab
        rw [Walk.adj_toSubgraph_iff_mem_edges] at hab ⊢
        exact p.edges_dropUntil_subset hzP hab
    by_cases hwpre : w ∈ pre.support
    · have hsplit : pre.append suf = p := Walk.take_spec p hzP
      have hpath_split : (pre.append suf).IsPath := by
        rw [hsplit]
        exact hp.isPath
      have hsuf_non_nil : ¬suf.Nil := Walk.not_nil_of_ne hzv
      have hdisj : pre.support.Disjoint suf.tail.support :=
        hpath_split.disjoint_support_of_append hsuf_non_nil
      have hwsuf : w ∉ suf.support := by
        intro hw
        have hw_tail_list : w ∈ suf.support.tail :=
          (suf.mem_support_iff.mp hw).resolve_left hzw.symm
        have hw_tail : w ∈ suf.tail.support := by
          rwa [← suf.support_tail_of_not_nil hsuf_non_nil] at hw_tail_list
        exact hdisj hwpre hw_tail
      refine ⟨v, ?_, suf, ?_⟩
      · rw [Subgraph.deleteVerts_verts]
        refine ⟨hp.finish_mem, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro hvw
        subst v
        exact hwsuf suf.end_mem_support
      · exact suf.toSubgraph_le_deleteVerts_of_le_of_not_mem_support
          (hsuf_le.trans le_sup_right) hwsuf
    · refine ⟨u, ?_, pre.reverse, ?_⟩
      · rw [Subgraph.deleteVerts_verts]
        refine ⟨hp.start_mem, ?_⟩
        simp only [Set.mem_singleton_iff]
        intro huw
        subst u
        exact hwpre pre.start_mem_support
      · exact Walk.toSubgraph_le_deleteVerts_of_le_of_not_mem_support pre.reverse
          (by simpa only [Walk.toSubgraph_reverse] using hpre_le.trans le_sup_right)
          (by simpa using hwpre)

/-! ## Main theorem -/

/-- Adding an H-path to an operationally 2-connected subgraph preserves the
absence of cut vertices: deleting any vertex from the supremum leaves a
connected graph. -/
theorem Subgraph.IsTwoConnected.no_cut_vertex_after_addHPath
    {G : SimpleGraph V} {H : G.Subgraph} (hH : H.IsTwoConnected)
    {u v : V} (p : G.Walk u v) (hp : IsHPath G H p) :
    ∀ w ∈ (H ⊔ p.toSubgraph).verts,
      ((H ⊔ p.toSubgraph).deleteVerts {w}).Connected := by
  intro w _hw
  let B := H.deleteVerts {w}
  let Q := (H ⊔ p.toSubgraph).deleteVerts {w}
  have hBconn : B.Connected := by
    by_cases hwH : w ∈ H.verts
    · exact hH.no_cut_vertex w hwH
    · have hdel : H.deleteVerts {w} = H := by
        ext <;> simp +contextual [hwH]
        constructor
        · exact fun h => h.2.2
        · intro hxy
          exact ⟨H.edge_vert hxy, H.edge_vert hxy.symm, hxy⟩
      simpa only [B, hdel] using hH.connected
  have hBQ : B ≤ Q := by
    exact Subgraph.deleteVerts_mono (le_sup_left : H ≤ H ⊔ p.toSubgraph)
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  constructor
  · obtain ⟨a, ha⟩ := hBconn.nonempty
    exact ⟨a, hBQ.1 ha⟩
  · intro x y hx hy
    obtain ⟨a, haB, qx, hqx⟩ := hp.exists_walk_to_surviving_H hx
    obtain ⟨b, hbB, qy, hqy⟩ := hp.exists_walk_to_surviving_H hy
    obtain ⟨r, hr⟩ :=
      (Subgraph.preconnected_iff_forall_exists_walk_subgraph B).mp
        hBconn.preconnected haB hbB
    refine ⟨(qx.append r).append qy.reverse, ?_⟩
    rw [Walk.toSubgraph_append, Walk.toSubgraph_append, Walk.toSubgraph_reverse]
    exact sup_le (sup_le hqx (hr.trans hBQ)) hqy

end SimpleGraph
