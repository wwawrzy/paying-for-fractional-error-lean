/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Eulerian circuits and Euler's theorem (1736)

This file proves the classical theorem of Euler (Diestel, *Graph Theory*
5th ed., Theorem 1.8.1): a connected finite graph admits an Eulerian
circuit (a closed walk traversing every edge exactly once) if and only
if every vertex has even degree.

The hard direction (⇐) is proved constructively via Hierholzer's
algorithm: starting from any closed trail through a vertex of positive
degree, we iteratively splice in fresh closed sub-trails attached at
"boundary" vertices, until all edges are exhausted.

## Main definitions

* `SimpleGraph.HasEulerianCircuit G`: the proposition that some closed
  walk in `G` is Eulerian.

## Main results

* `SimpleGraph.Walk.splice_closed_trails`: two closed trails with
  disjoint edge sets and a common support vertex can be combined into
  a single closed trail whose edge multiset is their concatenation.
* `SimpleGraph.Walk.extend_trail_at_endpoint`: in a graph with all even
  degrees, any trail can be extended at a non-start endpoint by a fresh
  edge.
* `SimpleGraph.Walk.closed_trail_of_pos_degree`: in a graph with all
  even degrees, every vertex of positive degree is the basepoint of a
  non-trivial closed trail.
* `SimpleGraph.Walk.boundary_vertex_of_remaining`: in a connected graph,
  any closed trail not covering all edges has a support vertex incident
  to a fresh edge.
* `SimpleGraph.Walk.deleteEdges_closed_trail_even_degree`: removing the
  edges of a closed trail preserves the property that every vertex has
  even degree.
* `SimpleGraph.Walk.hierholzer_main`: the constructive (⇐) direction of
  Euler 1736 — a connected graph with all even degrees has an Eulerian
  circuit.
* `SimpleGraph.Walk.euler_1736_full`: the full iff phrased on the
  existence of an Eulerian closed walk.
* `SimpleGraph.euler_1736`: Diestel Theorem 1.8.1 phrased via
  `HasEulerianCircuit`.

## Implementation notes

The construction proceeds by strong induction on
`G.edgeFinset.card - p.edges.length`. At each step:

1. If the current closed trail `p` covers all edges, it is Eulerian.
2. Otherwise, a fresh edge exists somewhere in `G`. Connectivity
   guarantees a *boundary vertex* `w ∈ p.support` adjacent to an unused
   edge.
3. The graph `G' := G \ p.edges` has all even degrees (parity is
   preserved because `p` is a closed trail), and `w` has positive
   degree in `G'`.
4. A closed trail `T_w` at `w` in `G'` is built and spliced into `p`,
   producing a strictly longer closed trail.

The parity argument behind extension uses
`Walk.IsTrail.even_countP_edges_iff` from Mathlib: in a trail with
distinct endpoints, the count of trail-edges incident to a vertex is
even unless that vertex is an endpoint.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

namespace Walk

/-- Splice two closed trails sharing a vertex on the support of the first.
If `p : G.Walk v v` is a closed trail and `q : G.Walk w w` is a closed trail
with edges disjoint from `p`, and `w ∈ p.support`, then there is a trail
`r : G.Walk v v` whose edge multiset is `p.edges ++ q.edges`. -/
theorem splice_closed_trails [DecidableEq V] {v w : V}
    (p : G.Walk v v) (q : G.Walk w w)
    (hp : p.IsTrail) (hq : q.IsTrail)
    (hd : p.edges.Disjoint q.edges)
    (hw : w ∈ p.support) :
    ∃ r : G.Walk v v, r.IsTrail ∧ List.Perm r.edges (p.edges ++ q.edges) := by
  set p1 := p.takeUntil w hw
  set p2 := p.dropUntil w hw
  have hp1 : p1.IsTrail := hp.takeUntil hw
  have hp2 : p2.IsTrail := hp.dropUntil hw
  have hd12 : p1.edges.Disjoint p2.edges := hp.disjoint_edges_takeUntil_dropUntil hw
  have hp_eq : p.edges = p1.edges ++ p2.edges := by
    rw [← edges_append, take_spec]
  have hd_p1q : p1.edges.Disjoint q.edges := by
    intro e he1 heq
    have hep : e ∈ p.edges := by rw [hp_eq]; exact List.mem_append_left _ he1
    exact hd hep heq
  have hd_qp2 : q.edges.Disjoint p2.edges := by
    intro e heq he2
    have : e ∈ p.edges := by rw [hp_eq]; exact List.mem_append_right _ he2
    exact hd this heq
  refine ⟨p1.append (q.append p2), ?_, ?_⟩
  · rw [isTrail_def, edges_append, edges_append]
    rw [List.nodup_append']
    refine ⟨hp1.edges_nodup, ?_, ?_⟩
    · rw [List.nodup_append']
      exact ⟨hq.edges_nodup, hp2.edges_nodup, hd_qp2⟩
    · rw [List.disjoint_append_right]
      exact ⟨hd_p1q, hd12⟩
  · rw [edges_append, edges_append, hp_eq]
    rw [List.append_assoc p1.edges p2.edges q.edges]
    exact List.Perm.append_left _ List.perm_append_comm

/-- Extension at a non-start endpoint via parity. If `p : G.Walk v u` is a trail
with `v ≠ u`, all `G`-degrees are even, and the underlying graph has finite
vertex set, then there exists a `G`-neighbor `w` of `u` with the edge `s(u,w)`
not in `p.edges`. -/
theorem extend_trail_at_endpoint
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v u : V} (p : G.Walk v u) (hp : p.IsTrail) (hne : v ≠ u)
    (hEven : ∀ x, Even (G.degree x)) :
    ∃ w, ∃ _ : G.Adj u w, s(u, w) ∉ p.edges := by
  have h_count_odd : ¬ Even (List.countP (fun e => decide (u ∈ e)) p.edges) := by
    rw [hp.even_countP_edges_iff (x := u)]
    intro habs
    exact (habs hne).2 rfl
  let T : Finset (Sym2 V) := (p.edges.filter (fun e => u ∈ e)).toFinset
  have hT_nodup : (p.edges.filter (fun e => u ∈ e)).Nodup :=
    hp.edges_nodup.filter _
  have hT_card : T.card = List.countP (fun e => decide (u ∈ e)) p.edges := by
    show (List.filter (fun e => decide (u ∈ e)) p.edges).toFinset.card = _
    rw [List.toFinset_card_of_nodup hT_nodup, List.countP_eq_length_filter]
  have hT_sub : T ⊆ G.incidenceFinset u := by
    intro e he
    simp only [T, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨he_p, he_u⟩ := he
    rw [G.mem_incidenceFinset]
    exact ⟨(Walk.edges_subset_edgeSet p) he_p, he_u⟩
  have h_inc_even : Even (G.incidenceFinset u).card := by
    rw [G.card_incidenceFinset_eq_degree]; exact hEven u
  have h_T_card_odd : ¬ Even T.card := by rw [hT_card]; exact h_count_odd
  have hT_ne : T ≠ G.incidenceFinset u := by
    intro habs; apply h_T_card_odd; rw [habs]; exact h_inc_even
  have hT_lt : T ⊂ G.incidenceFinset u := ⟨hT_sub, fun h => hT_ne (le_antisymm hT_sub h)⟩
  obtain ⟨e, he_inc, he_nT⟩ := Finset.exists_of_ssubset hT_lt
  rw [G.mem_incidenceFinset] at he_inc
  obtain ⟨he_edge, he_u_in⟩ := he_inc
  induction e using Sym2.ind with
  | h a b =>
    rw [Sym2.mem_iff] at he_u_in
    rcases he_u_in with rfl | rfl
    · refine ⟨b, G.mem_edgeSet.mp he_edge, ?_⟩
      intro habs
      apply he_nT
      simp only [T, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨habs, Sym2.mem_mk_left _ _⟩
    · refine ⟨a, (G.mem_edgeSet.mp he_edge).symm, ?_⟩
      intro habs
      apply he_nT
      simp only [T, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      refine ⟨?_, Sym2.mem_mk_right _ _⟩
      rwa [Sym2.eq_swap]

/-- From any vertex `v` of positive degree in a graph with all even degrees,
there is a non-trivial closed trail starting at `v`.

Proof by strong induction on the number of unused edges: starting with
`cons (some adj) Walk.nil` we keep extending as long as endpoint ≠ v;
`extend_trail_at_endpoint` guarantees this is always possible. -/
theorem closed_trail_of_pos_degree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hEven : ∀ x, Even (G.degree x))
    {v : V} (hv : 0 < G.degree v) :
    ∃ p : G.Walk v v, p.IsTrail ∧ p.edges ≠ [] := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, G.Adj v w := by
    by_contra habs
    push_neg at habs
    have : G.degree v = 0 := by
      rw [degree, Finset.card_eq_zero]
      ext x
      simp only [G.mem_neighborFinset, Finset.notMem_empty, iff_false]
      exact habs x
    omega
  let initial : G.Walk v w₀ := Walk.cons hw₀ Walk.nil
  have h_init_trail : initial.IsTrail := by
    rw [Walk.isTrail_cons]
    refine ⟨Walk.IsTrail.nil, ?_⟩
    simp
  have h_init_nonempty : initial.edges ≠ [] := by simp [initial]
  suffices h : ∀ k : ℕ, ∀ {u : V} (p : G.Walk v u),
      p.IsTrail → p.edges ≠ [] →
      G.edgeFinset.card - p.edges.length = k →
      ∃ q : G.Walk v v, q.IsTrail ∧ q.edges ≠ [] by
    exact h _ initial h_init_trail h_init_nonempty rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k IH =>
    intro u p hpT hpNE hk
    by_cases huv : u = v
    · subst huv
      exact ⟨p, hpT, hpNE⟩
    · obtain ⟨w, hAdj, h_e_notin⟩ := extend_trail_at_endpoint p hpT (Ne.symm huv) hEven
      let p' : G.Walk v w := p.append (Walk.cons hAdj Walk.nil)
      have hp'T : p'.IsTrail := by
        rw [Walk.isTrail_def, Walk.edges_append, Walk.edges_cons, Walk.edges_nil]
        rw [List.nodup_append']
        refine ⟨hpT.edges_nodup, by simp, ?_⟩
        intro e he1 he2
        simp only [List.mem_singleton] at he2
        subst he2
        exact h_e_notin he1
      have hp'NE : p'.edges ≠ [] := by
        simp [p', Walk.edges_append, Walk.edges_cons]
      have hp'_len : p'.edges.length = p.edges.length + 1 := by
        simp [p', Walk.edges_append, Walk.edges_cons]
      have h_le : p'.edges.length ≤ G.edgeFinset.card := by
        rw [← List.toFinset_card_of_nodup hp'T.edges_nodup]
        apply Finset.card_le_card
        intro e he
        rw [List.mem_toFinset] at he
        rw [G.mem_edgeFinset]
        exact (Walk.edges_subset_edgeSet p') he
      have h_pos_diff : 0 < G.edgeFinset.card - p.edges.length := by
        rw [hp'_len] at h_le; omega
      have h_decrease : G.edgeFinset.card - p'.edges.length <
          G.edgeFinset.card - p.edges.length := by
        rw [hp'_len]; omega
      have hk' : G.edgeFinset.card - p'.edges.length < k := by
        rw [← hk]; exact h_decrease
      exact IH _ hk' p' hp'T hp'NE rfl

/-- Walk-based boundary: if `pa : G.Walk a v` is any walk, `v ∈ p.support` and
`a ∉ p.support`, then somewhere along `pa` there is an edge `s(w, x)` not in
`p.edges` with `w ∈ p.support`. -/
private theorem boundary_along_walk
    {v : V} {p : G.Walk v v} :
    ∀ {a : V} (pa : G.Walk a v),
      a ∉ p.support →
      ∃ w ∈ p.support, ∃ x, G.Adj w x ∧ s(w, x) ∉ p.edges := by
  intro a pa
  induction pa with
  | nil =>
    intro habs
    exact (habs (Walk.start_mem_support _)).elim
  | @cons a b v hAdj q IH =>
    intro h_a_notin
    by_cases hb : b ∈ p.support
    · refine ⟨b, hb, a, hAdj.symm, ?_⟩
      intro he
      apply h_a_notin
      exact Walk.mem_support_of_mem_edges he (Sym2.mem_mk_right _ _)
    · exact IH hb

/-- If `p : G.Walk v v` is a trail, `G` is connected, and there is a `G`-edge
not in `p.edges`, then some vertex on `p` is incident to a `G`-edge that is
not in `p.edges`. -/
theorem boundary_vertex_of_remaining
    [Fintype V] [DecidableEq V]
    {v : V} (p : G.Walk v v) (hConn : G.Connected)
    {e₀ : Sym2 V} (he₀_G : e₀ ∈ G.edgeSet) (he₀_notin : e₀ ∉ p.edges) :
    ∃ w ∈ p.support, ∃ x : V, G.Adj w x ∧ s(w, x) ∉ p.edges := by
  induction e₀ using Sym2.ind with
  | h a b =>
    by_cases ha : a ∈ p.support
    · exact ⟨a, ha, b, G.mem_edgeSet.mp he₀_G, he₀_notin⟩
    · have hReach : G.Reachable a v := hConn.preconnected a v
      obtain ⟨pa⟩ := hReach
      exact boundary_along_walk pa ha

/-- For a closed trail `p` at `v`, the count of `p.edges` incident to any
vertex `x` is even. Uses Mathlib's `IsTrail.even_countP_edges_iff`. -/
theorem closed_trail_count_even
    [DecidableEq V]
    {v : V} {p : G.Walk v v} (hp : p.IsTrail) (x : V) :
    Even (List.countP (fun e => decide (x ∈ e)) p.edges) := by
  rw [hp.even_countP_edges_iff]
  intro hne
  exact (hne rfl).elim

/-- The neighbor finset of `G.deleteEdges S` is `(G.neighborFinset x).filter (s(x,·) ∉ S)`. -/
private theorem neighborFinset_deleteEdges_aux
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (x : V)
    [DecidableRel (G.deleteEdges (S : Set (Sym2 V))).Adj] :
    (G.deleteEdges (S : Set (Sym2 V))).neighborFinset x
      = (G.neighborFinset x).filter (fun y => s(x, y) ∉ S) := by
  ext y
  simp [mem_neighborFinset, deleteEdges_adj]

/-- The degree decomposition: `G.degree x = (G.deleteEdges S).degree x + #{p-edges at x}`. -/
private theorem degree_deleteEdges_decomp
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (x : V)
    [DecidableRel (G.deleteEdges (S : Set (Sym2 V))).Adj] :
    G.degree x =
      (G.deleteEdges (S : Set (Sym2 V))).degree x
        + ((G.neighborFinset x).filter (fun y => s(x, y) ∈ S)).card := by
  rw [degree, degree, neighborFinset_deleteEdges_aux]
  have := Finset.filter_card_add_filter_neg_card_eq_card (s := G.neighborFinset x)
    (p := fun y => s(x, y) ∉ S)
  have hflip : (G.neighborFinset x).filter (fun y => ¬ s(x, y) ∉ S)
      = (G.neighborFinset x).filter (fun y => s(x, y) ∈ S) := by
    apply Finset.filter_congr; intros; tauto
  rw [hflip] at this
  omega

/-- For closed trail `p`, the # of p-edges incident at `x` (as `neighborFinset` filter)
equals `(p.edges.filter (x ∈ ·)).length` (= the trail count at `x`). -/
private theorem neighbor_filter_eq_trail_count
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v : V} {p : G.Walk v v} (hp : p.IsTrail) (x : V) :
    ((G.neighborFinset x).filter (fun y => s(x, y) ∈ p.edges.toFinset)).card
      = (p.edges.filter (fun e => decide (x ∈ e))).length := by
  rw [← List.toFinset_card_of_nodup (hp.edges_nodup.filter _)]
  apply Finset.card_bij (fun y (hy : y ∈ (G.neighborFinset x).filter _) => s(x, y))
  · intro y hy
    simp only [Finset.mem_filter, mem_neighborFinset] at hy
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨?_, Sym2.mem_mk_left _ _⟩
    rw [List.mem_toFinset] at hy
    exact hy.2
  · intro a ha b hb hab
    simp only [Finset.mem_filter, mem_neighborFinset] at ha hb
    have hxa : x ≠ a := ha.1.ne
    rcases (Sym2.mk_eq_mk_iff (p := (x, a)) (q := (x, b))).mp hab with h | h
    · exact (Prod.mk.inj h).2
    · obtain ⟨_, h2⟩ := Prod.mk.inj h
      exact (hxa h2.symm).elim
  · intro e he
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨he_p, hxe⟩ := he
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.mem_iff] at hxe
      rcases hxe with rfl | rfl
      · refine ⟨b, ?_, rfl⟩
        simp only [Finset.mem_filter, mem_neighborFinset]
        refine ⟨?_, ?_⟩
        · exact (G.mem_edgeSet.mp ((Walk.edges_subset_edgeSet p) he_p))
        · simp [List.mem_toFinset, he_p]
      · refine ⟨a, ?_, ?_⟩
        · simp only [Finset.mem_filter, mem_neighborFinset]
          refine ⟨?_, ?_⟩
          · exact (G.mem_edgeSet.mp ((Walk.edges_subset_edgeSet p) he_p)).symm
          · rw [List.mem_toFinset, Sym2.eq_swap]; exact he_p
        · exact Sym2.eq_swap

/-- For a closed trail `p` in a graph `G` with all even degrees,
`(G.deleteEdges p.edges.toFinset).degree x` is even. -/
theorem deleteEdges_closed_trail_even_degree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v : V} {p : G.Walk v v} (hp : p.IsTrail)
    (hEven : ∀ x, Even (G.degree x)) (x : V)
    [DecidableRel (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).Adj] :
    Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) := by
  have h_decomp := degree_deleteEdges_decomp (G := G) p.edges.toFinset x
  have h_count := neighbor_filter_eq_trail_count (G := G) hp x
  have h_close := closed_trail_count_even hp x
  rw [List.countP_eq_length_filter] at h_close
  have h_filter_even :
      Even ((G.neighborFinset x).filter (fun y => s(x, y) ∈ p.edges.toFinset)).card := by
    rw [h_count]; exact h_close
  have hG := hEven x
  have hsum_even : Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x +
      ((G.neighborFinset x).filter (fun y => s(x, y) ∈ p.edges.toFinset)).card) := by
    rw [← h_decomp]; exact hG
  exact (Nat.even_add.mp hsum_even).mpr h_filter_even

/-- The boundary vertex `w` from `boundary_vertex_of_remaining` has positive degree
in `G.deleteEdges p.edges.toFinset`. -/
private theorem boundary_pos_degree_in_deleted
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v : V} (p : G.Walk v v) (hConn : G.Connected)
    (h_lt : p.edges.length < G.edgeFinset.card) (hp : p.IsTrail)
    [DecidableRel (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).Adj] :
    ∃ w ∈ p.support,
      0 < (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree w := by
  have h_ne_count : (p.edges.toFinset : Finset (Sym2 V)).card < G.edgeFinset.card := by
    calc (p.edges.toFinset).card
        ≤ p.edges.length := List.toFinset_card_le _
      _ < G.edgeFinset.card := h_lt
  have h_subset : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    rw [List.mem_toFinset] at he
    rw [G.mem_edgeFinset]; exact (Walk.edges_subset_edgeSet p) he
  obtain ⟨e₀, h_e₀_G, h_e₀_notin⟩ : ∃ e₀ ∈ G.edgeFinset, e₀ ∉ p.edges.toFinset := by
    by_contra habs
    push_neg at habs
    have : G.edgeFinset ⊆ p.edges.toFinset := habs
    have := Finset.card_le_card this
    omega
  rw [G.mem_edgeFinset] at h_e₀_G
  have h_e₀_notin_edges : e₀ ∉ p.edges := by
    intro he; apply h_e₀_notin; rw [List.mem_toFinset]; exact he
  obtain ⟨w, hw_supp, x, hAdj, h_e_notin⟩ :=
    boundary_vertex_of_remaining (G := G) p hConn h_e₀_G h_e₀_notin_edges
  refine ⟨w, hw_supp, ?_⟩
  have hAdj' : (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).Adj w x := by
    rw [deleteEdges_adj]
    refine ⟨hAdj, ?_⟩
    intro habs
    apply h_e_notin
    rw [Finset.mem_coe, List.mem_toFinset] at habs
    exact habs
  exact hAdj'.degree_pos_left

/-- **Main Hierholzer construction.** A connected graph with all even degrees admits
an Eulerian circuit. Proof by strong induction on `|G.edgeFinset| - |p.edges|`,
starting from a closed trail and iteratively splicing in fresh closed sub-trails
found via boundary vertices. -/
theorem hierholzer_main
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hConn : G.Connected) (hEven : ∀ x, Even (G.degree x)) :
    ∃ v, ∃ p : G.Walk v v, p.IsEulerian := by
  classical
  obtain ⟨v₀⟩ : Nonempty V := hConn.nonempty
  by_cases h_no_edge : G.edgeFinset.card = 0
  · refine ⟨v₀, Walk.nil, ?_⟩
    rw [Walk.isEulerian_iff]
    refine ⟨Walk.IsTrail.nil, ?_⟩
    intro e he
    rw [Finset.card_eq_zero] at h_no_edge
    have : e ∈ G.edgeFinset := G.mem_edgeFinset.mpr he
    rw [h_no_edge] at this
    exact (Finset.notMem_empty _ this).elim
  · have h_edges_pos : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero h_no_edge
    obtain ⟨v, hv⟩ : ∃ v, 0 < G.degree v := by
      by_contra habs
      push_neg at habs
      have : ∀ v, G.degree v = 0 := fun v => Nat.le_zero.mp (habs v)
      have h_sum_zero : ∑ x, G.degree x = 0 := by
        apply Finset.sum_eq_zero; intros; exact this _
      have h_sum := G.sum_degrees_eq_twice_card_edges
      omega
    obtain ⟨p₀, hp₀T, hp₀NE⟩ := closed_trail_of_pos_degree (G := G) hEven hv
    suffices h : ∀ k : ℕ, ∀ {v : V} (p : G.Walk v v),
        p.IsTrail → G.Connected → (∀ x, Even (G.degree x)) →
        G.edgeFinset.card - p.edges.length = k →
        ∃ q : G.Walk v v, q.IsEulerian by
      obtain ⟨q, hq⟩ := h _ p₀ hp₀T hConn hEven rfl
      exact ⟨v, q, hq⟩
    intro k
    induction k using Nat.strongRecOn with
    | _ k IH =>
      intro v p hpT hConn' hEven' hk
      by_cases h_full : p.edges.length = G.edgeFinset.card
      · refine ⟨p, ?_⟩
        rw [Walk.isEulerian_iff]
        refine ⟨hpT, ?_⟩
        intro e he
        have h1 : p.edges.toFinset.card = p.edges.length :=
          List.toFinset_card_of_nodup hpT.edges_nodup
        have h2 : p.edges.toFinset ⊆ G.edgeFinset := by
          intro e' he'; rw [List.mem_toFinset] at he'
          rw [G.mem_edgeFinset]; exact (Walk.edges_subset_edgeSet p) he'
        have h3 : p.edges.toFinset = G.edgeFinset :=
          Finset.eq_of_subset_of_card_le h2 (by rw [h1, h_full])
        have : e ∈ p.edges.toFinset := by
          rw [h3]; exact G.mem_edgeFinset.mpr he
        rwa [List.mem_toFinset] at this
      · have h_lt : p.edges.length < G.edgeFinset.card := by
          have h_le : p.edges.toFinset.card ≤ p.edges.length :=
            List.toFinset_card_le _
          have h_le2 : p.edges.toFinset.card ≤ G.edgeFinset.card := by
            apply Finset.card_le_card
            intro e' he'; rw [List.mem_toFinset] at he'
            rw [G.mem_edgeFinset]; exact (Walk.edges_subset_edgeSet p) he'
          have h_eq : p.edges.toFinset.card = p.edges.length :=
            List.toFinset_card_of_nodup hpT.edges_nodup
          omega
        haveI : DecidableRel (G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).Adj := fun a b =>
          decidable_of_iff (G.Adj a b ∧ s(a, b) ∉ p.edges.toFinset) (by
            rw [deleteEdges_adj]; rfl)
        obtain ⟨w, hw_supp, hw_pos⟩ :=
          boundary_pos_degree_in_deleted (G := G) p hConn' h_lt hpT
        have h_G'_even : ∀ x, Even ((G.deleteEdges (p.edges.toFinset : Set (Sym2 V))).degree x) :=
          fun x => deleteEdges_closed_trail_even_degree hpT hEven' x
        obtain ⟨Tw, hTwT, hTwNE⟩ :=
          closed_trail_of_pos_degree (G := G.deleteEdges (p.edges.toFinset : Set (Sym2 V)))
            h_G'_even hw_pos
        have h_Tw_edges_in_G : ∀ e ∈ Tw.edges, e ∈ G.edgeSet := by
          intro e he
          have := Tw.edges_subset_edgeSet he
          rw [edgeSet_deleteEdges] at this
          exact this.1
        let Tw_G : G.Walk w w := Tw.transfer G h_Tw_edges_in_G
        have hTw_G_T : Tw_G.IsTrail := by
          rw [Walk.isTrail_def]
          show (Tw.transfer G h_Tw_edges_in_G).edges.Nodup
          rw [Walk.edges_transfer]
          exact hTwT.edges_nodup
        have hTw_G_disj : Tw_G.edges.Disjoint p.edges := by
          show (Tw.transfer G h_Tw_edges_in_G).edges.Disjoint p.edges
          rw [Walk.edges_transfer]
          intro e he hep
          have := Tw.edges_subset_edgeSet he
          rw [edgeSet_deleteEdges] at this
          exact this.2 (by rw [Finset.mem_coe, List.mem_toFinset]; exact hep)
        obtain ⟨q, hqT, hq_perm⟩ :=
          Walk.splice_closed_trails p Tw_G hpT hTw_G_T hTw_G_disj.symm hw_supp
        have hq_len : q.edges.length = p.edges.length + Tw_G.edges.length := by
          rw [List.Perm.length_eq hq_perm, List.length_append]
        have hTw_G_len_pos : 0 < Tw_G.edges.length := by
          have hpos : Tw.edges.length > 0 := by
            cases h : Tw.edges with
            | nil => exact (hTwNE h).elim
            | cons _ _ => simp [h]
          show 0 < (Tw.transfer G h_Tw_edges_in_G).edges.length
          rwa [Walk.edges_transfer]
        have hq_decrease : G.edgeFinset.card - q.edges.length < k := by
          rw [hq_len]; omega
        exact IH _ hq_decrease q hqT hConn' hEven' rfl

/-- **Diestel Thm 1.8.1 (Euler 1736), full theorem.** A connected graph admits
an Eulerian circuit iff every vertex has even degree. Phrased on the existence
of an Eulerian closed walk. -/
theorem euler_1736_full
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hConn : G.Connected) :
    (∃ v, ∃ p : G.Walk v v, p.IsEulerian) ↔ ∀ x, Even (G.degree x) := by
  constructor
  · rintro ⟨_, p, hp⟩ x
    exact (hp.even_degree_iff).mpr (fun hne => (hne rfl).elim)
  · intro hEven
    exact hierholzer_main hConn hEven

end Walk

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A graph has an Eulerian circuit if some closed walk is Eulerian. -/
def HasEulerianCircuit : Prop := ∃ v, ∃ p : G.Walk v v, p.IsEulerian

/-- Easy direction (Diestel 1.8.1 ⇒): if `G` has an Eulerian circuit, every vertex
has even degree. -/
theorem HasEulerianCircuit.even_degree (h : G.HasEulerianCircuit) (x : V) :
    Even (G.degree x) := by
  obtain ⟨v, p, hp⟩ := h
  exact (hp.even_degree_iff (x := x)).mpr (fun hne => (hne rfl).elim)

/-- **Diestel Thm 1.8.1 (Euler 1736).** A connected graph has an Eulerian circuit
iff every vertex has even degree. The hard direction (⇐) is proved by Hierholzer's
algorithm in `SimpleGraph.Walk.hierholzer_main`. -/
theorem euler_1736 (hG : G.Connected) :
    G.HasEulerianCircuit ↔ ∀ x : V, Even (G.degree x) := by
  refine ⟨fun h x => HasEulerianCircuit.even_degree G h x, ?_⟩
  intro hEven
  exact Walk.hierholzer_main hG hEven

end SimpleGraph
