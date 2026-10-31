/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.SimpleGraph.BlockTree.Defs
import GraphTheory.SimpleGraph.Block.TwoConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-! # Acyclicity of the block-cut graph

The block-cut graph induced on `coreVertices` is acyclic, as in Diestel
Proposition 3.1.1 (Graph Theory, 5th edition, §3.1, p. 44).

An alleged cycle alternates between distinct blocks and cut vertices.
Join successive cut vertices by paths inside the intervening blocks.
Distinct blocks have disjoint edge sets, so the concatenation is a closed
trail in G. Its cycleBypass contains a cycle whose edges all belong to one
block. The per-block construction then puts all those cycle edges in one
path, a contradiction.

The proof uses block-internal path construction, disjointness of block edges,
and Mathlib's cycleBypass for trails. The main result is `BlockTree.isAcyclic`;
it also implies that two distinct blocks share at most one vertex. -/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.whitespace false

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

section BlockSubgraphReachable

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
/-- Vertices of an edge-containing block are joined by a walk whose edges
all belong to that block. Choose an incident edge at each endpoint. Equal
edges give reflexivity or a one-edge walk; otherwise use their common cycle,
all of whose edges belong to the block. -/
theorem exists_walk_in_blockSubgraph
    {b : G.Block} {u v : V}
    (hu : u ∈ G.blockVertices b) (hv : v ∈ G.blockVertices b) :
    ∃ w : G.Walk u v, ∀ e ∈ w.edges, e ∈ G.edgesInBlock b := by
  classical
  -- Choose block edges incident with u and v.
  rw [G.mem_blockVertices_iff] at hu hv
  obtain ⟨e_u, he_u, hu_in_eu⟩ := hu
  obtain ⟨e_v, he_v, hv_in_ev⟩ := hv
  -- SameBlockStep e_u e_v
  have hSBS : G.SameBlockStep e_u e_v :=
    G.sameBlockStep_of_mem_edgesInBlock he_u he_v
  rcases hSBS with heq | ⟨x, c, hc, hec_u, hec_v⟩
  · -- If the incident edges agree, both vertices lie on that edge.
    by_cases huv : u = v
    · subst huv
      exact ⟨Walk.nil, fun e he => by simp [Walk.edges_nil] at he⟩
    · -- Distinct endpoints identify the shared edge as s(u,v).
      subst heq
      have he_uv : e_u = s(u, v) := by
        induction e_u with
        | h x y =>
          rcases Sym2.mem_iff.mp hu_in_eu with hux | huy
          · rcases Sym2.mem_iff.mp hv_in_ev with hvx | hvy
            · exfalso; exact huv (hux.trans hvx.symm)
            · subst hux; subst hvy; rfl
          · rcases Sym2.mem_iff.mp hv_in_ev with hvx | hvy
            · subst huy; subst hvx; exact Sym2.eq_swap
            · exfalso; exact huv (huy.trans hvy.symm)
      have he_uv_G : s(u, v) ∈ G.edgeSet := by
        have he_uv_finset : e_u ∈ G.edgeFinset := (Finset.mem_filter.mp he_u).1
        have : e_u ∈ G.edgeSet := mem_edgeFinset.mp he_uv_finset
        rw [← he_uv]; exact this
      have hadj : G.Adj u v := he_uv_G
      refine ⟨Walk.cons hadj Walk.nil, ?_⟩
      intro e he
      simp [Walk.edges_cons, Walk.edges_nil] at he
      subst he
      rw [← he_uv]; exact he_u
  · -- The common cycle contains both incident edges and hence their endpoints.
    have hu_supp : u ∈ c.support := by
      induction e_u with
      | h a₀ b₀ =>
        rcases Sym2.mem_iff.mp hu_in_eu with hua | hub
        · subst hua; exact c.fst_mem_support_of_mem_edges hec_u
        · subst hub; exact c.snd_mem_support_of_mem_edges hec_u
    have hv_supp : v ∈ c.support := by
      induction e_v with
      | h a₀ b₀ =>
        rcases Sym2.mem_iff.mp hv_in_ev with hva | hvb
        · subst hva; exact c.fst_mem_support_of_mem_edges hec_v
        · subst hvb; exact c.snd_mem_support_of_mem_edges hec_v
    -- Every edge of that cycle belongs to the block.
    have hc_edges : ∀ f ∈ c.edges, f ∈ G.edgesInBlock b :=
      fun f hf => G.mem_edgesInBlock_of_mem_cycle_edges he_u hc hec_u hf
    -- Rotate the cycle to start at u.
    set cu : G.Walk u u := c.rotate u hu_supp with hcu_def
    have hcu_edges : cu.edges ~r c.edges := c.rotate_edges u hu_supp
    -- Rotation preserves membership of v in the support.
    have hv_cu : v ∈ cu.support := by
      rw [hcu_def]
      exact (Walk.mem_support_rotate_iff c u hu_supp).mpr hv_supp
    -- Take the prefix of the rotated cycle ending at v.
    refine ⟨cu.takeUntil v hv_cu, ?_⟩
    intro e he
    -- The prefix edges lie in the rotated cycle and hence in the original cycle.
    have he_cu : e ∈ cu.edges := cu.edges_takeUntil_subset hv_cu he
    have he_c : e ∈ c.edges := hcu_edges.mem_iff.mp he_cu
    exact hc_edges e he_c

open Classical in
/-- Vertices of an edge-containing block are joined by a path whose edges
all belong to that block. Apply Walk.toPath to the block-internal walk;
bypass preserves containment of its edge set. -/
theorem exists_path_in_blockSubgraph
    {b : G.Block} {u v : V}
    (hu : u ∈ G.blockVertices b) (hv : v ∈ G.blockVertices b) :
    ∃ p : G.Walk u v, p.IsPath ∧ ∀ e ∈ p.edges, e ∈ G.edgesInBlock b := by
  classical
  obtain ⟨w, hw_edges⟩ := G.exists_walk_in_blockSubgraph hu hv
  -- Bypass gives a path whose edges are contained in the original walk edges.
  refine ⟨w.bypass, w.bypass_isPath, ?_⟩
  intro e he
  exact hw_edges e (Walk.edges_bypass_subset w he)

end BlockSubgraphReachable

/-! ## A cycle cannot have all its edges in a path

A cycle based at an endpoint v has two distinct edges incident with v,
whereas a path from v to a different vertex has only one. Thus the cycle
edge set cannot be contained in the path edge set. -/

section CycleVsPath

variable {V : Type*} (G : SimpleGraph V)

omit G in
/-- A path with distinct endpoints has exactly one edge incident with
its initial vertex. -/
private theorem Walk.IsPath.count_edges_containing_start
    {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] {v w : V} (hvw : v ≠ w)
    (p : G.Walk v w) (hp : p.IsPath) :
    (p.edges.filter (v ∈ ·)).length = 1 := by
  -- Induct on the path.
  induction p with
  | nil => exact (hvw rfl).elim
  | @cons v u w hadj p' _ =>
    -- The tail remains a path and its support excludes the starting vertex.
    rw [Walk.cons_isPath_iff] at hp
    obtain ⟨_, hv_notin⟩ := hp
    -- edges(cons) = s(v,u) :: p'.edges
    rw [Walk.edges_cons]
    have hv_in_first : v ∈ s(v, u) := Sym2.mem_mk_left v u
    -- No tail edge contains the initial vertex, since the tail support excludes it.
    have hv_not_in_p'_edges : ∀ e ∈ p'.edges, v ∉ e := by
      intro e he hve
      apply hv_notin
      induction e with
      | h a b' =>
        rcases Sym2.mem_iff.mp hve with rfl | rfl
        · exact p'.fst_mem_support_of_mem_edges he
        · exact p'.snd_mem_support_of_mem_edges he
    -- Only the first edge survives the incidence filter.
    rw [List.filter_cons]
    simp only [hv_in_first, decide_true, if_true]
    -- The filtered tail edge list is empty.
    have hfilter_nil : p'.edges.filter (v ∈ ·) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      simp only [decide_eq_true_eq]
      exact hv_not_in_p'_edges e he
    rw [hfilter_nil]
    simp

omit G in
/-- A cycle based at v cannot have all its edges in a path from v to a
different vertex. The cycle has at least two incident edges at v, but the
path has exactly one, contradicting edge containment. -/
theorem Walk.cycle_edges_not_subset_path_edges
    {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {v w : V} (hvw : v ≠ w)
    (p : G.Walk v w) (hp : p.IsPath)
    (c : G.Walk v v) (hc : c.IsCycle)
    (hsub : ∀ e ∈ c.edges, e ∈ p.edges) : False := by
  -- A cycle has length at least three.
  have hclen : 3 ≤ c.length := hc.three_le_length
  -- Its first and last edges both contain the base vertex.
  -- Decompose the nonempty closed walk into its first edge and remaining walk.
  -- The last edge becomes the first edge after reversing the walk.
  -- The reversed closed walk is also a cycle.
  -- Count the cycle edges incident with the base vertex.
  -- The cycle's incident edges at its base are its first and last edges,
  -- because its support tail has no repetitions.
  -- The two edges differ because the cycle has length at least three.
  -- The incidence-filtered cycle edge list has length at least two.
  have hc_filter_ge2 : 2 ≤ (c.edges.filter (v ∈ ·)).length := by
    -- Exhibit the two distinct incident cycle edges.
    -- The first edge contains the starting vertex.
    -- The remaining walk ends at the same vertex, so its last edge also contains it.
    -- The cycle is a trail, so its first and last edges are distinct.
    --
    -- Decompose the cycle as a cons walk.
    match hcons : c, hc, hclen with
    | Walk.nil, hc', _ => exact (hc'.ne_nil rfl).elim
    | Walk.cons (v := u₁) h₁ rest₁, hc', hclen' =>
        -- c = cons h₁ rest₁; rest₁ : Walk u₁ v
        -- c.edges = s(v, u₁) :: rest₁.edges
        rw [Walk.edges_cons, List.filter_cons]
        have hv_first : v ∈ s(v, u₁) := Sym2.mem_mk_left v u₁
        simp only [hv_first, decide_true, if_true, List.length_cons]
        -- Goal: 2 ≤ (rest₁.edges.filter (v ∈ ·)).length + 1
        -- Wystarczy: 1 ≤ (rest₁.edges.filter (v ∈ ·)).length
        have hrest₁_len : 1 ≤ rest₁.length := by
          have hlen_cons : (Walk.cons h₁ rest₁).length = rest₁.length + 1 :=
            Walk.length_cons _ _
          omega
        -- The remaining walk is nonempty because its length is positive.
        have hrest_not_nil : ¬ rest₁.Nil := Walk.not_nil_iff_lt_length.mpr hrest₁_len
        -- Its last edge contains the final vertex v.
        let e : Sym2 V := s(rest₁.penultimate, v)
        have he_in : e ∈ rest₁.edges := rest₁.mk_penultimate_end_mem_edges hrest_not_nil
        have hve : v ∈ e := Sym2.mem_mk_right _ _
        have he_filter : e ∈ rest₁.edges.filter (v ∈ ·) := by
          rw [List.mem_filter]
          exact ⟨he_in, by simp [hve]⟩
        have hpos : 0 < (rest₁.edges.filter (v ∈ ·)).length :=
          List.length_pos_iff_exists_mem.mpr ⟨e, he_filter⟩
        omega
  -- Edge containment induces containment of the incidence-filtered edge lists.
  -- Nodup of both edge lists allows comparison by finite containment.
  have hc_trail : c.IsTrail := hc.isTrail
  have hc_nodup : c.edges.Nodup := hc_trail.edges_nodup
  -- Filtering preserves nodup.
  have hcfilter_nodup : (c.edges.filter (v ∈ ·)).Nodup := hc_nodup.filter _
  -- Each edge surviving the cycle filter also survives the path filter.
  have hsub_filter : ∀ e ∈ c.edges.filter (v ∈ ·), e ∈ p.edges.filter (v ∈ ·) := by
    intro e he
    rw [List.mem_filter] at he ⊢
    exact ⟨hsub e he.1, he.2⟩
  -- Nodup and containment give the length inequality for the filtered lists.
  have hle : (c.edges.filter (v ∈ ·)).length ≤ (p.edges.filter (v ∈ ·)).length := by
    -- Use Subperm and length_le.
    have hsubset : c.edges.filter (v ∈ ·) ⊆ p.edges.filter (v ∈ ·) := hsub_filter
    exact (hcfilter_nodup.subperm hsubset).length_le
  -- The path filter has length one by count_edges_containing_start.
  have hp_filter_one : (p.edges.filter (v ∈ ·)).length = 1 :=
    Walk.IsPath.count_edges_containing_start hvw p hp
  rw [hp_filter_one] at hle
  -- This gives the contradiction 2 ≤ 1.
  omega

end CycleVsPath

/-! ## Distinct blocks have disjoint edge sets

An edge belongs to at most one block, by block_decomposition. Thus walks
whose edges belong to distinct blocks have disjoint edge sets. -/

section BlocksDisjoint

variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Distinct blocks have disjoint edgesInBlock finsets. -/
theorem edgesInBlock_disjoint_of_ne {b₁ b₂ : G.Block}
    (hb₁ : b₁ ∈ G.blocks) (hb₂ : b₂ ∈ G.blocks) (hne : b₁ ≠ b₂) :
    Disjoint (G.edgesInBlock b₁) (G.edgesInBlock b₂) :=
  G.block_decomposition.2.2 b₁ hb₁ b₂ hb₂ hne

end BlocksDisjoint

/-! ## Acyclicity via block-internal paths

An alleged cycle in the bipartite core alternates between blocks and cut
vertices. Concatenate paths within successive blocks to obtain a closed
trail in G. Its cycleBypass gives a cycle whose edges belong to one block,
and therefore to one path in the construction, contradicting the cycle/path
edge-containment lemma. -/

section IsAcyclic

variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
/-- A block entry in coreVertices has a vertex in its block. -/
private theorem exists_vertex_in_inl_core
    {b : G.Block} (hb_core : Sum.inl b ∈ BlockTree.coreVertices G) :
    ∃ u : V, u ∈ G.blockVertices b := by
  classical
  have hb : b ∈ G.blocks := (BlockTree.mem_coreVertices_inl_iff G).mp hb_core
  have hne : (G.edgesInBlock b).Nonempty := G.block_decomposition.1 b hb
  obtain ⟨e, he⟩ := hne
  induction e with
  | h a c =>
    refine ⟨a, ?_⟩
    rw [G.mem_blockVertices_iff]
    exact ⟨s(a, c), he, Sym2.mem_mk_left a c⟩

/-! ### Mapping block-cut walks to walks in G

A walk through alternating block and cut-vertex entries gives a walk in G
by joining successive incident vertices inside each block. The construction
keeps a current original vertex associated with the block entry and handles
pairs of block-cut steps. -/

open Classical in
/-- Construct a walk in G from a block-to-block walk in the core.
Choose a path within the first block to the intervening cut vertex, then
recurse on the remaining pair of steps. For a closed block-cut walk, a
chosen vertex of the starting block serves as both endpoints. -/
private theorem buildWalkInG_aux :
    ∀ (n : ℕ) {b b' : G.Block}
      {hb_core : Sum.inl b ∈ BlockTree.coreVertices G}
      {hb'_core : Sum.inl b' ∈ BlockTree.coreVertices G}
      (W : ((G.BlockTree).induce (BlockTree.coreVertices G)).Walk
              ⟨Sum.inl b, hb_core⟩ ⟨Sum.inl b', hb'_core⟩)
      (_h_len : W.length = n)
      {u : V} (hu : u ∈ G.blockVertices b),
      ∃ (u' : V) (_hu' : u' ∈ G.blockVertices b') (q : G.Walk u u'),
        ∀ e ∈ q.edges, ∃ b'' : G.Block,
          (Sum.inl b'' ∈ BlockTree.coreVertices G) ∧ e ∈ G.edgesInBlock b'' := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro b b' hb_core hb'_core W h_len u hu
  -- Split the block-cut walk into nil and cons cases.
  match h_eq : W with
  | Walk.nil =>
      -- The nil case identifies the dependent endpoint block entries.
      refine ⟨u, hu, Walk.nil, ?_⟩
      intro e he; simp [Walk.edges_nil] at he
  | Walk.cons (v := mid) hadj p =>
      -- For a cons walk, inspect the intermediate core vertex.
      rcases mid with ⟨mid_val, hmid_core⟩
      rcases mid_val with mid_b | mid_v
      · -- Two block entries cannot be adjacent.
        rw [SimpleGraph.induce_adj] at hadj
        exact (BlockTree.not_adj_inl_inl G b mid_b hadj).elim
      · -- mid = inr mid_v
        have hadj_BT_first : (G.BlockTree).Adj (Sum.inl b) (Sum.inr mid_v) := by
          have := hadj
          rw [SimpleGraph.induce_adj] at this
          exact this
        have hmid_v_in_b : mid_v ∈ G.blockVertices b :=
          ((BlockTree.adj_inl_inr_iff G b mid_v).mp hadj_BT_first).2
        -- Path inside b: u → mid_v
        obtain ⟨w₁, hw₁_path, hw₁_edges⟩ :=
          G.exists_path_in_blockSubgraph hu hmid_v_in_b
        -- p : Walk ⟨inr mid_v, hmid_core⟩ ⟨inl b', hb'_core⟩
        -- The remaining walk is nonempty because its endpoint sum constructors differ.
        match hp_eq : p with
        | Walk.cons (v := mid₂_full) hadj₂ p₂ =>
            rcases mid₂_full with ⟨mid₂_val, hmid₂_core⟩
            rcases mid₂_val with b'' | v''
            · -- mid₂ = inl b''
              have hadj_BT_2 : (G.BlockTree).Adj (Sum.inr mid_v) (Sum.inl b'') := by
                have := hadj₂
                rw [SimpleGraph.induce_adj] at this
                exact this
              have hmid_v_in_b'' : mid_v ∈ G.blockVertices b'' :=
                ((BlockTree.adj_inr_inl_iff G mid_v b'').mp hadj_BT_2).2
              -- p₂ : Walk ⟨inl b'', hmid₂_core⟩ ⟨inl b', hb'_core⟩
              -- p₂.length < W.length = n
              have hp₂_lt : p₂.length < n := by
                rw [← h_len]
                simp only [Walk.length_cons]
                omega
              obtain ⟨u', hu'_in, q_rec, hq_rec⟩ :=
                ih p₂.length hp₂_lt p₂ rfl hmid_v_in_b''
              refine ⟨u', hu'_in, w₁.append q_rec, ?_⟩
              intro e he
              rw [Walk.edges_append, List.mem_append] at he
              rcases he with he₁ | he_rec
              · refine ⟨b, hb_core, hw₁_edges e he₁⟩
              · exact hq_rec e he_rec
            · -- Two right-hand vertex entries cannot be adjacent.
              rw [SimpleGraph.induce_adj] at hadj₂
              exact (BlockTree.not_adj_inr_inr G mid_v v'' hadj₂).elim

/-! ### Arbitrary paths cannot contain all edges of a cycle

The path may start anywhere, not necessarily at the cycle base. Induct on
its edge list. If its first edge lies on the cycle, the path's initial vertex
would have two incident cycle edges but only one incident path edge.
Otherwise discard the first path edge and apply induction. -/

omit G in
/-- Every support vertex of a cycle is incident with at least two cycle
edges. Rotate the cycle to that vertex, then use its first and last edges. -/
private theorem Walk.IsCycle.two_le_count_edges_containing
    {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {x : V} (hx : x ∈ c.support) :
    2 ≤ (c.edges.filter (x ∈ ·)).length := by
  -- Rotate the cycle to start at x, then apply
  -- the incident-edge argument for a cycle's starting vertex.
  set c' : G.Walk x x := c.rotate x hx with hc'_def
  have hc'_isCycle : c'.IsCycle := hc.rotate hx
  -- Rotation permutes the cycle edge list.
  have hrot : c'.edges ~r c.edges := c.rotate_edges x hx
  -- A permutation preserves the number of edges incident with x.
  have hcount_eq : (c'.edges.filter (x ∈ ·)).length =
      (c.edges.filter (x ∈ ·)).length := by
    have hperm' : c'.edges.Perm c.edges := hrot.perm
    have hperm_filter :
        (c'.edges.filter (x ∈ ·)).Perm (c.edges.filter (x ∈ ·)) :=
      hperm'.filter _
    exact hperm_filter.length_eq
  rw [← hcount_eq]
  -- Analyze the rotated cycle, now based at x.
  have hclen : 3 ≤ c'.length := hc'_isCycle.three_le_length
  -- c' = cons h₁ rest₁
  match hcons : c', hc'_isCycle, hclen with
  | Walk.nil, hc'', _ => exact (hc''.ne_nil rfl).elim
  | Walk.cons (v := u₁) h₁ rest₁, _, hclen' =>
      rw [Walk.edges_cons, List.filter_cons]
      have hx_first : x ∈ s(x, u₁) := Sym2.mem_mk_left x u₁
      simp only [hx_first, decide_true, if_true, List.length_cons]
      have hrest₁_len : 1 ≤ rest₁.length := by
        have hlen_cons : (Walk.cons h₁ rest₁).length = rest₁.length + 1 :=
          Walk.length_cons _ _
        omega
      have hrest_not_nil : ¬ rest₁.Nil := Walk.not_nil_iff_lt_length.mpr hrest₁_len
      let e : Sym2 V := s(rest₁.penultimate, x)
      have he_in : e ∈ rest₁.edges := rest₁.mk_penultimate_end_mem_edges hrest_not_nil
      have hxe : x ∈ e := Sym2.mem_mk_right _ _
      have he_filter : e ∈ rest₁.edges.filter (x ∈ ·) := by
        rw [List.mem_filter]
        exact ⟨he_in, by simp [hxe]⟩
      have hpos : 0 < (rest₁.edges.filter (x ∈ ·)).length :=
        List.length_pos_iff_exists_mem.mpr ⟨e, he_filter⟩
      omega

omit G in
/-- No cycle has all its edges in an arbitrary path. Induct on the path.
The nil case has no edges. In the cons case, either the first edge belongs
to the cycle, contradicting the incident-edge counts at the path's initial
vertex, or it can be removed before applying induction. -/
private theorem Walk.cycle_edges_not_subset_path_edges_general
    {V : Type*} {G : SimpleGraph V} [DecidableEq V]
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    ∀ {u w : V} (p : G.Walk u w), p.IsPath →
      (∀ e ∈ c.edges, e ∈ p.edges) → False := by
  intro u w p
  induction p with
  | nil =>
      intro _ hsub
      -- c.edges ⊆ Walk.nil.edges = []
      have hclen : 3 ≤ c.length := hc.three_le_length
      have hc_edges_pos : 0 < c.edges.length := by
        have h_len_eq : c.edges.length = c.length := c.length_edges
        omega
      obtain ⟨e, he⟩ := List.length_pos_iff_exists_mem.mp hc_edges_pos
      have := hsub e he
      simp [Walk.edges_nil] at this
  | @cons u u₁ w hadj p_tail ih =>
      intro hp hsub
      rw [Walk.cons_isPath_iff] at hp
      obtain ⟨hp_tail, hu_notin⟩ := hp
      -- The first path edge is s(u,u_1).
      -- If that edge lies on the cycle, then u belongs to the cycle support.
      -- The cycle has at least two edges incident with u, but the path has one,
      -- since u is its starting endpoint.
      -- Thus the first path edge is absent from the cycle, allowing induction on the tail.
      by_cases hu_in_c : u ∈ c.support
      · -- The vertex u lies in the cycle support.
        -- At least two cycle edges contain u.
        have hc_count := Walk.IsCycle.two_le_count_edges_containing hc hu_in_c
        -- Exactly one path edge contains u.
        have hu_ne_w : u ≠ w := by
          intro hu_eq_w
          subst hu_eq_w
          exact hu_notin p_tail.end_mem_support
        have hp_count_orig : ((Walk.cons hadj p_tail).edges.filter (u ∈ ·)).length = 1 :=
          Walk.IsPath.count_edges_containing_start hu_ne_w (Walk.cons hadj p_tail)
            ((Walk.cons_isPath_iff hadj p_tail).mpr ⟨hp_tail, hu_notin⟩)
        -- Edge containment induces containment after the incidence filter.
        have hc_trail : c.IsTrail := hc.isTrail
        have hc_nodup : c.edges.Nodup := hc_trail.edges_nodup
        have hcfilter_nodup : (c.edges.filter (u ∈ ·)).Nodup := hc_nodup.filter _
        have hsub_filter : ∀ e ∈ c.edges.filter (u ∈ ·),
            e ∈ (Walk.cons hadj p_tail).edges.filter (u ∈ ·) := by
          intro e he
          rw [List.mem_filter] at he ⊢
          exact ⟨hsub e he.1, he.2⟩
        have hsubset : c.edges.filter (u ∈ ·) ⊆
            (Walk.cons hadj p_tail).edges.filter (u ∈ ·) := hsub_filter
        have hle : (c.edges.filter (u ∈ ·)).length ≤
            ((Walk.cons hadj p_tail).edges.filter (u ∈ ·)).length :=
          (hcfilter_nodup.subperm hsubset).length_le
        rw [hp_count_orig] at hle
        omega
      · -- u ∉ c.support
        -- If u is absent from the cycle support, its incident first path edge is absent too.
        have h_first_notin : s(u, u₁) ∉ c.edges := by
          intro he
          apply hu_in_c
          exact c.fst_mem_support_of_mem_edges he
        -- c.edges ⊆ p_tail.edges
        have hsub_tail : ∀ e ∈ c.edges, e ∈ p_tail.edges := by
          intro e he
          have : e ∈ (Walk.cons hadj p_tail).edges := hsub e he
          simp only [Walk.edges_cons, List.mem_cons] at this
          rcases this with h_eq | h_in
          · subst h_eq; exact (h_first_notin he).elim
          · exact h_in
        exact ih hp_tail hsub_tail

/-! ## A closed trail in G from a block-cut cycle

Rotate the alleged core cycle to start at a cut-vertex entry. Concatenate
paths within its successive blocks. Distinct blocks have disjoint edges,
so the result is a trail. The construction also ensures that all edges
associated with any one block lie in a single path. Its cycleBypass would
then put a complete cycle in one such path, a contradiction. -/

section IsAcyclicBuild

variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge belonging to two blocks forces those blocks to be equal,
since blockOf is uniquely determined. -/
private theorem block_eq_of_mem_edgesInBlock_both {b₁ b₂ : G.Block} {e : Sym2 V}
    (h₁ : e ∈ G.edgesInBlock b₁) (h₂ : e ∈ G.edgesInBlock b₂) : b₁ = b₂ := by
  classical
  simp only [SimpleGraph.edgesInBlock, Finset.mem_filter] at h₁ h₂
  rw [← h₁.2, ← h₂.2]

open Classical in
/-- Every core cycle contains a cut-vertex entry `inr v`. It has an edge,
and each core edge joins opposite sides of the sum, so both types of entry
occur in the cycle support. -/
private theorem exists_inr_mem_support_of_isCycle
    {Z : ↥(BlockTree.coreVertices G)}
    {C : ((G.BlockTree).induce (BlockTree.coreVertices G)).Walk Z Z}
    (hC : C.IsCycle) :
    ∃ (W : ↥(BlockTree.coreVertices G)) (v : V),
      W.val = Sum.inr v ∧ W ∈ C.support := by
  classical
  have hlen : 3 ≤ C.length := hC.three_le_length
  obtain ⟨e, he⟩ := List.length_pos_iff_exists_mem.mp
    (show 0 < C.edges.length by rw [C.length_edges]; omega)
  induction e with
  | h a b =>
    have ha : a ∈ C.support := C.fst_mem_support_of_mem_edges he
    have hb : b ∈ C.support := C.snd_mem_support_of_mem_edges he
    have hadj : ((G.BlockTree).induce (BlockTree.coreVertices G)).Adj a b := by
      have hmem : s(a, b) ∈
          ((G.BlockTree).induce (BlockTree.coreVertices G)).edgeSet :=
        C.edges_subset_edgeSet he
      rwa [mem_edgeSet] at hmem
    rw [SimpleGraph.induce_adj, BlockTree.adj_iff] at hadj
    rcases hadj with ⟨bb, vv, _, hby, _, _⟩ | ⟨bb, vv, hax, _, _, _⟩
    · exact ⟨b, vv, hby, hb⟩
    · exact ⟨a, vv, hax, ha⟩

/-- Appending a path in block b to a trail using only blocks from a list
S that excludes b preserves the trail property and the per-block path
containment invariants. -/
private theorem combineBlockPath (b : G.Block)
    (S : List (G.Block ⊕ V))
    (hb_notin : (Sum.inl b : G.Block ⊕ V) ∉ S)
    {x s' t : V}
    (w : G.Walk x s') (hw_path : w.IsPath)
    (hw_block : ∀ e ∈ w.edges, e ∈ G.edgesInBlock b)
    (q' : G.Walk s' t) (hq'_trail : q'.IsTrail)
    (hq'_supp : ∀ e ∈ q'.edges, ∃ b'' : G.Block,
        (Sum.inl b'' : G.Block ⊕ V) ∈ S ∧ e ∈ G.edgesInBlock b'')
    (hq'_path : ∀ bq : G.Block, ∃ (a c : V) (p : G.Walk a c), p.IsPath ∧
        ∀ e ∈ q'.edges, e ∈ G.edgesInBlock bq → e ∈ p.edges) :
    (w.append q').IsTrail ∧
    (∀ e ∈ (w.append q').edges, ∃ b'' : G.Block,
        (Sum.inl b'' : G.Block ⊕ V) ∈ (Sum.inl b :: S) ∧ e ∈ G.edgesInBlock b'') ∧
    (∀ bq : G.Block, ∃ (a c : V) (p : G.Walk a c), p.IsPath ∧
        ∀ e ∈ (w.append q').edges, e ∈ G.edgesInBlock bq → e ∈ p.edges) := by
  classical
  have hq'_avoid : ∀ e ∈ q'.edges, e ∉ G.edgesInBlock b := by
    intro e he hb_mem
    obtain ⟨b'', hb''_S, he_b''⟩ := hq'_supp e he
    have hbe : b'' = b := G.block_eq_of_mem_edgesInBlock_both he_b'' hb_mem
    rw [hbe] at hb''_S
    exact hb_notin hb''_S
  have hdisj : ∀ e ∈ w.edges, e ∉ q'.edges := fun e hew heq =>
    hq'_avoid e heq (hw_block e hew)
  have htrail : (w.append q').IsTrail := by
    rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
    refine ⟨hw_path.edges_nodup, hq'_trail.edges_nodup, ?_⟩
    intro a ha c hc hac
    exact hdisj a ha (hac ▸ hc)
  refine ⟨htrail, ?_, ?_⟩
  · intro e he
    rw [Walk.edges_append, List.mem_append] at he
    rcases he with hew | heq
    · exact ⟨b, List.mem_cons_self, hw_block e hew⟩
    · obtain ⟨b'', hb''_S, he_b''⟩ := hq'_supp e heq
      exact ⟨b'', List.mem_cons_of_mem _ hb''_S, he_b''⟩
  · intro bq
    by_cases hbq : bq = b
    · subst hbq
      refine ⟨x, s', w, hw_path, ?_⟩
      intro e he hbq_mem
      rw [Walk.edges_append, List.mem_append] at he
      rcases he with hew | heq
      · exact hew
      · exact absurd hbq_mem (hq'_avoid e heq)
    · obtain ⟨a, c, p, hp_path, hp_sub⟩ := hq'_path bq
      refine ⟨a, c, p, hp_path, ?_⟩
      intro e he hbq_mem
      rw [Walk.edges_append, List.mem_append] at he
      rcases he with hew | heq
      · exact absurd (G.block_eq_of_mem_edgesInBlock_both (hw_block e hew) hbq_mem).symm hbq
      · exact hp_sub e heq hbq_mem

/-- A path in the core between cut-vertex entries gives a trail in G.
Each trail edge belongs to a block appearing in the core path support;
for each block, the corresponding edges lie in one block-internal path.
Induct on length, processing two alternating steps at a time. -/
private theorem buildTrail :
    ∀ (n : ℕ) {s t : V}
      {hs : Sum.inr s ∈ BlockTree.coreVertices G}
      {ht : Sum.inr t ∈ BlockTree.coreVertices G}
      (P : ((G.BlockTree).induce (BlockTree.coreVertices G)).Walk
              ⟨Sum.inr s, hs⟩ ⟨Sum.inr t, ht⟩)
      (_hlen : P.length = n) (_hpath : P.IsPath),
      ∃ q : G.Walk s t, q.IsTrail ∧
        (∀ e ∈ q.edges, ∃ b : G.Block,
            (Sum.inl b : G.Block ⊕ V) ∈ P.support.map Subtype.val ∧
            e ∈ G.edgesInBlock b) ∧
        (∀ bq : G.Block, ∃ (a c : V) (p : G.Walk a c), p.IsPath ∧
            ∀ e ∈ q.edges, e ∈ G.edgesInBlock bq → e ∈ p.edges) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t hs ht P hlen hpath
  match hPeq : P with
  | Walk.nil =>
      refine ⟨Walk.nil, Walk.IsTrail.nil, ?_, ?_⟩
      · intro e he; simp [Walk.edges_nil] at he
      · intro bq
        exact ⟨s, s, Walk.nil, Walk.IsPath.nil,
          by intro e he; simp [Walk.edges_nil] at he⟩
  | Walk.cons (v := mid) hadj rest =>
      rcases mid with ⟨mid_val, hmid_core⟩
      rcases mid_val with mid_b | mid_v
      · -- mid = inl mid_b
        have hadj_BT : (G.BlockTree).Adj (Sum.inr s) (Sum.inl mid_b) := by
          have h := hadj; rw [SimpleGraph.induce_adj] at h; exact h
        have hs_in_b : s ∈ G.blockVertices mid_b :=
          ((BlockTree.adj_inr_inl_iff G s mid_b).mp hadj_BT).2
        match hrestEq : rest with
        | Walk.cons (v := mid2) hadj2 P' =>
            rcases mid2 with ⟨mid2_val, hmid2_core⟩
            rcases mid2_val with b2 | v2
            · rw [SimpleGraph.induce_adj] at hadj2
              exact (BlockTree.not_adj_inl_inl G mid_b b2 hadj2).elim
            · -- mid2 = inr v2
              have hadj_BT2 : (G.BlockTree).Adj (Sum.inl mid_b) (Sum.inr v2) := by
                have h := hadj2; rw [SimpleGraph.induce_adj] at h; exact h
              have hv2_in_b : v2 ∈ G.blockVertices mid_b :=
                ((BlockTree.adj_inl_inr_iff G mid_b v2).mp hadj_BT2).2
              obtain ⟨w, hw_path, hw_edges⟩ :=
                G.exists_path_in_blockSubgraph hs_in_b hv2_in_b
              have hP'_lt : P'.length < n := by
                rw [← hlen]; simp only [Walk.length_cons]; omega
              have hpath_rest := ((Walk.cons_isPath_iff _ _).mp hpath).1
              have hpath_P' := ((Walk.cons_isPath_iff _ _).mp hpath_rest).1
              have hmidb_notin_P' := ((Walk.cons_isPath_iff _ _).mp hpath_rest).2
              obtain ⟨q', hq'_trail, hq'_supp, hq'_path⟩ :=
                ih P'.length hP'_lt P' rfl hpath_P'
              have hb_notin :
                  (Sum.inl mid_b : G.Block ⊕ V)
                    ∉ P'.support.map Subtype.val := by
                intro hmem
                rw [List.mem_map] at hmem
                obtain ⟨z, hz_mem, hz_val⟩ := hmem
                have hz_eq : z = ⟨Sum.inl mid_b, hmid_core⟩ := Subtype.ext hz_val
                rw [hz_eq] at hz_mem
                exact hmidb_notin_P' hz_mem
              obtain ⟨hq_trail, hq_supp_pre, hq_path⟩ :=
                G.combineBlockPath mid_b (P'.support.map Subtype.val) hb_notin
                  w hw_path hw_edges q' hq'_trail hq'_supp hq'_path
              refine ⟨w.append q', hq_trail, ?_, hq_path⟩
              intro e he
              obtain ⟨b'', hb''_mem, he_b''⟩ := hq_supp_pre e he
              refine ⟨b'', ?_, he_b''⟩
              simp only [Walk.support_cons, List.map_cons]
              exact List.mem_cons_of_mem _ hb''_mem
      · -- Two right-hand vertex entries cannot be adjacent.
        rw [SimpleGraph.induce_adj] at hadj
        exact (BlockTree.not_adj_inr_inr G s mid_v hadj).elim

end IsAcyclicBuild

/-! ## Assembling the acyclicity argument

`combineBlockPath` preserves the trail and per-block containment properties.
`buildTrail` constructs such a trail from a core path between cut vertices.
`cycle_inr_absurd` applies cycleBypass to an alleged core cycle and contradicts
the cycle/path edge-containment lemma. Finally `BlockTree.isAcyclic` rotates
an arbitrary core cycle to a cut-vertex entry and applies that contradiction. -/

end IsAcyclic

/-! ## Acyclicity of the core block-cut graph -/

section IsAcyclicMain

variable {V : Type*} (G : SimpleGraph V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- A core cycle based at a cut-vertex entry is impossible. Split off
its first block path and use buildTrail for the rest. Their concatenation
is a closed trail; its cycleBypass gives a cycle contained in the edges of
one block and hence one path, contradicting the general containment lemma. -/
private theorem cycle_inr_absurd {v0 : V}
    (hv0c : (Sum.inr v0 : G.Block ⊕ V) ∈ BlockTree.coreVertices G)
    (C₀ : ((G.BlockTree).induce (BlockTree.coreVertices G)).Walk
            ⟨Sum.inr v0, hv0c⟩ ⟨Sum.inr v0, hv0c⟩)
    (hC₀ : C₀.IsCycle) : False := by
  classical
  match hC0eq : C₀ with
  | Walk.nil => exact Walk.IsCycle.not_of_nil hC₀
  | Walk.cons (v := mid1) hadj1 rest1 =>
      rcases mid1 with ⟨mid1_val, hmid1_core⟩
      rcases mid1_val with b1 | u1
      · -- mid1 = inl b1
        have hadj_BT1 : (G.BlockTree).Adj (Sum.inr v0) (Sum.inl b1) := by
          have h := hadj1; rw [SimpleGraph.induce_adj] at h; exact h
        have hv0_in_b1 : v0 ∈ G.blockVertices b1 :=
          ((BlockTree.adj_inr_inl_iff G v0 b1).mp hadj_BT1).2
        match hrest1eq : rest1 with
        | Walk.cons (v := mid2) hadj2 P' =>
            rcases mid2 with ⟨mid2_val, hmid2_core⟩
            rcases mid2_val with b2 | s'
            · rw [SimpleGraph.induce_adj] at hadj2
              exact (BlockTree.not_adj_inl_inl G b1 b2 hadj2).elim
            · -- mid2 = inr s'
              have hadj_BT2 : (G.BlockTree).Adj (Sum.inl b1) (Sum.inr s') := by
                have h := hadj2; rw [SimpleGraph.induce_adj] at h; exact h
              have hs'_in_b1 : s' ∈ G.blockVertices b1 :=
                ((BlockTree.adj_inl_inr_iff G b1 s').mp hadj_BT2).2
              -- support.tail nodup: ⟨inl b1⟩ :: P'.support
              have htail_nodup :
                  (⟨Sum.inl b1, hmid1_core⟩ :: P'.support).Nodup := hC₀.support_nodup
              have hP'_path : P'.IsPath :=
                Walk.IsPath.mk' (List.nodup_cons.mp htail_nodup).2
              have hb1_notin :
                  (⟨Sum.inl b1, hmid1_core⟩ : ↥(BlockTree.coreVertices G))
                    ∉ P'.support := (List.nodup_cons.mp htail_nodup).1
              have hP'_pos : 1 ≤ P'.length := by
                have h3 := hC₀.three_le_length
                simp only [Walk.length_cons] at h3
                omega
              have hs'_ne_v0 : s' ≠ v0 := by
                intro hev
                subst hev
                have hP'_nil : P' = Walk.nil :=
                  (Walk.isPath_iff_eq_nil P').mp hP'_path
                rw [hP'_nil] at hP'_pos
                simp [Walk.length_nil] at hP'_pos
              -- Choose the path from v0 to s' within the first block.
              obtain ⟨w, hw_path, hw_edges⟩ :=
                G.exists_path_in_blockSubgraph hv0_in_b1 hs'_in_b1
              -- Construct the trail corresponding to the rest of the cycle.
              obtain ⟨q', hq'_trail, hq'_supp, hq'_path⟩ :=
                G.buildTrail P'.length P' rfl hP'_path
              -- The first block entry is absent from the remaining path support.
              have hb1_notin_map :
                  (Sum.inl b1 : G.Block ⊕ V) ∉ P'.support.map Subtype.val := by
                intro hmem
                rw [List.mem_map] at hmem
                obtain ⟨z, hz_mem, hz_val⟩ := hmem
                have hz_eq : z = ⟨Sum.inl b1, hmid1_core⟩ := Subtype.ext hz_val
                rw [hz_eq] at hz_mem
                exact hb1_notin hz_mem
              obtain ⟨hW_trail, _hW_supp, hW_path⟩ :=
                G.combineBlockPath b1 (P'.support.map Subtype.val) hb1_notin_map
                  w hw_path hw_edges q' hq'_trail hq'_supp hq'_path
              -- W = w.append q' ≠ nil
              have hw_not_nil : ¬ w.Nil := Walk.not_nil_of_ne (Ne.symm hs'_ne_v0)
              have hw_pos : 1 ≤ w.length := by
                rw [Walk.nil_iff_length_eq] at hw_not_nil; omega
              have hW_ne_nil : (w.append q') ≠ Walk.nil := by
                intro h
                have : 1 ≤ (w.append q').length := by
                  rw [Walk.length_append]; omega
                rw [h] at this; simp [Walk.length_nil] at this
              -- Extract a cycle using cycleBypass.
              set Wc := (w.append q').cycleBypass with hWc_def
              have hWc_cycle : Wc.IsCycle :=
                Walk.IsTrail.isCycle_cycleBypass hW_ne_nil hW_trail
              have hWc_sub : ∀ e ∈ Wc.edges, e ∈ (w.append q').edges :=
                fun e he => Walk.edges_cycleBypass_subset he
              obtain ⟨e0, he0⟩ := List.length_pos_iff_exists_mem.mp
                (show 0 < Wc.edges.length by
                  rw [Wc.length_edges]; have := hWc_cycle.three_le_length; omega)
              have he0_W : e0 ∈ (w.append q').edges := hWc_sub e0 he0
              obtain ⟨bstar, _hbstar, he0_block⟩ := _hW_supp e0 he0_W
              have hWc_all_block : ∀ f ∈ Wc.edges, f ∈ G.edgesInBlock bstar :=
                fun f hf =>
                  G.mem_edgesInBlock_of_mem_cycle_edges he0_block hWc_cycle he0 hf
              obtain ⟨pa, pc, pp, hpp_path, hpp_sub⟩ := hW_path bstar
              have hWc_in_pp : ∀ e ∈ Wc.edges, e ∈ pp.edges :=
                fun f hf => hpp_sub f (hWc_sub f hf) (hWc_all_block f hf)
              exact Walk.cycle_edges_not_subset_path_edges_general
                Wc hWc_cycle pp hpp_path hWc_in_pp
      · -- Two right-hand vertex entries cannot be adjacent.
        rw [SimpleGraph.induce_adj] at hadj1
        exact (BlockTree.not_adj_inr_inr G v0 u1 hadj1).elim

/-- The core block-cut graph is acyclic. Rotate any alleged cycle to
start at a cut-vertex entry and apply cycle_inr_absurd. -/
theorem BlockTree.isAcyclic :
    ((G.BlockTree).induce (BlockTree.coreVertices G)).IsAcyclic := by
  classical
  intro Z C hC
  obtain ⟨W0, v0, hW0_val, hW0_supp⟩ :=
    exists_inr_mem_support_of_isCycle G hC
  have hv0c : (Sum.inr v0 : G.Block ⊕ V) ∈ BlockTree.coreVertices G :=
    hW0_val ▸ W0.2
  have hW0_eq : W0 = ⟨Sum.inr v0, hv0c⟩ := Subtype.ext hW0_val
  have hC₀ : ((C.rotate W0 hW0_supp).copy hW0_eq hW0_eq).IsCycle := by
    rw [Walk.isCycle_copy]
    exact hC.rotate hW0_supp
  exact G.cycle_inr_absurd hv0c _ hC₀

/-- Two distinct blocks share at most one vertex (Diestel §3.1, Exercise 5).
Two distinct common vertices would give two different length-two paths
between the block entries in the acyclic core block-cut graph. -/
theorem card_inter_blockVertices_le_one {b₁ b₂ : G.Block}
    (hb₁ : b₁ ∈ G.blocks) (hb₂ : b₂ ∈ G.blocks) (hne : b₁ ≠ b₂) :
    (G.blockVertices b₁ ∩ G.blockVertices b₂).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro u v hu hv
  obtain ⟨hu₁, hu₂⟩ := Finset.mem_inter.mp hu
  obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
  have hucut : G.IsCutVertex u :=
    isCutVertex_of_mem_two_blocks G hb₁ hb₂ hne hu₁ hu₂
  have hvcut : G.IsCutVertex v :=
    isCutVertex_of_mem_two_blocks G hb₁ hb₂ hne hv₁ hv₂
  let B₁ : ↥(BlockTree.coreVertices G) :=
    ⟨Sum.inl b₁, BlockTree.inl_mem_coreVertices G hb₁⟩
  let B₂ : ↥(BlockTree.coreVertices G) :=
    ⟨Sum.inl b₂, BlockTree.inl_mem_coreVertices G hb₂⟩
  let U : ↥(BlockTree.coreVertices G) :=
    ⟨Sum.inr u, BlockTree.inr_mem_coreVertices G hucut⟩
  let W : ↥(BlockTree.coreVertices G) :=
    ⟨Sum.inr v, BlockTree.inr_mem_coreVertices G hvcut⟩
  let T := (G.BlockTree).induce (BlockTree.coreVertices G)
  have hB₁U : T.Adj B₁ U := by
    rw [SimpleGraph.induce_adj]
    exact (BlockTree.adj_inl_inr_iff G b₁ u).mpr ⟨hucut, hu₁⟩
  have hUB₂ : T.Adj U B₂ := by
    rw [SimpleGraph.induce_adj]
    exact (BlockTree.adj_inr_inl_iff G u b₂).mpr ⟨hucut, hu₂⟩
  have hB₁W : T.Adj B₁ W := by
    rw [SimpleGraph.induce_adj]
    exact (BlockTree.adj_inl_inr_iff G b₁ v).mpr ⟨hvcut, hv₁⟩
  have hWB₂ : T.Adj W B₂ := by
    rw [SimpleGraph.induce_adj]
    exact (BlockTree.adj_inr_inl_iff G v b₂).mpr ⟨hvcut, hv₂⟩
  let p : T.Walk B₁ B₂ := Walk.cons hB₁U (Walk.cons hUB₂ Walk.nil)
  let q : T.Walk B₁ B₂ := Walk.cons hB₁W (Walk.cons hWB₂ Walk.nil)
  have hp : p.IsPath := by
    rw [Walk.isPath_def]
    simp [p, B₁, B₂, U, hne]
  have hq : q.IsPath := by
    rw [Walk.isPath_def]
    simp [q, B₁, B₂, W, hne]
  have hpq : (⟨p, hp⟩ : T.Path B₁ B₂) = ⟨q, hq⟩ :=
    (BlockTree.isAcyclic G).path_unique _ _
  have hsupp := congrArg (fun r : T.Path B₁ B₂ => r.val.support) hpq
  simpa [p, q, B₁, B₂, U, W] using hsupp

end IsAcyclicMain

end SimpleGraph
