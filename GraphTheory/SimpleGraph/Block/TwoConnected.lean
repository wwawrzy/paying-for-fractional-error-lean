/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic
import GraphTheory.SimpleGraph.Block.Defs
import GraphTheory.SimpleGraph.Connectivity.Whitney
import GraphTheory.SimpleGraph.Block.EarDecomposition

/-! # The induced graph of a nontrivial block is 2-connected

For a block `b` with at least three vertices, the induced graph on
`blockVertices b` satisfies `IsKConnected 2`.

Incident edges at two vertices of the block are equal or lie on a common
cycle, by the imported `SameBlock_iff_SameBlockStep`. Every edge and vertex
of that cycle remains in the block. Splitting the cycle gives a walk between
the two vertices avoiding any specified third vertex. Thus the induced
block graph is connected and stays connected after one vertex is deleted.

The main result is `induce_blockVertices_isKConnected_two`. Its proof uses
the imported block, Whitney-connectivity, and ear-decomposition results;
this file introduces no additional axioms or proof placeholders.

Reference: Whitney's block characterization (1932), and Diestel §3.1. -/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.whitespace false

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]

/-! ## Cycle edges belong to the same block -/

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- If a cycle contains an edge of a block, all its edges belong to that
block. Edges on a common cycle are SameBlock-related, hence have equal blockOf. -/
theorem mem_edgesInBlock_of_mem_cycle_edges
    {b : G.Block} {e : Sym2 V} (he : e ∈ G.edgesInBlock b)
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) (hec : e ∈ c.edges)
    {f : Sym2 V} (hfc : f ∈ c.edges) :
    f ∈ G.edgesInBlock b := by
  classical
  -- The two edges share the cycle, so they are SameBlock-related.
  have hSB : G.SameBlock e f := SameBlock.of_common_cycle G hc hec hfc
  -- Their blockOf values are equal.
  have hblock : G.blockOf e = G.blockOf f := (G.blockOf_eq_iff).mpr hSB
  -- Block-edge membership includes edge membership and blockOf e = b.
  have he_filter := (Finset.mem_filter.mp he : e ∈ G.edgeFinset ∧ G.blockOf e = b)
  -- A cycle edge is an edge of G, hence belongs to edgeFinset.
  have hfG : f ∈ G.edgeFinset := by
    have : f ∈ G.edgeSet := c.edges_subset_edgeSet hfc
    exact mem_edgeFinset.mpr this
  -- blockOf f = b
  have hbf : G.blockOf f = b := hblock ▸ he_filter.2
  -- Thus f belongs to edgesInBlock b.
  unfold edgesInBlock
  exact Finset.mem_filter.mpr ⟨hfG, hbf⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every vertex in the support of a positive-length walk is an endpoint
of one of its edges. Prove this by induction on the walk. -/
theorem Walk.exists_mem_edges_of_mem_support_of_pos_length
    {a b : V} (w : G.Walk a b) (hpos : 1 ≤ w.length) {v : V}
    (hv : v ∈ w.support) :
    ∃ f ∈ w.edges, v ∈ f := by
  induction w with
  | nil =>
      -- A nil walk contradicts the positive-length assumption.
      simp at hpos
  | @cons a' b' c' hadj p ih =>
      -- (cons hadj p).support = a' :: p.support
      -- (cons hadj p).edges = s(a', b') :: p.edges
      rcases List.mem_cons.mp hv with hv_eq | hv_p
      · -- If v is the initial vertex, the first edge contains it.
        subst hv_eq
        refine ⟨s(v, b'), ?_, ?_⟩
        · simp [Walk.edges_cons]
        · exact Sym2.mem_mk_left _ _
      · -- v ∈ p.support
        by_cases hplen : 1 ≤ p.length
        · -- For a positive-length tail, apply induction.
          obtain ⟨f, hfp, hvf⟩ := ih hplen hv_p
          refine ⟨f, ?_, hvf⟩
          simp [Walk.edges_cons, hfp]
        · -- A zero-length tail is nil, so its two endpoints coincide.
          push_neg at hplen
          have hplen0 : p.length = 0 := by omega
          -- Zero length makes the tail support a singleton.
          have hsupp_eq : p.support = [b'] := by
            have := Walk.length_support p
            -- length_support : p.support.length = p.length + 1
            rw [hplen0] at this
            -- p.support has length 1
            -- Its first vertex is b', the starting endpoint of the tail.
            -- p.support.head ne_nil = b'.
            have hhead := Walk.head_support p
            -- A nonempty list of length one is the singleton containing its head.
            rcases hp_supp : p.support with _ | ⟨x, xs⟩
            · simp [hp_supp] at this
            · -- support = x :: xs, length = 1 + xs.length = 1 → xs = []
              simp [hp_supp] at this hhead
              subst hhead
              cases xs with
              | nil => rfl
              | cons _ _ => simp [List.length] at this
          rw [hsupp_eq] at hv_p
          rcases List.mem_singleton.mp hv_p with hv_eq
          subst hv_eq
          -- The first edge also contains the tail's starting vertex b'.
          refine ⟨s(a', v), ?_, ?_⟩
          · simp [Walk.edges_cons]
          · exact Sym2.mem_mk_right _ _

open Classical in
/-- If a cycle contains an edge of a block, every support vertex belongs
to that block's vertex set. Each vertex is incident with a cycle edge,
and all cycle edges belong to the same block. -/
theorem mem_blockVertices_of_mem_cycle_support
    {b : G.Block} {e : Sym2 V} (he : e ∈ G.edgesInBlock b)
    {u : V} {c : G.Walk u u} (hc : c.IsCycle) (hec : e ∈ c.edges)
    {v : V} (hv : v ∈ c.support) :
    v ∈ G.blockVertices b := by
  classical
  -- Choose a cycle edge incident with the given support vertex.
  -- A cycle has length at least three, hence positive length.
  have hclen : 1 ≤ c.length := by
    have h3 : 3 ≤ c.length := hc.three_le_length
    omega
  obtain ⟨f, hfc, hvf⟩ :=
    Walk.exists_mem_edges_of_mem_support_of_pos_length G c hclen hv
  -- f ∈ c.edges → f ∈ edgesInBlock b
  have hf_block : f ∈ G.edgesInBlock b :=
    G.mem_edgesInBlock_of_mem_cycle_edges he hc hec hfc
  -- v ∈ blockVertices b
  rw [G.mem_blockVertices_iff]
  exact ⟨f, hf_block, hvf⟩

/-! ## Connectedness of the induced block graph

Any two vertices of an edge-containing block are reachable inside its
vertex set. Incident edges are equal or lie on a common cycle by the imported
block characterization. The cycle case supplies a walk entirely within
the block. This first proves connectedness; the vertex-deletion argument
below strengthens the result to 2-connectivity. -/

open Classical in
/-- Two edges of the same block are equal or lie on a common cycle.
Their blockOf values agree, and `SameBlock_iff_SameBlockStep` supplies the
common-cycle characterization. -/
theorem sameBlockStep_of_mem_edgesInBlock
    {b : G.Block} {e₁ e₂ : Sym2 V}
    (h₁ : e₁ ∈ G.edgesInBlock b) (h₂ : e₂ ∈ G.edgesInBlock b) :
    G.SameBlockStep e₁ e₂ := by
  classical
  -- Both edges have blockOf equal to b.
  have hb₁ : G.blockOf e₁ = b := (Finset.mem_filter.mp h₁).2
  have hb₂ : G.blockOf e₂ = b := (Finset.mem_filter.mp h₂).2
  have heq : G.blockOf e₁ = G.blockOf e₂ := hb₁.trans hb₂.symm
  have hSB : G.SameBlock e₁ e₂ := (G.blockOf_eq_iff).mp heq
  exact (G.SameBlock_iff_SameBlockStep).mp hSB

open Classical in
/-- Any two vertices of a block are joined by a walk within its vertex
set. Choose an incident block edge at each vertex. Equal edges give a direct
edge or reflexivity; a common cycle gives a walk whose entire support lies
in blockVertices b. -/
theorem reachable_in_induce_blockVertices
    {b : G.Block} {u v : V}
    (hu : u ∈ G.blockVertices b) (hv : v ∈ G.blockVertices b) :
    ∃ (hu' : u ∈ (↑(G.blockVertices b) : Set V))
      (hv' : v ∈ (↑(G.blockVertices b) : Set V)),
      (G.induce (↑(G.blockVertices b) : Set V)).Reachable ⟨u, hu'⟩ ⟨v, hv'⟩ := by
  classical
  -- Convert between finset membership and its coerced set.
  have hu' : u ∈ (↑(G.blockVertices b) : Set V) := hu
  have hv' : v ∈ (↑(G.blockVertices b) : Set V) := hv
  refine ⟨hu', hv', ?_⟩
  -- Choose incident edges.
  rw [G.mem_blockVertices_iff] at hu hv
  obtain ⟨e_u, he_u, hu_in_eu⟩ := hu
  obtain ⟨e_v, he_v, hv_in_ev⟩ := hv
  -- SameBlockStep e_u e_v
  have hSBS : G.SameBlockStep e_u e_v :=
    G.sameBlockStep_of_mem_edgesInBlock he_u he_v
  rcases hSBS with heq | ⟨x, c, hc, hec_u, hec_v⟩
  · -- If the incident edges agree, both vertices lie on the same edge of G.
    -- For distinct endpoints, that edge gives a walk of length one.
    -- For equal endpoints, use a nil walk.
    by_cases huv : u = v
    · subst huv
      exact Reachable.refl _
    · -- Two distinct endpoints determine the unordered edge s(u,v).
      subst heq  -- e_v = e_u
      -- Identify the shared edge as s(u,v).
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
      -- This unordered pair is an edge of G.
      have he_uv_G : s(u, v) ∈ G.edgeSet := by
        have he_uv_finset : e_u ∈ G.edgeFinset := (Finset.mem_filter.mp he_u).1
        have : e_u ∈ G.edgeSet := mem_edgeFinset.mp he_uv_finset
        rw [← he_uv]; exact this
      have hadj : G.Adj u v := he_uv_G
      -- Construct the one-edge walk in the induced block graph.
      have hadj_ind : (G.induce (↑(G.blockVertices b) : Set V)).Adj
          ⟨u, hu'⟩ ⟨v, hv'⟩ := by
        rw [induce_adj]; exact hadj
      exact ⟨Walk.cons hadj_ind Walk.nil⟩
  · -- The common cycle contains both chosen incident edges and their endpoints.
    -- Construct a walk between the vertices within the cycle.
    -- The entire cycle lies in blockVertices b.
    -- u ∈ e_u i e_u ∈ c.edges → u ∈ c.support
    have hu_supp : u ∈ c.support := by
      -- Membership in the unordered edge identifies one of its two endpoints.
      -- Both endpoints of a cycle edge belong to the cycle support.
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
    -- Every cycle support vertex lies in the block.
    have hsupp_subset : ∀ z ∈ c.support, z ∈ (↑(G.blockVertices b) : Set V) :=
      fun z hz => G.mem_blockVertices_of_mem_cycle_support he_u hc hec_u hz
    -- Construct a walk from u to v by traversing the cycle from u.
    -- Use the cycle split at u to choose the starting point.
    -- The prefix ending at v starts at the original cycle base.
    -- The suffix starting at u ends at the original cycle base.
    -- Concatenate the suffix and prefix at u to obtain a closed walk based at u.
    -- The construction must account for the return to the original cycle base.
    --
    -- Use the suffix starting at u as the first part.
    -- A vertex in that suffix already occurs after u.
    -- A vertex absent from the suffix must occur in the prefix ending at u,
    -- since the two supports cover the original cycle support.
    -- Preserve the required endpoint types when joining the pieces.
    -- The concatenation of suffix and prefix is a closed walk based at u.
    -- Its support contains every original cycle vertex, so a prefix
    -- ending at v gives the desired walk from u to v.
    -- The joined walk has both endpoints u.
    -- Construct the joined walk explicitly.
    let cu : G.Walk u u := (c.dropUntil u hu_supp).append (c.takeUntil u hu_supp)
    -- Show that v belongs to the joined support.
    have hv_cu : v ∈ cu.support := by
      -- support(append) = support1 ++ support2.tail
      -- The take/drop decomposition reconstructs the original support.
      have hv_split : v ∈ (c.takeUntil u hu_supp).support ∨
          v ∈ (c.dropUntil u hu_supp).support := by
        have hsupp_eq : c.support =
            (c.takeUntil u hu_supp).support ++ (c.dropUntil u hu_supp).support.tail := by
          conv_lhs => rw [← c.take_spec hu_supp]
          rw [Walk.support_append]
        rw [hsupp_eq] at hv_supp
        rcases List.mem_append.mp hv_supp with h | h
        · exact Or.inl h
        · right; exact List.mem_of_mem_tail h
      -- The joined support is the suffix support followed by the prefix tail.
      show v ∈ ((c.dropUntil u hu_supp).append (c.takeUntil u hu_supp)).support
      rw [Walk.support_append, List.mem_append]
      rcases hv_split with hvT | hvD
      · -- For a vertex in the prefix, split on whether it is the first vertex x.
        by_cases hv_x : v = x
        · -- The suffix ends at x, so x belongs to its support.
          left
          rw [hv_x]
          -- Use endpoint membership of the suffix to include x.
          exact (c.dropUntil u hu_supp).end_mem_support
        · -- Any other prefix vertex belongs to the prefix support tail.
          right
          have hhead := (c.takeUntil u hu_supp).head_support
          have hsupp_cons : (c.takeUntil u hu_supp).support =
              x :: (c.takeUntil u hu_supp).support.tail := by
            conv_lhs => rw [← List.cons_head_tail (c.takeUntil u hu_supp).support_ne_nil]
            rw [hhead]
          rw [hsupp_cons] at hvT
          rcases List.mem_cons.mp hvT with h_eq | h_t
          · exact absurd h_eq hv_x
          · exact h_t
      · -- v ∈ dropUntil.support
        left; exact hvD
    -- Take the prefix of the joined closed walk ending at v.
    let wuv : G.Walk u v := cu.takeUntil v hv_cu
    -- Every support vertex of the resulting walk belongs to the cycle, hence the block.
    have hwuv_supp : ∀ z ∈ wuv.support, z ∈ (↑(G.blockVertices b) : Set V) := by
      intro z hz
      have hz_cu : z ∈ cu.support := cu.support_takeUntil_subset hv_cu hz
      -- The joined support is contained in the original cycle support.
      have hz_c : z ∈ c.support := by
        simp [cu, Walk.support_append] at hz_cu
        rcases hz_cu with h | h
        · -- z ∈ dropUntil.support → z ∈ c.support
          exact c.support_dropUntil_subset hu_supp h
        · -- z ∈ takeUntil.support.tail → z ∈ takeUntil.support → z ∈ c.support
          have : z ∈ (c.takeUntil u hu_supp).support := List.mem_of_mem_tail h
          exact c.support_takeUntil_subset hu_supp this
      exact hsupp_subset z hz_c
    -- Restrict the constructed walk to the induced block graph.
    let w_induced :
        (G.induce (↑(G.blockVertices b) : Set V)).Walk
          ⟨u, hu'⟩ ⟨v, hv'⟩ :=
      Walk.induce (↑(G.blockVertices b) : Set V) wuv hwuv_supp
    exact ⟨w_induced⟩

/-! ## Connectedness and nonemptiness of a block -/

open Classical in
/-- If the block vertex set is nonempty, its induced graph is connected.
Pairwise reachability comes from `reachable_in_induce_blockVertices`, and
the given vertex witnesses nonemptiness. -/
theorem induce_blockVertices_connected
    {b : G.Block} (hne : (G.blockVertices b).Nonempty) :
    (G.induce (↑(G.blockVertices b) : Set V)).Connected := by
  classical
  rw [connected_iff]
  refine ⟨?_, ?_⟩
  · -- Any two induced vertices are reachable.
    intro ⟨u, hu_set⟩ ⟨v, hv_set⟩
    -- Recover finset membership from membership in the coerced vertex set.
    have hu : u ∈ G.blockVertices b := hu_set
    have hv : v ∈ G.blockVertices b := hv_set
    obtain ⟨hu', hv', hreach⟩ := G.reachable_in_induce_blockVertices hu hv
    -- The two membership proofs differ only by their presentation.
    convert hreach using 0
  · -- Use a vertex from the nonempty block vertex set.
    obtain ⟨w, hw⟩ := hne
    exact ⟨⟨w, hw⟩⟩

/-! ## From connectedness to 2-connectivity

The remaining lemmas split a cycle into internally disjoint paths and use
one path to avoid a specified third vertex. This gives reachability after
any single vertex of a nontrivial block is deleted. The final theorem
`induce_blockVertices_isKConnected_two` packages connectedness and these
one-vertex deletion results as `IsKConnected 2`. -/

/-! ## Splitting a cycle into internally disjoint paths

For a cycle based at u and another vertex v on it, takeUntil v and
dropUntil v meet only at u and v. A third common support vertex would occur
twice in the cycle support tail, contradicting its nodup property. -/
private lemma takeUntil_dropUntil_support_disjoint
    {u v : V} (cu : G.Walk u u) (hcu : cu.IsCycle)
    (hv : v ∈ cu.support) (hvu : v ≠ u)
    {a : V}
    (haT : a ∈ (cu.takeUntil v hv).support)
    (haD : a ∈ (cu.dropUntil v hv).support) :
    a = u ∨ a = v := by
  classical
  -- Assume the common vertex differs from u and v and derive a contradiction.
  by_contra hne
  push_neg at hne
  obtain ⟨hau, hav⟩ := hne
  -- Use the take/drop decomposition of the cycle support.
  have hsupp_eq : cu.support =
      (cu.takeUntil v hv).support ++ (cu.dropUntil v hv).support.tail := by
    conv_lhs => rw [← cu.take_spec hv]
    rw [Walk.support_append]
  -- The prefix starts at u.
  have htake_head : (cu.takeUntil v hv).support.head?
      = some u := by
    have : (cu.takeUntil v hv).support = u :: (cu.takeUntil v hv).support.tail := by
      conv_lhs => rw [← List.cons_head_tail (cu.takeUntil v hv).support_ne_nil]
      congr 1
      exact (cu.takeUntil v hv).head_support
    rw [this]
    rfl
  -- The suffix starts at v.
  have hdrop_head : (cu.dropUntil v hv).support = v :: (cu.dropUntil v hv).support.tail := by
    conv_lhs => rw [← List.cons_head_tail (cu.dropUntil v hv).support_ne_nil]
    congr 1
    exact (cu.dropUntil v hv).head_support
  -- A prefix vertex different from u belongs to the prefix tail.
  have ha_takeT : a ∈ (cu.takeUntil v hv).support.tail := by
    have hsupp_cons : (cu.takeUntil v hv).support
        = u :: (cu.takeUntil v hv).support.tail := by
      conv_lhs => rw [← List.cons_head_tail (cu.takeUntil v hv).support_ne_nil]
      congr 1
      exact (cu.takeUntil v hv).head_support
    rw [hsupp_cons] at haT
    rcases List.mem_cons.mp haT with heq | hin
    · exact absurd heq hau
    · exact hin
  -- A suffix vertex different from v belongs to the suffix tail.
  have ha_dropT : a ∈ (cu.dropUntil v hv).support.tail := by
    rw [hdrop_head] at haD
    rcases List.mem_cons.mp haD with heq | hin
    · exact absurd heq hav
    · exact hin
  -- The cycle support tail is the concatenation of those two tails.
  have htail_eq : cu.support.tail =
      (cu.takeUntil v hv).support.tail ++ (cu.dropUntil v hv).support.tail := by
    have hsupp_cons : (cu.takeUntil v hv).support
        = u :: (cu.takeUntil v hv).support.tail := by
      conv_lhs => rw [← List.cons_head_tail (cu.takeUntil v hv).support_ne_nil]
      congr 1
      exact (cu.takeUntil v hv).head_support
    -- cu.support = (u :: takeT.tail) ++ dropT.tail = u :: (takeT.tail ++ dropT.tail)
    -- → cu.support.tail = takeT.tail ++ dropT.tail
    rw [hsupp_eq, hsupp_cons]
    simp [List.cons_append]
  -- The cycle support tail has no repeated vertices.
  have hnodup : cu.support.tail.Nodup := hcu.support_nodup
  rw [htail_eq] at hnodup
  -- A common element of both tails contradicts nodup of their concatenation.
  rw [List.nodup_append] at hnodup
  obtain ⟨_, _, hdis⟩ := hnodup
  exact hdis a ha_takeT a ha_dropT rfl

/-! ## A walk between cycle vertices avoiding a third vertex

For distinct cycle vertices u,v and a third vertex a, at least one of the
two cycle pieces avoids a. The prefix or the reversed suffix therefore
supplies a walk from u to v avoiding a. -/
private theorem cycle_walk_avoid_third
    {u v a : V} (cu : G.Walk u u) (hcu : cu.IsCycle)
    (hv : v ∈ cu.support) (hvu : v ≠ u)
    (hau : a ≠ u) (hav : a ≠ v) :
    ∃ (w : G.Walk u v), a ∉ w.support ∧
      (∀ z ∈ w.support, z ∈ cu.support) := by
  classical
  -- Split on whether a belongs to the prefix support.
  by_cases haT : a ∈ (cu.takeUntil v hv).support
  · -- If a lies in the prefix, internal disjointness excludes it from the suffix.
    have haD : a ∉ (cu.dropUntil v hv).support := by
      intro hD
      rcases takeUntil_dropUntil_support_disjoint G cu hcu hv hvu haT hD with heq | heq
      · exact hau heq
      · exact hav heq
    -- Use the reversed suffix as a walk from u to v.
    refine ⟨(cu.dropUntil v hv).reverse, ?_, ?_⟩
    · -- Reversal preserves exclusion of a from the support.
      rw [Walk.support_reverse]
      simpa using haD
    · -- support ⊆ cu.support
      intro z hz
      rw [Walk.support_reverse] at hz
      have hz' : z ∈ (cu.dropUntil v hv).support := by simpa using hz
      exact cu.support_dropUntil_subset hv hz'
  · -- Otherwise the prefix itself avoids a.
    refine ⟨cu.takeUntil v hv, haT, ?_⟩
    intro z hz
    exact cu.support_takeUntil_subset hv hz

/-! ## Reachability in a block avoiding one vertex

For distinct block vertices u,v and a third vertex a, choose incident block
edges at u,v. If the edges coincide, the one-edge walk avoids a. Otherwise
use their common cycle, rotate it to u, and choose a cycle walk to v avoiding
a. The entire support stays inside the block. -/
private theorem walk_in_block_avoid_third
    {b : G.Block} {u v a : V}
    (hu : u ∈ G.blockVertices b) (hv : v ∈ G.blockVertices b)
    (huv : u ≠ v) (hau : a ≠ u) (hav : a ≠ v) :
    ∃ (w : G.Walk u v),
      a ∉ w.support ∧
      (∀ z ∈ w.support, z ∈ G.blockVertices b) := by
  classical
  -- Choose incident block edges.
  rw [G.mem_blockVertices_iff] at hu hv
  obtain ⟨e_u, he_u, hu_in_eu⟩ := hu
  obtain ⟨e_v, he_v, hv_in_ev⟩ := hv
  -- SameBlockStep
  have hSBS : G.SameBlockStep e_u e_v :=
    G.sameBlockStep_of_mem_edgesInBlock he_u he_v
  rcases hSBS with heq | ⟨x, c, hc, hec_u, hec_v⟩
  · -- Equal incident edges give a walk of length one.
    subst heq
    -- The distinct endpoints identify the shared unordered edge.
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
    -- Use the edge u–v as the walk.
    refine ⟨Walk.cons hadj Walk.nil, ?_, ?_⟩
    · -- Its support is [u,v], which excludes a.
      intro hin
      simp [Walk.support_cons, Walk.support_nil] at hin
      rcases hin with h | h
      · exact hau h
      · exact hav h
    · -- Both endpoints belong to the block vertex set.
      intro z hz
      simp [Walk.support_cons, Walk.support_nil] at hz
      rcases hz with hzu | hzv
      · subst hzu
        rw [G.mem_blockVertices_iff]; exact ⟨e_u, he_u, hu_in_eu⟩
      · subst hzv
        rw [G.mem_blockVertices_iff]; exact ⟨e_u, he_u, hv_in_ev⟩
  · -- For a common cycle, rotate to u and use cycle_walk_avoid_third.
    -- u ∈ c.support
    have hu_supp : u ∈ c.support := by
      induction e_u with
      | h a₀ b₀ =>
        rcases Sym2.mem_iff.mp hu_in_eu with hua | hub
        · subst hua; exact c.fst_mem_support_of_mem_edges hec_u
        · subst hub; exact c.snd_mem_support_of_mem_edges hec_u
    -- Rotate the cycle to start at u.
    let cu := c.rotate u hu_supp
    have hcu : cu.IsCycle := hc.rotate hu_supp
    -- v ∈ c.support
    have hv_supp : v ∈ c.support := by
      induction e_v with
      | h a₀ b₀ =>
        rcases Sym2.mem_iff.mp hv_in_ev with hva | hvb
        · subst hva; exact c.fst_mem_support_of_mem_edges hec_v
        · subst hvb; exact c.snd_mem_support_of_mem_edges hec_v
    -- Rotation preserves membership of v in the cycle support.
    have hv_cu : v ∈ cu.support := (Walk.mem_support_rotate_iff c u hu_supp).mpr hv_supp
    -- v ≠ u
    have hvu : v ≠ u := huv.symm
    -- Construct the walk from u to v avoiding a inside the rotated support.
    obtain ⟨w, ha_notin, hsupp_cu⟩ := cycle_walk_avoid_third G cu hcu hv_cu hvu hau hav
    -- Rotation preserves the support set, which is contained in the block.
    refine ⟨w, ha_notin, ?_⟩
    intro z hz
    have hz_cu : z ∈ cu.support := hsupp_cu z hz
    have hz_c : z ∈ c.support := (Walk.mem_support_rotate_iff c u hu_supp).mp hz_cu
    -- Every original cycle vertex belongs to blockVertices b.
    exact G.mem_blockVertices_of_mem_cycle_support he_u hc hec_u hz_c

/-! ## Connectedness after deleting one block vertex

The induced graph on a nontrivial block remains connected after deleting
one vertex. Use `walk_in_block_avoid_third` and restrict the resulting walks
to the appropriate induced vertex types. -/
private theorem induce_blockVertices_remove_one_connected
    {b : G.Block} (hntriv : 3 ≤ (G.blockVertices b).card)
    (a : (↑(G.blockVertices b) : Set V)) :
    ((G.induce (↑(G.blockVertices b) : Set V)).induce
      ((Finset.univ \ {a} : Finset _) : Set _)).Connected := by
  classical
  set H := G.induce (↑(G.blockVertices b) : Set V) with hH
  set S : Set ↑(G.blockVertices b) :=
    ((Finset.univ \ {a} : Finset ↑(G.blockVertices b)) : Set ↑(G.blockVertices b))
  set K := H.induce S with hK
  -- At least three block vertices leave at least two after deletion.
  rw [connected_iff]
  refine ⟨?_, ?_⟩
  · -- Prove pairwise reachability in the remaining induced graph.
    intro ⟨⟨u, hu_block⟩, hu_S⟩ ⟨⟨v, hv_block⟩, hv_S⟩
    -- Membership in S means that the block vertex differs from a.
    have hu_ne_a : (⟨u, hu_block⟩ : ↑(G.blockVertices b)) ≠ a := by
      intro hua
      have : (⟨u, hu_block⟩ : ↑(G.blockVertices b)) ∈ ({a} : Finset _) := by
        rw [Finset.mem_singleton]; exact hua
      have hu_S' : (⟨u, hu_block⟩ : ↑(G.blockVertices b)) ∈ (Finset.univ \ {a} : Finset _) := hu_S
      simp at hu_S'
      exact hu_S' hua
    have hv_ne_a : (⟨v, hv_block⟩ : ↑(G.blockVertices b)) ≠ a := by
      intro hva
      have hv_S' : (⟨v, hv_block⟩ : ↑(G.blockVertices b)) ∈ (Finset.univ \ {a} : Finset _) := hv_S
      simp at hv_S'
      exact hv_S' hva
    -- The deleted subtype vertex has its value in the block.
    have ha_block : (a : V) ∈ G.blockVertices b := a.property
    -- Subtype.ext transfers inequality of subtype vertices to their underlying values.
    have hau_val : (a : V) ≠ u := by
      intro hua
      apply hu_ne_a
      exact Subtype.ext hua.symm
    have hav_val : (a : V) ≠ v := by
      intro hva
      apply hv_ne_a
      exact Subtype.ext hva.symm
    -- For equal underlying endpoints, use reflexivity.
    by_cases huv_eq : u = v
    · subst huv_eq
      -- Subtype.ext identifies the corresponding induced vertices.
      exact Reachable.refl _
    · -- For distinct endpoints, construct a walk avoiding a.
      obtain ⟨w, ha_not_in_w, hw_supp⟩ :=
        G.walk_in_block_avoid_third hu_block hv_block huv_eq hau_val hav_val
      -- Restrict the original-graph walk to the remaining induced graph.
      -- First use block membership of its support to obtain a walk in H.
      -- Then use exclusion of a to obtain a walk in K.
      -- Construct the induced walk in two stages.
      have hw_supp_S : ∀ z ∈ w.support, z ∈ ((↑(G.blockVertices b) : Set V)) := hw_supp
      -- First obtain the walk in H.
      let wH : H.Walk ⟨u, hu_block⟩ ⟨v, hv_block⟩ :=
        Walk.induce (↑(G.blockVertices b) : Set V) w hw_supp_S
      -- support wH = w.support.attachWith
      have hsupp_wH :
          ∀ z ∈ wH.support, (z : V) ∈ ((↑(G.blockVertices b) : Set V)) := by
        intro z hz
        exact z.property
      -- Every support vertex of the induced walk differs from a.
      have hsupp_wH_avoid_a :
          ∀ z ∈ wH.support, z ∈ S := by
        intro z hz
        -- Induced support membership gives original support membership.
        -- The original support avoids a.val.
        have hz_val : (z : V) ∈ w.support := by
          have hsupp_wH_eq : wH.support
              = w.support.attachWith (Membership.mem ↑(G.blockVertices b)) hw_supp_S :=
            Walk.support_induce w hw_supp_S
          rw [hsupp_wH_eq] at hz
          -- Use the membership characterization for attachWith.
          exact (List.mem_attachWith hw_supp_S z).mp hz
        have hz_ne_a : z ≠ a := by
          intro hza
          apply ha_not_in_w
          have : (a : V) = (z : V) := congrArg Subtype.val hza.symm
          rw [this]
          exact hz_val
        -- z ∈ S = univ \ {a}
        show z ∈ S
        simp [S, hz_ne_a]
      -- Restrict the H-walk further to K = H.induce S.
      let wK : K.Walk ⟨⟨u, hu_block⟩, hu_S⟩ ⟨⟨v, hv_block⟩, hv_S⟩ :=
        Walk.induce S wH hsupp_wH_avoid_a
      exact ⟨wK⟩
  · -- The remaining graph is nonempty because at least three block vertices existed.
    -- Choose any vertex of the nonempty remaining finset S.
    -- Deleting one vertex leaves cardinality at least two.
    have hS_ne : Finset.Nonempty (Finset.univ \ {a} : Finset ↑(G.blockVertices b)) := by
      have hcard : (Finset.univ \ {a} : Finset ↑(G.blockVertices b)).card =
          Fintype.card ↑(G.blockVertices b) - 1 := by
        rw [Finset.card_sdiff]
        simp [Finset.card_univ, Finset.card_singleton]
      have hcard_block : Fintype.card ↑(G.blockVertices b) =
          (G.blockVertices b).card := Fintype.card_coe _
      have h_card_ge : 2 ≤ (Finset.univ \ {a} : Finset ↑(G.blockVertices b)).card := by
        rw [hcard, hcard_block]; omega
      exact Finset.card_pos.mp (by omega)
    obtain ⟨z, hz⟩ := hS_ne
    refine ⟨⟨z, ?_⟩⟩
    show z ∈ S
    simpa [S] using hz

/-! ## 2-connectivity of the induced nontrivial block

For a block with at least three vertices, prove `IsVertexConnected 2`.
The cardinality requirement is immediate. A deleted finset of size less than
two is either empty, handled by block connectedness, or a singleton, handled
by `induce_blockVertices_remove_one_connected`. The vertex-connectivity
comparison then gives `IsKConnected 2`. -/
theorem induce_blockVertices_isKConnected_two
    (b : G.Block) (hntriv : 3 ≤ (G.blockVertices b).card) :
    (G.induce (↑(G.blockVertices b) : Set V)).IsKConnected 2 := by
  classical
  set H := G.induce (↑(G.blockVertices b) : Set V) with hH
  -- |↑blockVertices b| ≥ 3
  have hcard : 3 ≤ Fintype.card ↑(G.blockVertices b) := by
    rw [Fintype.card_coe]; exact hntriv
  -- Obtain Nontrivial for the vertex-connectivity comparison.
  have hntr : Nontrivial ↑(G.blockVertices b) := by
    rw [← Fintype.one_lt_card_iff_nontrivial]
    omega
  -- Establish IsVertexConnected H 2.
  have hVC : H.IsVertexConnected 2 := by
    refine ⟨?_, ?_⟩
    · -- The induced vertex type has cardinality greater than two.
      show 2 < Fintype.card ↑(G.blockVertices b)
      omega
    · -- ∀ S, |S| < 2 → (H.induce (univ \ S)).Connected
      intro S hS
      -- |S| ∈ {0, 1}
      interval_cases hS_card : S.card
      · -- |S| = 0 → S = ∅
        have hS_empty : S = ∅ := Finset.card_eq_zero.mp hS_card
        subst hS_empty
        -- With an empty deletion, connectedness is that of H.
        -- Prove this directly through induced walks.
        set Sempty : Set ↑(G.blockVertices b) :=
          ((Finset.univ \ ∅ : Finset ↑(G.blockVertices b)) :
            Set ↑(G.blockVertices b)) with hSempty
        rw [connected_iff]
        refine ⟨?_, ?_⟩
        · intro ⟨⟨u, hu_block⟩, hu_univ⟩ ⟨⟨v, hv_block⟩, hv_univ⟩
          -- Both underlying endpoints belong to the block.
          have hreach_H : H.Reachable ⟨u, hu_block⟩ ⟨v, hv_block⟩ := by
            obtain ⟨_, _, hr⟩ := G.reachable_in_induce_blockVertices hu_block hv_block
            exact hr
          -- Restrict the H-walk to the full remaining induced vertex set.
          obtain ⟨w⟩ := hreach_H
          have hw_supp_univ : ∀ z ∈ w.support, z ∈ Sempty := by
            intro z _
            show z ∈ Sempty
            simp [Sempty]
          let wK := Walk.induce Sempty w hw_supp_univ
          exact ⟨wK⟩
        · -- Nonempty
          have : Nonempty ↑(G.blockVertices b) := hntr.to_nonempty
          obtain ⟨z⟩ := this
          refine ⟨⟨z, ?_⟩⟩
          show z ∈ Sempty
          simp [Sempty]
      · -- |S| = 1 → S = {a}
        rw [Finset.card_eq_one] at hS_card
        obtain ⟨a, ha⟩ := hS_card
        subst ha
        exact G.induce_blockVertices_remove_one_connected hntriv a
  -- Apply le_vertexConnectivity_of_isVertexConnected.
  exact le_vertexConnectivity_of_isVertexConnected H hVC

end SimpleGraph
