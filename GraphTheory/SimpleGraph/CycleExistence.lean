/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic
import GraphTheory.SimpleGraph.LongestPath

/-!
# Cycle Existence in Simple Graphs (Diestel Prop 1.3.1)

Two forms of **Diestel, Proposition 1.3.1** ("Every graph `G` contains a path of
length `δ(G)` and a cycle of length at least `δ(G) + 1`, provided `δ(G) ≥ 2`").

* Qualitative form: a finite graph with minimum degree `≥ 2` contains a cycle
  (`not_isAcyclic_of_two_le_minDegree`), proved via the **forest edge bound**
  (an acyclic graph on `n ≥ 1` vertices has fewer than `n` edges).

* Quantitative form (the actual statement of Prop 1.3.1), proved via the
  **longest-path argument** (`exists_maximal_isPath`, from `LongestPath.lean`):
  - `exists_path_length_ge_minDegree` : there is a path of length `≥ δ(G)`;
  - `exists_cycle_length_gt_minDegree` : if `δ(G) ≥ 2` there is a cycle of
    length `≥ δ(G) + 1`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

open Classical in
/-- Edges partition across connected components. -/
lemma sum_edgeFinset_components_eq :
    ∑ C : G.ConnectedComponent, C.toSimpleGraph.edgeFinset.card =
    G.edgeFinset.card := by
  -- Image of component edges in G
  let f : G.ConnectedComponent → Finset (Sym2 V) :=
    fun C => C.toSimpleGraph.edgeFinset.image (Sym2.map Subtype.val)
  -- G.edgeFinset = biUnion of component images
  have hCover : G.edgeFinset = Finset.univ.biUnion f := by
    ext e
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | hf u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        rw [Finset.mem_biUnion]
        refine ⟨G.connectedComponentMk u, Finset.mem_univ _, ?_⟩
        simp only [f, Finset.mem_image]
        exact ⟨s(⟨u, (ConnectedComponent.mem_supp_iff _ u).mpr rfl⟩,
                  ⟨v, (ConnectedComponent.mem_supp_iff _ v).mpr
                    (ConnectedComponent.sound he.reachable).symm⟩),
               by rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet], rfl⟩
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨C, _, he'⟩ := he
      simp only [f, Finset.mem_image] at he'
      obtain ⟨e', he'_mem, rfl⟩ := he'
      rw [SimpleGraph.mem_edgeFinset] at he'_mem
      rw [SimpleGraph.mem_edgeFinset]
      induction e' using Sym2.inductionOn with
      | hf u v =>
        rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
        rw [SimpleGraph.mem_edgeSet] at he'_mem
        exact he'_mem
  -- Component images are pairwise disjoint
  have hDisj : (↑(Finset.univ : Finset G.ConnectedComponent) :
      Set G.ConnectedComponent).PairwiseDisjoint f := by
    intro C _ C' _ hne
    show Disjoint (f C) (f C')
    rw [Finset.disjoint_left]
    intro e heC heC'
    apply hne
    simp only [f, Finset.mem_image] at heC heC'
    obtain ⟨eC, heC_mem, rfl⟩ := heC
    obtain ⟨eC', heC'_mem, heq⟩ := heC'
    induction eC using Sym2.inductionOn with
    | hf u v =>
      induction eC' using Sym2.inductionOn with
      | hf u' v' =>
        have heq' : s(u.val, v.val) = s(u'.val, v'.val) := heq.symm
        rw [Sym2.eq_iff] at heq'
        have hCu  := (ConnectedComponent.mem_supp_iff C  u.val).mp u.prop
        have hCu' := (ConnectedComponent.mem_supp_iff C' u'.val).mp u'.prop
        have hCv' := (ConnectedComponent.mem_supp_iff C' v'.val).mp v'.prop
        rcases heq' with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [← hCu, h1, hCu']
        · rw [← hCu, h1, hCv']
  -- Card of each image = card of component edgeFinset (by injectivity)
  have hInj : ∀ C : G.ConnectedComponent,
      (f C).card = C.toSimpleGraph.edgeFinset.card := fun C =>
    Finset.card_image_of_injective _ (Sym2.map.injective Subtype.val_injective)
  -- Conclude by biUnion card formula
  calc ∑ C : G.ConnectedComponent, C.toSimpleGraph.edgeFinset.card
      = ∑ C : G.ConnectedComponent, (f C).card :=
        Finset.sum_congr rfl fun C _ => (hInj C).symm
    _ = (Finset.univ.biUnion f).card := (Finset.card_biUnion hDisj).symm
    _ = G.edgeFinset.card := by rw [← hCover]

open Classical in
omit [DecidableRel G.Adj] in
/-- Vertices partition across connected components. -/
lemma sum_card_components_eq :
    ∑ C : G.ConnectedComponent, Fintype.card ↥C = Fintype.card V := by
  rw [← Fintype.card_sigma]
  apply Fintype.card_congr
  exact ((Equiv.sigmaFiberEquiv G.connectedComponentMk).symm.trans
    (Equiv.sigmaCongrRight fun C =>
      Equiv.subtypeEquivRight fun v => (ConnectedComponent.mem_supp_iff C v).symm)).symm

open Classical in
/-- Every finite graph satisfies `|V| ≤ |E| + c(G)`, where `c(G)` is its
number of connected components.  This is the connected lower edge bound summed
over all components. -/
lemma card_le_edgeFinset_card_add_card_connectedComponent :
    Fintype.card V ≤
      G.edgeFinset.card + Fintype.card G.ConnectedComponent := by
  have hper : ∀ C : G.ConnectedComponent,
      Fintype.card ↥C ≤ C.toSimpleGraph.edgeFinset.card + 1 := by
    intro C
    have h := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
    rw [show Fintype.card C.toSimpleGraph.edgeSet =
      C.toSimpleGraph.edgeFinset.card from edgeFinset_card.symm] at h
    exact h
  have hsum :
      (∑ C : G.ConnectedComponent, Fintype.card ↥C) ≤
        ∑ C : G.ConnectedComponent,
          (C.toSimpleGraph.edgeFinset.card + 1) :=
    Finset.sum_le_sum fun C _ ↦ hper C
  calc
    Fintype.card V =
        ∑ C : G.ConnectedComponent, Fintype.card ↥C :=
      (sum_card_components_eq (G := G)).symm
    _ ≤ ∑ C : G.ConnectedComponent,
        (C.toSimpleGraph.edgeFinset.card + 1) := hsum
    _ = (∑ C : G.ConnectedComponent,
        C.toSimpleGraph.edgeFinset.card) +
        ∑ _C : G.ConnectedComponent, 1 := Finset.sum_add_distrib
    _ = G.edgeFinset.card + Fintype.card G.ConnectedComponent := by
      rw [sum_edgeFinset_components_eq]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

open Classical in
/-- Exact forest edge formula (Diestel Proposition 1.5.1): an acyclic finite
graph satisfies `|E| + c(G) = |V|`.  Each connected component is a tree and
therefore contributes exactly one fewer edge than vertex. -/
lemma IsAcyclic.edgeFinset_card_add_card_connectedComponent
    (hac : G.IsAcyclic) :
    G.edgeFinset.card + Fintype.card G.ConnectedComponent =
      Fintype.card V := by
  have hEdge : ∀ C : G.ConnectedComponent,
      C.toSimpleGraph.edgeFinset.card + 1 = Fintype.card ↥C :=
    fun C ↦ (hac.isTree_connectedComponent C).card_edgeFinset
  have hsum :
      (∑ C : G.ConnectedComponent,
        (C.toSimpleGraph.edgeFinset.card + 1)) =
      ∑ C : G.ConnectedComponent, Fintype.card ↥C :=
    Finset.sum_congr rfl fun C _ ↦ hEdge C
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at hsum
  calc
    G.edgeFinset.card + Fintype.card G.ConnectedComponent =
        (∑ C : G.ConnectedComponent,
          C.toSimpleGraph.edgeFinset.card) +
          Fintype.card G.ConnectedComponent := by
      rw [sum_edgeFinset_components_eq]
    _ = ∑ C : G.ConnectedComponent, Fintype.card ↥C := hsum
    _ = Fintype.card V := sum_card_components_eq

open Classical in
/-- Exact edge/component characterization of finite forests: a graph is
acyclic if and only if `|E| + c(G) = |V|`.  For the reverse direction, compare
the graph with a spanning forest that has the same reachability relation. -/
theorem isAcyclic_iff_edgeFinset_card_add_card_connectedComponent :
    G.IsAcyclic ↔
      G.edgeFinset.card + Fintype.card G.ConnectedComponent =
        Fintype.card V := by
  constructor
  · exact IsAcyclic.edgeFinset_card_add_card_connectedComponent
  · intro hcard
    obtain ⟨F, hFG, hFac, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
    let componentMap : F.ConnectedComponent → G.ConnectedComponent :=
      ConnectedComponent.map (Hom.ofLE hFG)
    have hMapInjective : Function.Injective componentMap := by
      refine ConnectedComponent.ind₂ ?_
      intro u v huv
      simp only [componentMap, ConnectedComponent.map_mk] at huv ⊢
      apply ConnectedComponent.sound
      rw [hreach]
      exact ConnectedComponent.exact huv
    have hMapSurjective : Function.Surjective componentMap :=
      ConnectedComponent.surjective_map_ofLE hFG
    have hcomponents :
        Fintype.card F.ConnectedComponent =
          Fintype.card G.ConnectedComponent :=
      Fintype.card_congr
        (Equiv.ofBijective componentMap ⟨hMapInjective, hMapSurjective⟩)
    have hFcard := hFac.edgeFinset_card_add_card_connectedComponent
    have hedges : F.edgeFinset.card = G.edgeFinset.card := by omega
    have hEdgeFinset : F.edgeFinset = G.edgeFinset :=
      Finset.eq_of_subset_of_card_le (edgeFinset_mono hFG) hedges.ge
    have hEq : F = G := by
      apply edgeSet_injective
      rw [← coe_edgeFinset, ← coe_edgeFinset, hEdgeFinset]
    rwa [← hEq]

open Classical in
/-- **Forest edge bound**: An acyclic graph on n ≥ 1 vertices has fewer than n edges. -/
lemma IsAcyclic.edgeFinset_card_lt [Nonempty V] (hac : G.IsAcyclic) :
    G.edgeFinset.card < Fintype.card V := by
  have hEq := hac.edgeFinset_card_add_card_connectedComponent
  have hPos : 0 < Fintype.card G.ConnectedComponent :=
    Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  omega

/-- If δ(G) ≥ 2, then |V| ≤ |E|. -/
lemma card_le_edgeFinset_of_two_le_minDegree [Nonempty V]
    (h : 2 ≤ G.minDegree) :
    Fintype.card V ≤ G.edgeFinset.card := by
  have h1 : ∀ v : V, 2 ≤ G.degree v :=
    fun v ↦ le_trans h (G.minDegree_le_degree v)
  have h2 : 2 * Fintype.card V ≤ Finset.univ.sum fun v ↦ G.degree v := by
    have : Finset.univ.sum (fun (_ : V) ↦ 2) ≤ Finset.univ.sum fun v ↦ G.degree v :=
      Finset.sum_le_sum fun v _ ↦ h1 v
    simp [Finset.sum_const, Finset.card_univ] at this
    linarith
  linarith [G.sum_degrees_eq_twice_card_edges]

/-- **Diestel Proposition 1.3.1** (qualitative form): δ(G) ≥ 2 → G contains a cycle. -/
theorem not_isAcyclic_of_two_le_minDegree [Nonempty V]
    (h : 2 ≤ G.minDegree) : ¬ G.IsAcyclic := fun hac =>
  absurd hac.edgeFinset_card_lt (not_lt.mpr (card_le_edgeFinset_of_two_le_minDegree h))

/-!
## Quantitative form via the longest-path argument

The length-maximal-path engine (`exists_maximal_isPath`,
`Adj.mem_support_of_maximal_isPath`, `Walk.length_takeUntil_getVert`,
`Walk.IsPath.eq_singleton_of_mem_edges`) is shared with the Hamilton chapter and
lives in `GraphTheory.SimpleGraph.LongestPath`.
-/

/-- The endpoint of a longest path has all of its neighbours on that path (otherwise
the path could be extended), hence `d(u) ≤ length`. -/
lemma degree_start_le_of_longest
    {u w : V} (p : G.Walk u w) (hp : p.IsPath)
    (hmax : ∀ (a b : V) (q : G.Walk a b), q.IsPath → q.length ≤ p.length) :
    G.degree u ≤ p.length := by
  classical
  have hnb : ∀ x, G.Adj u x → x ∈ p.support :=
    fun x hx => Adj.mem_support_of_maximal_isPath hp hmax hx
  have hsub : G.neighborFinset u ⊆ p.support.toFinset.erase u := by
    intro x hx
    rw [mem_neighborFinset] at hx
    rw [Finset.mem_erase]
    exact ⟨(G.ne_of_adj hx).symm, by rw [List.mem_toFinset]; exact hnb x hx⟩
  have hu : u ∈ p.support.toFinset := by rw [List.mem_toFinset]; exact p.start_mem_support
  have htf : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support]
  calc G.degree u = (G.neighborFinset u).card := (G.card_neighborFinset_eq_degree u).symm
    _ ≤ (p.support.toFinset.erase u).card := Finset.card_le_card hsub
    _ = p.support.toFinset.card - 1 := Finset.card_erase_of_mem hu
    _ = p.length := by omega

/-- **Diestel Proposition 1.3.1** (path part): every finite graph contains a path of
length at least `δ(G)`. -/
theorem exists_path_length_ge_minDegree [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ G.minDegree ≤ p.length := by
  obtain ⟨u, w, p, hp, hmax⟩ := exists_maximal_isPath (G := G)
  exact ⟨u, w, p, hp,
    le_trans (G.minDegree_le_degree u) (degree_start_le_of_longest p hp hmax)⟩

/-- **Diestel Proposition 1.3.1** (cycle part): if `δ(G) ≥ 2` then `G` contains a
cycle of length at least `δ(G) + 1`. Take a longest path `p`; its start `u` has all
`≥ δ` neighbours on `p`, so the neighbour `x` of `u` farthest along `p` sits at index
`m ≥ δ`. Closing the prefix `u … x` with the edge `x u` yields a cycle of length
`m + 1 ≥ δ + 1`. -/
theorem exists_cycle_length_gt_minDegree [Nonempty V]
    (hδ : 2 ≤ G.minDegree) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ G.minDegree + 1 ≤ c.length := by
  classical
  obtain ⟨u, w, p, hp, hmax⟩ := exists_maximal_isPath (G := G)
  have hnb : ∀ x, G.Adj u x → x ∈ p.support :=
    fun x hx => Adj.mem_support_of_maximal_isPath hp hmax hx
  have hdeg_le : G.degree u ≤ p.length := degree_start_le_of_longest p hp hmax
  have hdeg_ge : 2 ≤ G.degree u := le_trans hδ (G.minDegree_le_degree u)
  have hInj : Set.InjOn p.getVert {i | i ≤ p.length} := hp.getVert_injOn
  set I : Finset ℕ :=
    (Finset.range (p.length + 1)).filter (fun i => G.Adj u (p.getVert i)) with hI
  have himg : I.image p.getVert = G.neighborFinset u := by
    ext y
    simp only [Finset.mem_image, mem_neighborFinset, hI, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨_, hadj⟩, rfl⟩; exact hadj
    · intro hy
      obtain ⟨n, hn, hnle⟩ := (Walk.mem_support_iff_exists_getVert).mp (hnb y hy)
      exact ⟨n, ⟨by omega, by rw [hn]; exact hy⟩, hn⟩
  have hcardI : I.card = G.degree u := by
    rw [← G.card_neighborFinset_eq_degree u, ← himg]
    refine (Finset.card_image_of_injOn ?_).symm
    intro a ha b hb hab
    rw [Finset.mem_coe, hI, Finset.mem_filter, Finset.mem_range] at ha hb
    exact hInj (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hab
  have hIne : I.Nonempty := by
    refine ⟨1, ?_⟩
    rw [hI, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have h := p.adj_getVert_succ (i := 0) (by omega)
    rwa [Walk.getVert_zero] at h
  set m := I.max' hIne with hm_def
  have hmI : m ∈ I := I.max'_mem hIne
  rw [hI, Finset.mem_filter, Finset.mem_range] at hmI
  have hm_le : m ≤ p.length := by omega
  have hm_adj : G.Adj u (p.getVert m) := hmI.2
  have hI_sub : I ⊆ Finset.Icc 1 m := by
    intro i hi
    have hi' := hi
    rw [hI, Finset.mem_filter, Finset.mem_range] at hi'
    rw [Finset.mem_Icc]
    refine ⟨?_, I.le_max' i hi⟩
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso; subst h0; rw [Walk.getVert_zero] at hi'; exact (G.ne_of_adj hi'.2) rfl
    · exact hpos
  have hm_ge : G.degree u ≤ m := by
    calc G.degree u = I.card := hcardI.symm
      _ ≤ (Finset.Icc 1 m).card := Finset.card_le_card hI_sub
      _ = m := by rw [Nat.card_Icc]; omega
  -- Close the prefix `u … (getVert m)` with the edge back to `u`.
  have hx_supp : p.getVert m ∈ p.support := p.getVert_mem_support m
  have hq_path : (p.takeUntil (p.getVert m) hx_supp).IsPath := hp.takeUntil hx_supp
  have hq_len : (p.takeUntil (p.getVert m) hx_supp).length = m :=
    Walk.length_takeUntil_getVert hp hm_le
  have hedge : s(u, p.getVert m) ∉ (p.takeUntil (p.getVert m) hx_supp).reverse.edges := by
    rw [Walk.edges_reverse, List.mem_reverse]
    intro hmem
    obtain ⟨_, hq1⟩ := hq_path.eq_singleton_of_mem_edges hmem
    have hm1 : m = 1 := by rw [← hq_len, hq1, Walk.length_cons, Walk.length_nil]
    omega
  have hcyc : (Walk.cons hm_adj (p.takeUntil (p.getVert m) hx_supp).reverse).IsCycle := by
    rw [Walk.cons_isCycle_iff]; exact ⟨hq_path.reverse, hedge⟩
  refine ⟨u, Walk.cons hm_adj (p.takeUntil (p.getVert m) hx_supp).reverse, hcyc, ?_⟩
  rw [Walk.length_cons, Walk.length_reverse, hq_len]
  have : G.minDegree ≤ m := le_trans (G.minDegree_le_degree u) hm_ge
  omega

end SimpleGraph
