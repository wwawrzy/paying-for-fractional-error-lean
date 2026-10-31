/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Preorder.Finite
import GraphTheory.SimpleGraph.Connectivity.Whitney
import GraphTheory.SimpleGraph.Block.EarDecomposition
import GraphTheory.SimpleGraph.Block.CycleHPathConstruction
import GraphTheory.SimpleGraph.Block.CycleHPathTwoConnected
import Mathlib.Tactic

/-! # Diestel Proposition 3.1.2: construction from a cycle

A finite graph is 2-connected exactly when it can be constructed from a
cycle by successively adding H-paths, expressed as
`IsConstructibleFromCycle G ⊤`.

A 2-connected graph contains a cycle. Finiteness of its subgraph lattice
then supplies a maximal constructible subgraph H. If H is not spanning,
2-connectivity supplies an H-path through a complementary component. If H
is spanning but not the whole graph, a missing edge is an H-path. Either
case would strictly extend H, so maximality forces H = ⊤.

The public equivalence is `isKConnected_two_iff_isConstructibleFromCycle_top`.
The witness variant compares `H.spanningCoe = G`, whose graphs have the same
vertex type; `H.coe = G` would not be well typed.

This file introduces no additional axioms or proof placeholders.
Reference: Diestel, Graph Theory, 5th edition, Proposition 3.1.2. -/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}

/-- A 2-connected graph has at least three vertices. Its vertex connectivity
is the supremum of values k requiring k < |V|, so |V| ≤ 2 would contradict
the connectivity lower bound. -/
theorem IsKConnected.two_card_ge_three
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsKConnected 2) :
    3 ≤ Fintype.card V := by
  unfold IsKConnected at h
  unfold vertexConnectivity at h
  -- h : 2 ≤ sSup {k | G.IsVertexConnected k}
  rcases (Set.eq_empty_or_nonempty {k : Nat | G.IsVertexConnected k}) with hempty | hne
  · -- The empty supremum is zero, contradicting connectivity at least two.
    rw [hempty] at h; simp at h
  · -- For a nonempty set, every connectivity value is at most |V| - 1.
    have hsup : sSup {k : Nat | G.IsVertexConnected k} ≤ Fintype.card V - 1 := by
      apply csSup_le hne
      intro b ⟨hb, _⟩
      omega
    omega

/-- A 2-connected graph has a nontrivial vertex type, since it has at least
three vertices. -/
theorem IsKConnected.two_nontrivial
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsKConnected 2) :
    Nontrivial V := by
  rw [← Fintype.one_lt_card_iff_nontrivial]
  have := IsKConnected.two_card_ge_three h
  omega

/-- Derive IsVertexConnected 2 from IsKConnected 2 without a separate
Nontrivial hypothesis. -/
theorem IsKConnected.two_isVertexConnected
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsKConnected 2) :
    G.IsVertexConnected 2 :=
  haveI : Nontrivial V := IsKConnected.two_nontrivial h
  IsKConnected.isVertexConnected G h

/-- Every 2-connected graph contains a cycle. Choose distinct vertices and
a nonempty walk between them. Its first edge lies on a cycle by
`IsVertexConnected.exists_cycle_through_adj`. -/
theorem IsKConnected.two_exists_cycle
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsKConnected 2) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle := by
  have hVC : G.IsVertexConnected 2 := IsKConnected.two_isVertexConnected hG
  have hcard : 3 ≤ Fintype.card V := IsKConnected.two_card_ge_three hG
  have hconn : G.Connected := hVC.connected_of_one_le (by omega)
  -- Choose distinct vertices using nontriviality.
  haveI : Nontrivial V := IsKConnected.two_nontrivial hG
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  -- Connectedness supplies a walk between them.
  obtain ⟨w⟩ := hconn.preconnected u v
  -- Their distinctness excludes a nil walk.
  have hne : ¬ w.Nil := by
    intro hnil
    exact huv hnil.eq
  -- The first edge gives adjacency to the walk's second vertex.
  have hadj : G.Adj u w.snd := Walk.adj_snd hne
  -- Apply exists_cycle_through_adj to that edge.
  obtain ⟨x, c, hc, _, _⟩ := hVC.exists_cycle_through_adj hadj
  exact ⟨x, c, hc⟩

/-! ## H-paths extending a proper subgraph -/

/-- Every nonempty proper vertex set of a connected graph has a boundary edge. -/
private lemma Connected.exists_adj_mem_not_mem
    {G : SimpleGraph V} (hG : G.Connected) {S : Set V}
    (hS : S.Nonempty) (hproper : ¬ ∀ v, v ∈ S) :
    ∃ y v : V, y ∈ S ∧ v ∉ S ∧ G.Adj y v := by
  obtain ⟨y, hyS⟩ := hS
  obtain ⟨v, hvS⟩ := not_forall.mp hproper
  obtain ⟨q⟩ := hG.preconnected y v
  obtain ⟨d, _hdq, hdy, hdv⟩ := q.exists_boundary_dart S hyS hvS
  exact ⟨d.fst, d.snd, hdy, hdv, d.adj⟩

/-- If H is not spanning, 2-connectivity supplies an H-path that strictly
extends H. Choose a boundary edge from y in H to v outside H. Deleting y
leaves the graph connected, so v can reach another H-vertex while avoiding y.
Stop at the first return to H and prepend the boundary edge. -/
theorem IsVertexConnected.exists_strict_hpath_extension_of_not_isSpanning
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsVertexConnected 2) {H : G.Subgraph}
    (hpair : ∃ a b : V, a ∈ H.verts ∧ b ∈ H.verts ∧ a ≠ b)
    (hspan : ¬ H.IsSpanning) :
    ∃ (u v : V) (p : G.Walk u v),
      IsHPath G H p ∧ H < H ⊔ p.toSubgraph := by
  classical
  obtain ⟨a, b, haH, hbH, hab⟩ := hpair
  have hconn : G.Connected := hG.connected_of_one_le (by omega)
  obtain ⟨y, v, hyH, hvH, hyv⟩ :=
    hconn.exists_adj_mem_not_mem ⟨a, haH⟩ hspan
  obtain ⟨z, hzH, hzy⟩ : ∃ z : V, z ∈ H.verts ∧ z ≠ y := by
    by_cases hay : a = y
    · refine ⟨b, hbH, ?_⟩
      intro hby
      exact hab (hay.trans hby.symm)
    · exact ⟨a, haH, hay⟩
  have hvy : v ≠ y := by
    intro hvy
    apply hvH
    simpa [hvy] using hyH
  obtain ⟨q, hq_avoid⟩ := hG.exists_walk_avoiding_vertex hvy hzy
  let qp : G.Path v z := q.toPath
  have hqp_avoid : y ∉ (qp : G.Walk v z).support := by
    intro hyqp
    exact hq_avoid (q.support_toPath_subset hyqp)
  have hmeet :
      {t ∈ H.verts.toFinset | t ∈ (qp : G.Walk v z).support}.Nonempty := by
    refine ⟨z, Finset.mem_filter.mpr ⟨Set.mem_toFinset.mpr hzH, ?_⟩⟩
    exact Walk.end_mem_support _
  obtain ⟨x, hxHfin, hxqp, hfirst⟩ :=
    (qp : G.Walk v z).exists_mem_support_forall_mem_support_imp_eq
      H.verts.toFinset hmeet
  have hxH : x ∈ H.verts := Set.mem_toFinset.mp hxHfin
  let r : G.Walk v x := (qp : G.Walk v z).takeUntil x hxqp
  have hr_path : r.IsPath := by
    dsimp only [r]
    exact qp.property.takeUntil hxqp
  have hyr : y ∉ r.support := by
    intro hyr
    exact hqp_avoid (Walk.support_takeUntil_subset _ hxqp hyr)
  have hfirst_r : ∀ t ∈ H.verts.toFinset, t ∈ r.support → t = x := by
    simpa only [r] using hfirst
  let p : G.Walk y x := Walk.cons hyv r
  have hp_path : p.IsPath := by
    dsimp only [p]
    exact Walk.IsPath.cons hr_path hyr
  have hpH : IsHPath G H p := by
    refine {
      isPath := hp_path
      start_mem := hyH
      finish_mem := hxH
      interior_disj := ?_
      edges_disj := ?_
    }
    · intro w hwint hwH
      have hwr : w ∈ r.support := by
        unfold Walk.interior at hwint
        dsimp only [p] at hwint
        simpa only [Walk.support_cons, List.tail_cons] using
          List.mem_of_mem_dropLast hwint
      have hwx : w ≠ x := by
        unfold Walk.interior at hwint
        dsimp only [p] at hwint
        simp only [Walk.support_cons, List.tail_cons] at hwint
        have hne_last := hr_path.support_nodup.rel_dropLast_getLast hwint
        simpa only [Walk.getLast_support] using hne_last
      exact hwx (hfirst_r w (Set.mem_toFinset.mpr hwH) hwr)
    · intro e hep heH
      have he_cases : e = s(y, v) ∨ e ∈ r.edges := by
        dsimp only [p] at hep
        simpa only [Walk.edges_cons, List.mem_cons] using hep
      rcases he_cases with he | her
      · subst e
        have hyvH : H.Adj y v := Subgraph.mem_edgeSet.mp heH
        exact hvH hyvH.snd_mem
      · induction e using Sym2.ind with
        | _ e₁ e₂ =>
          have heH' : H.Adj e₁ e₂ := Subgraph.mem_edgeSet.mp heH
          have he₁x : e₁ = x := hfirst_r e₁
            (Set.mem_toFinset.mpr heH'.fst_mem)
            (r.fst_mem_support_of_mem_edges her)
          have he₂x : e₂ = x := hfirst_r e₂
            (Set.mem_toFinset.mpr heH'.snd_mem)
            (r.snd_mem_support_of_mem_edges her)
          exact (G.ne_of_adj (r.adj_of_mem_edges her)) (he₁x.trans he₂x.symm)
  refine ⟨y, x, p, hpH, ?_⟩
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  apply hvH
  rw [heq, Subgraph.verts_sup]
  exact Or.inr (p.mem_verts_toSubgraph.mpr <| by
    dsimp only [p]
    rw [Walk.support_cons]
    exact List.mem_cons_of_mem _ r.start_mem_support)

/-- If H is spanning but not the whole graph, a missing edge is a one-edge
H-path whose addition strictly extends H. -/
theorem Subgraph.exists_strict_hpath_extension_of_isSpanning
    {G : SimpleGraph V} [DecidableEq V] {H : G.Subgraph}
    (hspan : H.IsSpanning) (htop : H ≠ ⊤) :
    ∃ (u v : V) (p : G.Walk u v),
      IsHPath G H p ∧ H < H ⊔ p.toSubgraph := by
  classical
  have hmissing : ∃ u v : V, G.Adj u v ∧ ¬ H.Adj u v := by
    by_contra h
    have hall : ∀ u v : V, G.Adj u v → H.Adj u v := by
      intro u v huvG
      by_contra huvH
      exact h ⟨u, v, huvG, huvH⟩
    apply htop
    apply le_antisymm le_top
    refine ⟨?_, ?_⟩
    · intro v _hv
      exact hspan v
    · intro u v huv
      exact hall u v (Subgraph.top_adj.mp huv)
  obtain ⟨u, v, huvG, huvH⟩ := hmissing
  let p : G.Walk u v := Walk.cons huvG Walk.nil
  have hpH : IsHPath G H p := by
    refine {
      isPath := ?_
      start_mem := hspan u
      finish_mem := hspan v
      interior_disj := ?_
      edges_disj := ?_
    }
    · dsimp only [p]
      exact Walk.IsPath.cons Walk.IsPath.nil (by simpa using huvG.ne)
    · intro w hw
      simp [p, Walk.interior] at hw
    · intro e he
      have heq : e = s(u, v) := by
        simpa [p] using he
      subst e
      simpa only [Subgraph.mem_edgeSet] using huvH
  refine ⟨u, v, p, hpH, ?_⟩
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  apply huvH
  rw [heq, Subgraph.sup_adj]
  right
  rw [Walk.adj_toSubgraph_iff_mem_edges]
  simp [p]

/-- In a 2-connected graph, a proper subgraph with at least two vertices
has an H-path whose addition gives a strict extension. -/
theorem IsVertexConnected.exists_strict_hpath_extension
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsVertexConnected 2) {H : G.Subgraph}
    (hpair : ∃ a b : V, a ∈ H.verts ∧ b ∈ H.verts ∧ a ≠ b)
    (htop : H ≠ ⊤) :
    ∃ (u v : V) (p : G.Walk u v),
      IsHPath G H p ∧ H < H ⊔ p.toSubgraph := by
  by_cases hspan : H.IsSpanning
  · exact H.exists_strict_hpath_extension_of_isSpanning hspan htop
  · exact hG.exists_strict_hpath_extension_of_not_isSpanning hpair hspan

/-! ## A maximal constructible subgraph -/

/-- Every finite 2-connected graph is constructible from a cycle by
successively adding H-paths. Choose an inclusion-maximal constructible
subgraph containing an initial cycle. If it were proper, an extending H-path
would contradict maximality. -/
theorem IsKConnected.two_isConstructibleFromCycle_top
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsKConnected 2) :
    IsConstructibleFromCycle G ⊤ := by
  obtain ⟨u, c, hc⟩ := hG.two_exists_cycle
  have hbase : IsConstructibleFromCycle G c.toSubgraph :=
    IsConstructibleFromCycle.cycleBase c hc
  obtain ⟨H, _hbase_le, hmax⟩ :=
    @Finite.exists_le_maximal _ _ _
      (fun H : G.Subgraph => IsConstructibleFromCycle G H) c.toSubgraph hbase
  have hVC : G.IsVertexConnected 2 := hG.two_isVertexConnected
  have htop : H = ⊤ := by
    by_contra hne
    obtain ⟨a, b, d, ha, hb, _hd, hab, _hbd, _had⟩ :=
      hmax.prop.exists_three_distinct_verts
    obtain ⟨x, y, p, hp, hlt⟩ :=
      hVC.exists_strict_hpath_extension ⟨a, b, ha, hb, hab⟩ hne
    have hnext : IsConstructibleFromCycle G (H ⊔ p.toSubgraph) :=
      hmax.prop.add_hpath hp
    exact (hmax.not_prop_of_gt hlt) hnext
  simpa only [htop] using hmax.prop

/-- A well-typed witness variant of the construction theorem.
`H.spanningCoe = G` compares graphs on the same vertex type V. -/
theorem IsKConnected.two_exists_constructible_spanning
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsKConnected 2) :
    ∃ H : G.Subgraph,
      IsConstructibleFromCycle G H ∧ H.IsSpanning ∧ H.spanningCoe = G := by
  exact ⟨⊤, hG.two_isConstructibleFromCycle_top, by simp [Subgraph.IsSpanning],
    Subgraph.spanningCoe_top⟩

/-! ## The graph-theoretic equivalence -/

/-- A finite graph is 2-connected exactly when it is constructible from
a cycle by successive additions of H-paths. The construction direction gives
2-connectivity on the full subgraph's vertex type; the canonical graph
isomorphism transfers it to G. -/
theorem isKConnected_two_iff_isConstructibleFromCycle_top
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    G.IsKConnected 2 ↔ IsConstructibleFromCycle G ⊤ := by
  constructor
  · exact IsKConnected.two_isConstructibleFromCycle_top
  · intro h
    let e : (⊤ : G.Subgraph).spanningCoe ≃g (⊤ : G.Subgraph).coe :=
      (⊤ : G.Subgraph).spanningCoeEquivCoeOfSpanning (fun _ => Set.mem_univ _)
    letI : Fintype (⊤ : G.Subgraph).verts :=
      Fintype.ofEquiv V e.toEquiv
    have hcoe : (⊤ : G.Subgraph).coe.IsKConnected 2 := h.isKConnected_two
    letI : DecidableRel (⊤ : G.Subgraph).spanningCoe.Adj := Classical.decRel _
    have hspanningCoe : (⊤ : G.Subgraph).spanningCoe.IsKConnected 2 :=
      (e.isKConnected_iff 2).mpr hcoe
    simpa only [Subgraph.spanningCoe_top] using hspanningCoe

end SimpleGraph
