/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import GraphTheory.HPathStepNoCutVertex
import GraphTheory.SimpleGraph.Block.CycleNoCutVertex
import GraphTheory.SimpleGraph.Connectivity.Whitney

/-!
# Cycle-and-path constructions are two-connected

This module proves that a subgraph constructed from a cycle by successively adding H-paths is two-connected. It also connects the operational two-connectivity predicate to `SimpleGraph.IsKConnected 2` for finite graphs.
-/

namespace SimpleGraph

variable {V : Type*}





theorem IsConstructibleFromCycle.isTwoConnected
    {G : SimpleGraph V} {H : G.Subgraph}
    (h : IsConstructibleFromCycle G H) : H.IsTwoConnected := by
  induction h with
  | cycleBase c hc =>
      refine ⟨c.toSubgraph_connected, ?_, ?_⟩
      · exact (IsConstructibleFromCycle.cycleBase c hc).exists_three_distinct_verts
      · intro v hv
        exact Subgraph.connected_iff'.mpr
          (Walk.IsCycle.toSubgraph_no_cut_vertex c hc v hv)
  | addHPath H' p ih hp ihTwo =>
      have hnext : IsConstructibleFromCycle G (H' ⊔ p.toSubgraph) :=
        IsConstructibleFromCycle.addHPath H' p ih hp
      exact ⟨hnext.connected, hnext.exists_three_distinct_verts,
        ihTwo.no_cut_vertex_after_addHPath p hp⟩









theorem Subgraph.IsTwoConnected.coe_isKConnected_two
    {G : SimpleGraph V} {H : G.Subgraph}
    [Fintype H.verts] [DecidableEq H.verts] [DecidableRel H.coe.Adj]
    (hH : H.IsTwoConnected) : H.coe.IsKConnected 2 := by
  have hcard : 2 < Fintype.card H.verts := by
    obtain ⟨a, b, d, ha, hb, hd, hab, hbd, had⟩ := hH.three_distinct
    let a' : H.verts := ⟨a, ha⟩
    let b' : H.verts := ⟨b, hb⟩
    let d' : H.verts := ⟨d, hd⟩
    have hab' : a' ≠ b' := by
      intro h
      exact hab (congrArg Subtype.val h)
    have hbd' : b' ≠ d' := by
      intro h
      exact hbd (congrArg Subtype.val h)
    have had' : a' ≠ d' := by
      intro h
      exact had (congrArg Subtype.val h)
    have hthree : ({a', b', d'} : Finset H.verts).card = 3 := by
      simp [hab', hbd', had']
    have hle : 3 ≤ Fintype.card H.verts := by
      calc
        3 = ({a', b', d'} : Finset H.verts).card := hthree.symm
        _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card H.verts := Finset.card_univ
    omega
  have hVC : H.coe.IsVertexConnected 2 := by
    refine ⟨hcard, ?_⟩
    intro S hS
    interval_cases hScard : S.card
    · have hS : S = ∅ := Finset.card_eq_zero.mp hScard
      subst S
      have hset :
          (((Finset.univ \ ∅ : Finset H.verts) : Set H.verts)) = Set.univ := by
        ext x
        simp
      rw [hset]
      exact H.coe.induceUnivIso.connected_iff.mpr hH.connected.coe
    · rw [Finset.card_eq_one] at hScard
      obtain ⟨v, rfl⟩ := hScard
      have hset :
          (((Finset.univ \ {v} : Finset H.verts) : Set H.verts)) =
            {x : H.verts | (x : V) ∉ ({v.val} : Set V)} := by
        ext x
        simp
        constructor
        · intro hx hxval
          exact hx (Subtype.ext hxval)
        · intro hx hxsub
          exact hx (congrArg Subtype.val hxsub)
      rw [hset]
      exact (H.coeDeleteVertsIso {v.val}).connected_iff.mp
        (hH.no_cut_vertex v.val v.property)
  haveI : Nontrivial H.verts :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact H.coe.le_vertexConnectivity_of_isVertexConnected hVC





theorem IsConstructibleFromCycle.isKConnected_two
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {H : G.Subgraph} [Fintype H.verts] [DecidableRel H.coe.Adj]
    (h : IsConstructibleFromCycle G H) : H.coe.IsKConnected 2 :=
  h.isTwoConnected.coe_isKConnected_two

end SimpleGraph
