/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import GraphTheory.MaderPaths

/-!
# Construction from a cycle by adding paths

This module defines an inductive construction of a subgraph from a cycle by repeatedly adding an H-path whose endpoints lie in the existing subgraph and whose internal vertices are new. It proves basic structural properties of this construction, including connectedness and the existence of at least three vertices.
-/

namespace SimpleGraph

variable {V : Type*}















inductive IsConstructibleFromCycle (G : SimpleGraph V) : G.Subgraph → Prop where
  
  | cycleBase {u : V} (c : G.Walk u u) (hc : c.IsCycle) :
      IsConstructibleFromCycle G c.toSubgraph
  
  | addHPath (H : G.Subgraph) {u v : V} (p : G.Walk u v)
      (ih : IsConstructibleFromCycle G H) (hp : IsHPath G H p) :
      IsConstructibleFromCycle G (H ⊔ p.toSubgraph)





lemma IsConstructibleFromCycle.cycle_base {G : SimpleGraph V} {u : V}
    (c : G.Walk u u) (hc : c.IsCycle) :
    IsConstructibleFromCycle G c.toSubgraph :=
  IsConstructibleFromCycle.cycleBase c hc



lemma IsConstructibleFromCycle.add_hpath {G : SimpleGraph V} {H : G.Subgraph}
    {u v : V} {p : G.Walk u v}
    (ih : IsConstructibleFromCycle G H) (hp : IsHPath G H p) :
    IsConstructibleFromCycle G (H ⊔ p.toSubgraph) :=
  IsConstructibleFromCycle.addHPath H p ih hp




lemma IsConstructibleFromCycle.verts_nonempty {G : SimpleGraph V}
    {H : G.Subgraph} (h : IsConstructibleFromCycle G H) : H.verts.Nonempty := by
  induction h with
  | cycleBase c _hc =>
    
    exact ⟨_, c.start_mem_verts_toSubgraph⟩
  | addHPath H' p _ih _hp ihNE =>
    
    obtain ⟨w, hw⟩ := ihNE
    refine ⟨w, ?_⟩
    
    simp [Subgraph.verts_sup, hw]













lemma IsConstructibleFromCycle.connected {G : SimpleGraph V}
    {H : G.Subgraph} (h : IsConstructibleFromCycle G H) : H.Connected := by
  induction h with
  | cycleBase c _hc =>
    exact c.toSubgraph_connected
  | @addHPath H' u v p _ih hp ihConn =>
    
    refine Subgraph.connected_sup ihConn.preconnected
      p.toSubgraph_connected.preconnected ?_
    
    
    
    refine ⟨u, ?_⟩
    refine ⟨hp.start_mem, ?_⟩
    exact p.start_mem_verts_toSubgraph










lemma IsConstructibleFromCycle.step {G : SimpleGraph V} {H : G.Subgraph}
    (ih : IsConstructibleFromCycle G H)
    {u v : V} {p : G.Walk u v} (hp : IsHPath G H p) :
    IsConstructibleFromCycle G (H ⊔ p.toSubgraph) :=
  ih.add_hpath hp







































private lemma Walk.IsCycle.exists_three_distinct_support
    {G : SimpleGraph V} {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    ∃ a b d : V, a ∈ c.support ∧ b ∈ c.support ∧ d ∈ c.support ∧
      a ≠ b ∧ b ≠ d ∧ a ≠ d := by
  
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  
  have hlen : 3 ≤ c.support.tail.length := by
    rw [List.length_tail, Walk.length_support]
    have := hc.three_le_length; omega
  
  have h0 : 0 < c.support.tail.length := by omega
  have h1 : 1 < c.support.tail.length := by omega
  have h2 : 2 < c.support.tail.length := by omega
  set a := c.support.tail[0]'h0 with ha_def
  set b := c.support.tail[1]'h1 with hb_def
  set d := c.support.tail[2]'h2 with hd_def
  
  have ha_mem : a ∈ c.support := by
    refine List.mem_of_mem_tail ?_
    exact List.getElem_mem _
  have hb_mem : b ∈ c.support := by
    refine List.mem_of_mem_tail ?_
    exact List.getElem_mem _
  have hd_mem : d ∈ c.support := by
    refine List.mem_of_mem_tail ?_
    exact List.getElem_mem _
  
  refine ⟨a, b, d, ha_mem, hb_mem, hd_mem, ?_, ?_, ?_⟩
  · 
    intro hab
    have := List.Nodup.getElem_inj_iff hnodup |>.mp hab
    exact absurd this (by decide)
  · 
    intro hbd
    have := List.Nodup.getElem_inj_iff hnodup |>.mp hbd
    exact absurd this (by decide)
  · 
    intro had
    have := List.Nodup.getElem_inj_iff hnodup |>.mp had
    exact absurd this (by decide)














lemma IsConstructibleFromCycle.exists_three_distinct_verts {G : SimpleGraph V}
    {H : G.Subgraph} (h : IsConstructibleFromCycle G H) :
    ∃ a b d : V, a ∈ H.verts ∧ b ∈ H.verts ∧ d ∈ H.verts ∧
      a ≠ b ∧ b ≠ d ∧ a ≠ d := by
  induction h with
  | cycleBase c hc =>
    obtain ⟨a, b, d, ha, hb, hd, hab, hbd, had⟩ := hc.exists_three_distinct_support
    
    refine ⟨a, b, d, ?_, ?_, ?_, hab, hbd, had⟩
    · exact c.mem_verts_toSubgraph.mpr ha
    · exact c.mem_verts_toSubgraph.mpr hb
    · exact c.mem_verts_toSubgraph.mpr hd
  | addHPath H' p _ih _hp ihExists =>
    obtain ⟨a, b, d, ha, hb, hd, hab, hbd, had⟩ := ihExists
    
    refine ⟨a, b, d, ?_, ?_, ?_, hab, hbd, had⟩
    · simp [Subgraph.verts_sup, ha]
    · simp [Subgraph.verts_sup, hb]
    · simp [Subgraph.verts_sup, hd]



























structure Subgraph.IsTwoConnected {G : SimpleGraph V} (H : G.Subgraph) : Prop where
  
  connected : H.Connected
  
  three_distinct : ∃ a b d : V, a ∈ H.verts ∧ b ∈ H.verts ∧ d ∈ H.verts ∧
    a ≠ b ∧ b ≠ d ∧ a ≠ d
  

  no_cut_vertex : ∀ v ∈ H.verts, (H.deleteVerts {v}).Connected














lemma IsConstructibleFromCycle.connected_and_three_distinct {G : SimpleGraph V}
    {H : G.Subgraph} (h : IsConstructibleFromCycle G H) :
    H.Connected ∧ ∃ a b d : V, a ∈ H.verts ∧ b ∈ H.verts ∧ d ∈ H.verts ∧
      a ≠ b ∧ b ≠ d ∧ a ≠ d :=
  ⟨h.connected, h.exists_three_distinct_verts⟩

end SimpleGraph
