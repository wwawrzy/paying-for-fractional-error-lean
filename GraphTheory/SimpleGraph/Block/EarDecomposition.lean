/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import GraphTheory.SimpleGraph.Connectivity.Whitney
import GraphTheory.SimpleGraph.Block.Defs
import Mathlib.Tactic

/-!
# Connectivity and cycles in finite graphs

This module develops consequences of vertex connectivity two for finite graphs: connectedness, absence of cut vertices, and cycle and walk existence under vertex or edge avoidance. It proves that edge subdivision preserves vertex connectivity two and establishes cycle-through-two-edges results used to characterize the common-cycle relation on edges.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*}














theorem IsVertexConnected.card_gt_two {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (h : G.IsVertexConnected 2) :
    2 < Fintype.card V :=
  h.1




theorem IsVertexConnected.no_cut_vertex_of_two {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (h : G.IsVertexConnected 2) (v : V) :
    (G.induce ((Finset.univ \ ({v} : Finset V) : Finset V) : Set V)).Connected :=
  h.2 {v} (by simp)




theorem IsVertexConnected.connected_of_one_le {G : SimpleGraph V} [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {k : Nat} (hk : 1 ≤ k)
    (h : G.IsVertexConnected k) : G.Connected := by
  have hconn := h.2 ∅ (by simp; omega)
  have huniv : ((Finset.univ \ ∅ : Finset V) : Set V) = Set.univ := by simp
  rw [huniv] at hconn
  exact G.induceUnivIso.connected_iff.mp hconn





theorem IsVertexConnected.deleteEdges_singleton_connected
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) (e : Sym2 V) :
    (G.deleteEdges {e}).Connected := by
  have hdel : (G.deleteEdges {e}).IsVertexConnected 1 :=
    isVertexConnected_deleteEdges_singleton G h e
  exact hdel.connected_of_one_le (by omega)

















private lemma Walk.endpoints_of_edge_mem {G : SimpleGraph V} {x : V}
    {c : G.Walk x x} {u v : V} (h : s(u, v) ∈ c.edges) :
    u ∈ c.support ∧ v ∈ c.support :=
  ⟨c.fst_mem_support_of_mem_edges h, c.snd_mem_support_of_mem_edges h⟩




theorem IsVertexConnected.exists_cycle_through_adj
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) {u v : V} (huv : G.Adj u v) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ u ∈ c.support ∧ v ∈ c.support := by
  have hconn : (G.deleteEdges {s(u, v)}).Connected :=
    h.deleteEdges_singleton_connected s(u, v)
  have hreach : (G \ fromEdgeSet {s(u, v)}).Reachable u v := by
    have heq : G \ fromEdgeSet {s(u, v)} = G.deleteEdges {s(u, v)} := by
      rfl
    rw [heq]; exact hconn.preconnected u v
  obtain ⟨x, c, hc, he⟩ :=
    (adj_and_reachable_delete_edges_iff_exists_cycle (G := G) (v := u) (w := v)).mp
      ⟨huv, hreach⟩
  obtain ⟨hu, hv⟩ := Walk.endpoints_of_edge_mem he
  exact ⟨x, c, hc, hu, hv⟩










theorem IsVertexConnected.exists_walk_avoiding_vertex
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) {u v w : V} (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ Q : G.Walk u v, w ∉ Q.support := by
  set S : Set V :=
    ((Finset.univ \ ({w} : Finset V) : Finset V) : Set V) with hS
  have hconn : (G.induce S).Connected := h.no_cut_vertex_of_two w
  have huS : u ∈ S := by
    simp [hS, huw]
  have hvS : v ∈ S := by
    simp [hS, hvw]
  have hreach : (G.induce S).Reachable ⟨u, huS⟩ ⟨v, hvS⟩ :=
    hconn.preconnected ⟨u, huS⟩ ⟨v, hvS⟩
  obtain ⟨Q'⟩ := hreach
  
  
  refine ⟨Q'.map (Embedding.induce S).toHom, ?_⟩
  intro hw_in
  
  have hsupp := SimpleGraph.Walk.support_map (Embedding.induce S).toHom Q'
  have hw_in' : w ∈ List.map (⇑(Embedding.induce S).toHom) Q'.support := hsupp ▸ hw_in
  rw [List.mem_map] at hw_in'
  obtain ⟨⟨x, hx⟩, _, hxw⟩ := hw_in'
  
  
  have hx_eq_w : x = w := hxw
  subst hx_eq_w
  simp [hS] at hx









private lemma Walk.exists_first_mem
    {G : SimpleGraph V} {u v : V} (Q : G.Walk u v) (T : Set V) (hv : v ∈ T) :
    ∃ (t : V) (Q1 : G.Walk u t) (Q2 : G.Walk t v),
      t ∈ T ∧ Q = Q1.append Q2 ∧
      (∀ x ∈ Q1.support, x ≠ t → x ∉ T) := by
  classical
  induction Q with
  | nil =>
    
    exact ⟨_, .nil, .nil, hv, by simp, by
      intro x hx hxne
      simp only [Walk.support_nil, List.mem_singleton] at hx
      exact absurd hx hxne⟩
  | @cons u u' v hadj rest ih =>
    by_cases huT : u ∈ T
    · 
      refine ⟨u, .nil, .cons hadj rest, huT, by simp, ?_⟩
      intro x hx hxne
      simp only [Walk.support_nil, List.mem_singleton] at hx
      exact absurd hx hxne
    · 
      obtain ⟨t, R1, R2, htT, hQeq, hint⟩ := ih hv
      refine ⟨t, .cons hadj R1, R2, htT, ?_, ?_⟩
      · 
        rw [hQeq, Walk.cons_append]
      · intro x hx hxne
        
        rw [Walk.support_cons] at hx
        rcases List.mem_cons.mp hx with hxu | hxR1
        · subst hxu; exact huT
        · exact hint x hxR1 hxne






theorem IsVertexConnected.exists_cycle_through_two_vertices
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) {u v : V} (huv : u ≠ v) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ u ∈ c.support ∧ v ∈ c.support := by
  suffices aux : ∀ n, ∀ {u v : V}, G.dist u v ≤ n → u ≠ v →
      ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧ u ∈ c.support ∧ v ∈ c.support from
    aux _ le_rfl huv
  intro n
  induction n with
  | zero =>
    intro u v hd huv
    have hG : G.Connected := h.connected_of_one_le (by omega)
    have hd0 : G.dist u v = 0 := Nat.le_zero.mp hd
    exact absurd (hG.dist_eq_zero_iff.mp hd0) huv
  | succ n ih =>
    intro u v hd huv
    by_cases hd_le : G.dist u v ≤ n
    · exact ih hd_le huv
    have hd_gt : n < G.dist u v := Nat.lt_of_not_le hd_le
    have hd_eq : G.dist u v = n + 1 := by omega
    by_cases hn0 : n = 0
    · subst hn0
      have hadj : G.Adj u v := dist_eq_one_iff_adj.mp hd_eq
      exact h.exists_cycle_through_adj hadj
    
    have hG : G.Connected := h.connected_of_one_le (by omega)
    
    obtain ⟨p, hpd⟩ := hG.exists_walk_length_eq_dist u v
    have hp_len : p.length = n + 1 := by rw [hpd, hd_eq]
    have hp_pos : 0 < p.length := by rw [hp_len]; omega
    have hp_not_nil : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr hp_pos
    
    set w_neigh : V := p.snd with hw_def
    have hadj : G.Adj u w_neigh := p.adj_snd hp_not_nil
    
    have hd_wv : G.dist w_neigh v ≤ n := by
      have hle := SimpleGraph.dist_le p.tail
      have hrest_len : p.tail.length = n := by
        have := Walk.length_tail_add_one hp_not_nil
        omega
      change G.dist w_neigh v ≤ _ at hle
      omega
    
    have hwv : w_neigh ≠ v := by
      intro heq
      have hle : G.dist u v ≤ 1 := by
        rw [← heq]
        exact_mod_cast SimpleGraph.dist_le (Walk.cons hadj Walk.nil)
      omega
    
    obtain ⟨xc, c, hc, hwc, hvc⟩ := ih hd_wv hwv
    by_cases huc : u ∈ c.support
    · exact ⟨xc, c, hc, huc, hvc⟩
    
    have huw : u ≠ w_neigh := fun heq => huc (heq ▸ hwc)
    have hvw : v ≠ w_neigh := fun heq => hwv heq.symm
    
    obtain ⟨Q, hQ_avoid⟩ := h.exists_walk_avoiding_vertex huw hvw
    
    set Qp : G.Path u v := Q.toPath with hQp_def
    have hQp_avoid : w_neigh ∉ (Qp : G.Walk u v).support := by
      intro hin
      apply hQ_avoid
      exact Walk.support_toPath_subset Q hin
    have hQp_path : (Qp : G.Walk u v).IsPath := Qp.2
    
    have hv_in_Qp : v ∈ (Qp : G.Walk u v).support := Walk.end_mem_support _
    obtain ⟨t, Q1, Q2, htc, hQp_eq, _hQ1_int⟩ :=
      (Qp : G.Walk u v).exists_first_mem ({x | x ∈ c.support} : Set V) hvc
    
    have ht_in_Qp : t ∈ (Qp : G.Walk u v).support := by
      rw [hQp_eq, Walk.support_append]
      exact List.mem_append.mpr (Or.inl Q1.end_mem_support)
    
    have htw : t ≠ w_neigh := fun heq => hQp_avoid (heq ▸ ht_in_Qp)
    
    have htu : t ≠ u := fun heq => huc (heq ▸ htc)
    
    have hQ1_path : Q1.IsPath := by
      have : (Q1.append Q2).IsPath := hQp_eq ▸ hQp_path
      exact this.of_append_left
    
    have hc' : (c.rotate t htc).IsCycle := hc.rotate htc
    have hwc' : w_neigh ∈ (c.rotate t htc).support :=
      (c.mem_support_rotate_iff t htc).mpr hwc
    have hvc' : v ∈ (c.rotate t htc).support :=
      (c.mem_support_rotate_iff t htc).mpr hvc
    
    
    
    
    have hv_in_arcs :
        v ∈ ((c.rotate t htc).takeUntil w_neigh hwc').support ∨
        v ∈ (((c.rotate t htc).dropUntil w_neigh hwc').reverse).support := by
      have hv_split :
          v ∈ ((c.rotate t htc).takeUntil w_neigh hwc' |>.append
              ((c.rotate t htc).dropUntil w_neigh hwc')).support := by
        rw [(c.rotate t htc).take_spec hwc']; exact hvc'
      rw [Walk.support_append] at hv_split
      rcases List.mem_append.mp hv_split with h | h
      · exact Or.inl h
      · right
        rw [Walk.support_reverse, List.mem_reverse]
        exact List.mem_of_mem_tail h
    
    have hrot_support : (c.rotate t htc).support ⊆ c.support := fun x hx =>
      (c.mem_support_rotate_iff t htc).mp hx
    
    
    suffices build_cycle : ∀ (arc : G.Walk t w_neigh),
        arc.IsPath → arc.support ⊆ c.support → v ∈ arc.support →
        ∃ (x : V) (cy : G.Walk x x), cy.IsCycle ∧ u ∈ cy.support ∧ v ∈ cy.support by
      
      
      
      
      
      
      have htake_not_nil : ¬ ((c.rotate t htc).takeUntil w_neigh hwc').Nil := by
        rw [Walk.nil_takeUntil]
        exact htw
      have hdrop_path : ((c.rotate t htc).dropUntil w_neigh hwc').IsPath := by
        have heq := (c.rotate t htc).take_spec hwc'
        have hcyc :
            (((c.rotate t htc).takeUntil w_neigh hwc').append
              ((c.rotate t htc).dropUntil w_neigh hwc')).IsCycle := by
          rw [heq]; exact hc'
        exact hcyc.isPath_of_append_right htake_not_nil
      rcases hv_in_arcs with hv1 | hv2
      · 
        refine build_cycle ((c.rotate t htc).takeUntil w_neigh hwc') ?_ ?_ hv1
        · exact hc'.isPath_takeUntil hwc'
        · intro x hx
          exact hrot_support ((c.rotate t htc).support_takeUntil_subset hwc' hx)
      · 
        refine build_cycle (((c.rotate t htc).dropUntil w_neigh hwc').reverse) ?_ ?_ hv2
        · exact hdrop_path.reverse
        · intro x hx
          rw [Walk.support_reverse, List.mem_reverse] at hx
          exact hrot_support ((c.rotate t htc).support_dropUntil_subset hwc' hx)
    
    intro arc harc_path harc_sub hv_arc
    
    let path : G.Walk u w_neigh := Q1.append arc
    have hpath_def : path = Q1.append arc := rfl
    
    refine ⟨u, Walk.cons hadj path.reverse, ?_, ?_, ?_⟩
    · 
      
      rw [Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · 
        rw [Walk.isPath_reverse_iff]
        rw [Walk.isPath_def]
        rw [Walk.support_append, List.nodup_append]
        refine ⟨hQ1_path.support_nodup, harc_path.support_nodup.tail, ?_⟩
        intro x hxQ1 y hyarc
        
        intro hxy
        
        
        
        subst hxy
        have hx_arc_supp : x ∈ arc.support := List.mem_of_mem_tail hyarc
        have hx_in_c : x ∈ c.support := harc_sub hx_arc_supp
        have hx_eq_t : x = t := by
          by_contra hne
          exact _hQ1_int x hxQ1 hne hx_in_c
        have hnodup := harc_path.support_nodup
        have hsupp_eq : arc.support = t :: arc.support.tail := arc.support_eq_cons
        rw [hsupp_eq] at hnodup
        rw [hx_eq_t] at hyarc
        exact (List.Nodup.notMem hnodup) hyarc
      · 
        rw [Walk.edges_reverse, List.mem_reverse]
        
        rw [Walk.edges_append, List.mem_append, not_or]
        refine ⟨?_, ?_⟩
        · 
          intro he
          apply hQp_avoid
          have : w_neigh ∈ Q1.support := Q1.snd_mem_support_of_mem_edges he
          rw [hQp_eq, Walk.support_append]
          exact List.mem_append.mpr (Or.inl this)
        · 
          intro he
          apply huc
          exact harc_sub (arc.fst_mem_support_of_mem_edges he)
    · 
      rw [Walk.support_cons]
      exact List.mem_cons_self
    · 
      
      
      rw [Walk.support_cons, List.mem_cons]
      right
      rw [Walk.support_reverse, List.mem_reverse]
      
      rw [hpath_def, Walk.support_append]
      apply List.mem_append.mpr
      
      
      
      by_cases hvt : v = t
      · 
        left
        rw [hvt]
        exact Q1.end_mem_support
      · 
        right
        rw [Walk.support_eq_cons] at hv_arc
        rcases List.mem_cons.mp hv_arc with hvt' | hv_tail
        · exact absurd hvt' hvt
        · exact hv_tail














theorem IsVertexConnected.exists_walk_avoiding_edge
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) (a b : V) (x y : V) :
    ∃ w : G.Walk x y, s(a, b) ∉ w.edges := by
  
  have hconn := h.deleteEdges_singleton_connected s(a, b)
  have hreach : (G \ fromEdgeSet {s(a, b)}).Reachable x y := by
    have heq : G \ fromEdgeSet {s(a, b)} = G.deleteEdges {s(a, b)} := rfl
    rw [heq]
    exact hconn.preconnected x y
  
  exact (reachable_delete_edges_iff_exists_walk).mp hreach




theorem IsVertexConnected.no_cut_vertex_walk
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) (z x y : V) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w : G.Walk x y, ∀ q ∈ w.support, q ≠ z := by
  obtain ⟨w, hw⟩ := h.exists_walk_avoiding_vertex hxz hyz
  exact ⟨w, fun q hq heq => hw (heq ▸ hq)⟩






private noncomputable def Walk.toInducedSubd
    {V' : Type*} {G' : SimpleGraph V'}
    {a b : V'} (w : G'.Walk a b) (s : Set V')
    (hsub : ∀ x ∈ w.support, x ∈ s)
    (ha : a ∈ s) (hb : b ∈ s) :
    (G'.induce s).Walk ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction w with
  | nil => exact Walk.nil
  | cons hadj w' ih =>
      rename_i u v w
      have hv_in : v ∈ s := hsub v (by simp)
      have hw_sub : ∀ x ∈ w'.support, x ∈ s := by
        intro x hx
        exact hsub x (by simp [hx])
      have hadj_ind : (G'.induce s).Adj ⟨u, ha⟩ ⟨v, hv_in⟩ := by
        rw [induce_adj]; exact hadj
      exact Walk.cons hadj_ind (ih hw_sub hv_in hb)











theorem IsVertexConnected.subdivideEdge
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) {a b : V} (hab : G.Adj a b) :
    (G.subdivideEdge a b).IsVertexConnected 2 := by
  refine ⟨?_, ?_⟩
  · 
    have h1 : 2 < Fintype.card V := h.1
    rw [Fintype.card_sum, Fintype.card_unit]; omega
  · 
    intro S hS
    set T : Set (V ⊕ Unit) :=
      ((Finset.univ \ S : Finset (V ⊕ Unit)) : Set (V ⊕ Unit)) with hT_def
    
    have hT_char : ∀ q : V ⊕ Unit, q ∈ T ↔ q ∉ S := by
      intro q
      simp [hT_def]
    
    
    
    
    rw [connected_iff]
    refine ⟨?_, ?_⟩
    · 
      intro ⟨x', hx'⟩ ⟨y', hy'⟩
      have hx_notS : x' ∉ S := (hT_char x').mp hx'
      have hy_notS : y' ∉ S := (hT_char y').mp hy'
      
      have hwalk : ∃ w : (G.subdivideEdge a b).Walk x' y',
          ∀ q ∈ w.support, q ∉ S := by
        by_cases hSemp : S = ∅
        · 
          
          
          subst hSemp
          
          
          
          have hcard : 3 < Fintype.card (V ⊕ Unit) := by
            have h1 : 2 < Fintype.card V := h.1
            rw [Fintype.card_sum, Fintype.card_unit]; omega
          have hex : ∃ z : V ⊕ Unit, z ≠ x' ∧ z ≠ y' := by
            by_contra hne
            
            
            have hall : ∀ z : V ⊕ Unit, z = x' ∨ z = y' := by
              intro z
              by_contra hzz
              rw [not_or] at hzz
              exact hne ⟨z, hzz.1, hzz.2⟩
            have hsub : (Finset.univ : Finset (V ⊕ Unit)) ⊆ {x', y'} := by
              intro z _
              rcases hall z with h1 | h1
              · simp [h1]
              · simp [h1]
            have hle : Fintype.card (V ⊕ Unit) ≤ 2 := by
              calc Fintype.card (V ⊕ Unit)
                  = (Finset.univ : Finset (V ⊕ Unit)).card := rfl
                _ ≤ ({x', y'} : Finset (V ⊕ Unit)).card :=
                    Finset.card_le_card hsub
                _ ≤ 2 := by
                    by_cases heq : x' = y'
                    · simp [heq]
                    · rw [Finset.card_insert_of_notMem (by simpa using heq),
                          Finset.card_singleton]
            omega
          obtain ⟨z, hzx, hzy⟩ := hex
          obtain ⟨w, hw⟩ := subdivideEdge_walk_avoiding a b hab
            h.no_cut_vertex_walk (h.exists_walk_avoiding_edge a b) z x' y'
            (Ne.symm hzx) (Ne.symm hzy)
          exact ⟨w, fun q hq => by simp⟩
        · 
          have hSone : S.card = 1 := by
            have h0 : S.card ≠ 0 := fun h0 => hSemp (Finset.card_eq_zero.mp h0)
            omega
          obtain ⟨z, hSz⟩ := Finset.card_eq_one.mp hSone
          subst hSz
          have hxz : x' ≠ z := by simpa using hx_notS
          have hyz : y' ≠ z := by simpa using hy_notS
          obtain ⟨w, hw⟩ := subdivideEdge_walk_avoiding a b hab
            h.no_cut_vertex_walk (h.exists_walk_avoiding_edge a b) z x' y' hxz hyz
          refine ⟨w, ?_⟩
          intro q hq
          simp only [Finset.mem_singleton]
          exact hw q hq
      obtain ⟨w, hw_avoid⟩ := hwalk
      have hsub : ∀ q ∈ w.support, q ∈ T := by
        intro q hq
        exact (hT_char q).mpr (hw_avoid q hq)
      exact (w.toInducedSubd T hsub hx' hy').reachable
    · 
      
      have hcard_VU : 2 < Fintype.card (V ⊕ Unit) := by
        have h1 : 2 < Fintype.card V := h.1
        rw [Fintype.card_sum, Fintype.card_unit]; omega
      have hT_ne : T.Nonempty := by
        have : ((Finset.univ \ S : Finset (V ⊕ Unit))).Nonempty := by
          rw [← Finset.card_pos]
          have : (Finset.univ \ S : Finset (V ⊕ Unit)).card =
              Fintype.card (V ⊕ Unit) - S.card := by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
            rfl
          omega
        obtain ⟨q, hq⟩ := this
        refine ⟨q, ?_⟩
        rw [hT_def]
        exact_mod_cast hq
      obtain ⟨q, hq⟩ := hT_ne
      exact ⟨⟨q, hq⟩⟩









theorem IsVertexConnected.exists_cycle_through_two_edges
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : G.IsVertexConnected 2) {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) :
    ∃ (x : V) (cyc : G.Walk x x),
      cyc.IsCycle ∧ s(a, b) ∈ cyc.edges ∧ s(c, d) ∈ cyc.edges := by
  
  set G' : SimpleGraph (V ⊕ Unit) := G.subdivideEdge a b with hG'
  
  have hG'_vc : G'.IsVertexConnected 2 := h.subdivideEdge hab
  
  have hcd_ne_ab : s(c, d) ≠ s(a, b) := fun h => hne h.symm
  
  have hG'_cd : G'.Adj (Sum.inl c) (Sum.inl d) :=
    subdivideEdge_adj_inl_inl_of_ne G a b hcd hcd_ne_ab
  
  
  set G'' : SimpleGraph ((V ⊕ Unit) ⊕ Unit) :=
    G'.subdivideEdge (Sum.inl c) (Sum.inl d) with hG''
  
  have hG''_vc : G''.IsVertexConnected 2 := hG'_vc.subdivideEdge hG'_cd
  
  
  
  let z₁ : (V ⊕ Unit) ⊕ Unit := Sum.inl (Sum.inr ())
  let z₂ : (V ⊕ Unit) ⊕ Unit := Sum.inr ()
  have hz_ne : z₁ ≠ z₂ := Sum.inl_ne_inr
  obtain ⟨xc, c'', hc''_cyc, hz₁_in, hz₂_in⟩ :=
    hG''_vc.exists_cycle_through_two_vertices hz_ne
  
  
  
  obtain ⟨v', c', hc'_cyc, hcd_in_c', hc'_edges_from_c'', hc'_inl_inl_edges⟩ :=
    Walk.fromSubdivide_cycle hG'_cd hc''_cyc hz₂_in
  
  
  
  
  
  
  
  
  have hc'_inr_in_support : (Sum.inr () : V ⊕ Unit) ∈ c'.support := by
    
    set r := c''.rotate z₁ hz₁_in with hr_def
    have hr_cyc : r.IsCycle := hc''_cyc.rotate hz₁_in
    have hr_perm : r.edges ~r c''.edges := c''.rotate_edges z₁ hz₁_in
    have hr_pos : 0 < r.length := by
      have := hr_cyc.three_le_length; omega
    have hr_not_nil : ¬ r.Nil := Walk.not_nil_iff_lt_length.mpr hr_pos
    
    set z' := r.snd with hz'_def
    have h_adj_z₁_z' : G''.Adj z₁ z' := r.adj_snd hr_not_nil
    
    have hz'_inl : ∃ y : V ⊕ Unit, z' = Sum.inl y := by
      
      
      
      
      cases hz'_eq : z' with
      | inl y => exact ⟨y, rfl⟩
      | inr u =>
          exfalso
          rw [hz'_eq] at h_adj_z₁_z'
          
          
          rw [subdivideEdge_adj_inl_inr] at h_adj_z₁_z'
          rcases h_adj_z₁_z' with h | h
          · exact Sum.inr_ne_inl h
          · exact Sum.inr_ne_inl h
    obtain ⟨y, hy_eq⟩ := hz'_inl
    
    have h_first_in_r : s(z₁, z') ∈ r.edges := by
      have h_dart_mem : r.firstDart hr_not_nil ∈ r.darts :=
        Walk.firstDart_mem_darts hr_not_nil
      have h_edge_eq : (r.firstDart hr_not_nil).edge = s(z₁, z') :=
        Walk.edge_firstDart r hr_not_nil
      have h_edge_mem :
          (r.firstDart hr_not_nil).edge ∈ r.darts.map (·.edge) :=
        List.mem_map.mpr ⟨_, h_dart_mem, rfl⟩
      rw [h_edge_eq] at h_edge_mem
      change s(z₁, z') ∈ r.edges
      simpa [Walk.edges] using h_edge_mem
    rw [hy_eq] at h_first_in_r
    
    have h_first_in_c'' :
        s((Sum.inl (Sum.inr ()) : (V ⊕ Unit) ⊕ Unit), Sum.inl y) ∈ c''.edges :=
      (hr_perm.mem_iff).mp h_first_in_r
    
    have h_in_c' : s((Sum.inr () : V ⊕ Unit), y) ∈ c'.edges :=
      hc'_inl_inl_edges (Sum.inr ()) y h_first_in_c''
    
    exact c'.fst_mem_support_of_mem_edges h_in_c'
  
  
  obtain ⟨v_final, cyc, hcyc_isCyc, hab_in_cyc, _hcyc_edges_from_c', hcyc_inl_inl_edges⟩ :=
    Walk.fromSubdivide_cycle hab hc'_cyc hc'_inr_in_support
  
  
  have hcd_in_cyc : s(c, d) ∈ cyc.edges :=
    hcyc_inl_inl_edges c d hcd_in_c'
  exact ⟨v_final, cyc, hcyc_isCyc, hab_in_cyc, hcd_in_cyc⟩




















theorem Walk.whitney_cycle_through_two_edges_of_paths_special
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b)
    (p₁ p₂ : G.Walk a b) (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath) (hne : a ≠ b)
    {e₁ e₃ : Sym2 V} (he₁ : e₁ ∈ p₁.edges) (he₃ : e₃ ∈ p₂.edges) (hne13 : e₁ ≠ e₃)
    (h₁_avoid : s(a, b) ∉ p₁.edges) (h₂_avoid : s(a, b) ∉ p₂.edges) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ e₁ ∈ c.edges ∧ e₃ ∈ c.edges := by
  let S : Set V := (↑(G.unionSupportFinset p₁ p₂) : Set V)
  have h2c : ((G ⊔ SimpleGraph.edge a b).induce S).IsVertexConnected 2 :=
    induce_unionSupport_sup_edge_isVertexConnected_two G p₁ p₂ hp₁ hp₂ hne
      h₁_avoid h₂_avoid
  have hS_char : ∀ u : V, u ∈ S ↔ u ∈ p₁.support ∨ u ∈ p₂.support := by
    intro u; simp [S, unionSupportFinset]
  obtain ⟨u₁, w₁⟩ := e₁
  have hu₁_p₁ : u₁ ∈ p₁.support := p₁.fst_mem_support_of_mem_edges he₁
  have hw₁_p₁ : w₁ ∈ p₁.support := p₁.snd_mem_support_of_mem_edges he₁
  have hu₁_S : u₁ ∈ S := (hS_char u₁).mpr (Or.inl hu₁_p₁)
  have hw₁_S : w₁ ∈ S := (hS_char w₁).mpr (Or.inl hw₁_p₁)
  have huw₁_G : G.Adj u₁ w₁ := p₁.adj_of_mem_edges he₁
  have huw₁_sup : (G ⊔ SimpleGraph.edge a b).Adj u₁ w₁ :=
    (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl huw₁_G)
  have huw₁_H' : ((G ⊔ SimpleGraph.edge a b).induce S).Adj
      ⟨u₁, hu₁_S⟩ ⟨w₁, hw₁_S⟩ := huw₁_sup
  obtain ⟨u₃, w₃⟩ := e₃
  have hu₃_p₂ : u₃ ∈ p₂.support := p₂.fst_mem_support_of_mem_edges he₃
  have hw₃_p₂ : w₃ ∈ p₂.support := p₂.snd_mem_support_of_mem_edges he₃
  have hu₃_S : u₃ ∈ S := (hS_char u₃).mpr (Or.inr hu₃_p₂)
  have hw₃_S : w₃ ∈ S := (hS_char w₃).mpr (Or.inr hw₃_p₂)
  have huw₃_G : G.Adj u₃ w₃ := p₂.adj_of_mem_edges he₃
  have huw₃_sup : (G ⊔ SimpleGraph.edge a b).Adj u₃ w₃ :=
    (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl huw₃_G)
  have huw₃_H' : ((G ⊔ SimpleGraph.edge a b).induce S).Adj
      ⟨u₃, hu₃_S⟩ ⟨w₃, hw₃_S⟩ := huw₃_sup
  have hne_H' : s((⟨u₁, hu₁_S⟩ : S), ⟨w₁, hw₁_S⟩) ≠
                s((⟨u₃, hu₃_S⟩ : S), ⟨w₃, hw₃_S⟩) := by
    intro heq
    apply hne13
    have key := congr_arg (Sym2.map (Subtype.val (p := (· ∈ S)))) heq
    simpa using key
  obtain ⟨y, cyc, hcyc_isCycle, hr₁, hr₃⟩ :=
    h2c.exists_cycle_through_two_edges huw₁_H' huw₃_H' hne_H'
  let emb : (G ⊔ SimpleGraph.edge a b).induce S ↪g (G ⊔ SimpleGraph.edge a b) :=
    SimpleGraph.Embedding.induce S
  let cyc' : (G ⊔ SimpleGraph.edge a b).Walk y.val y.val :=
    cyc.map emb.toHom
  have h_inj : Function.Injective ⇑emb.toHom := emb.injective
  have hcyc'_isCycle : cyc'.IsCycle := hcyc_isCycle.map h_inj
  have he₁_in_cyc' : s(u₁, w₁) ∈ cyc'.edges := by
    change s(u₁, w₁) ∈ (cyc.map emb.toHom).edges
    rw [Walk.edges_map]
    refine List.mem_map.mpr ⟨s((⟨u₁, hu₁_S⟩ : S), ⟨w₁, hw₁_S⟩), hr₁, ?_⟩
    rfl
  have he₃_in_cyc' : s(u₃, w₃) ∈ cyc'.edges := by
    show s(u₃, w₃) ∈ (cyc.map emb.toHom).edges
    rw [Walk.edges_map]
    refine List.mem_map.mpr ⟨s((⟨u₃, hu₃_S⟩ : S), ⟨w₃, hw₃_S⟩), hr₃, ?_⟩
    rfl
  have h_edges_in_G : ∀ e ∈ cyc'.edges, e ∈ G.edgeSet := by
    intro e he
    have h_in_sup : e ∈ (G ⊔ SimpleGraph.edge a b).edgeSet :=
      cyc'.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_sup, Set.mem_union] at h_in_sup
    rcases h_in_sup with h | h
    · exact h
    · rw [SimpleGraph.edge_edgeSet_of_ne hab.ne] at h
      simp at h
      rw [h]
      exact hab
  refine ⟨y.val, cyc'.transfer G h_edges_in_G, ?_, ?_, ?_⟩
  · exact hcyc'_isCycle.transfer h_edges_in_G
  · rw [Walk.edges_transfer]; exact he₁_in_cyc'
  · rw [Walk.edges_transfer]; exact he₃_in_cyc'
















theorem SameBlockStep.trans
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {e₁ e₂ e₃ : Sym2 V}
    (h₁₂ : G.SameBlockStep e₁ e₂) (h₂₃ : G.SameBlockStep e₂ e₃) :
    G.SameBlockStep e₁ e₃ := by
  rcases h₁₂ with heq | ⟨u₁, c₁, hc₁, h₁e₁, h₁e₂⟩
  · exact heq ▸ h₂₃
  rcases h₂₃ with heq | ⟨u₂, c₂, hc₂, h₂e₂, h₂e₃⟩
  · exact heq ▸ Or.inr ⟨u₁, c₁, hc₁, h₁e₁, h₁e₂⟩
  by_cases hne13 : e₁ = e₃
  · exact Or.inl hne13
  obtain ⟨a, b⟩ := e₂
  have hab : G.Adj a b := c₁.adj_of_mem_edges h₁e₂
  by_cases h₁eq : e₁ = s(a, b)
  · exact Or.inr ⟨u₂, c₂, hc₂, h₁eq ▸ h₂e₂, h₂e₃⟩
  by_cases h₃eq : e₃ = s(a, b)
  · exact Or.inr ⟨u₁, c₁, hc₁, h₁e₁, h₃eq ▸ h₁e₂⟩
  obtain ⟨w₁, hw₁_path, hw₁_avoid, hw₁_e₁⟩ :=
    Walk.exists_walk_of_cycle_through_edge G hc₁ hab h₁e₂ h₁e₁ h₁eq
  obtain ⟨w₂, hw₂_path, hw₂_avoid, hw₂_e₃⟩ :=
    Walk.exists_walk_of_cycle_through_edge G hc₂ hab h₂e₂ h₂e₃ h₃eq
  obtain ⟨v, c, hc, hce₁, hce₃⟩ :=
    Walk.whitney_cycle_through_two_edges_of_paths_special G hab w₁ w₂
      hw₁_path hw₂_path hab.ne hw₁_e₁ hw₂_e₃ hne13 hw₁_avoid hw₂_avoid
  exact Or.inr ⟨v, c, hc, hce₁, hce₃⟩


theorem SameBlockStep.equivalence
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Equivalence G.SameBlockStep :=
  ⟨SameBlockStep.refl G, fun {_ _} => SameBlockStep.symm G,
    fun {_ _ _} => SameBlockStep.trans G⟩



theorem SameBlock_iff_SameBlockStep
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {e₁ e₂ : Sym2 V} :
    G.SameBlock e₁ e₂ ↔ G.SameBlockStep e₁ e₂ :=
  (SameBlockStep.equivalence G).eqvGen_iff

end SimpleGraph
