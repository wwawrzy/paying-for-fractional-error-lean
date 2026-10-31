/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import GraphTheory.SimpleGraph.Planar.Basic
import GraphTheory.SimpleGraph.Connectivity.Whitney
import GraphTheory.SimpleGraph.Connectivity.Menger
import GraphTheory.SimpleGraph.Block.Decomposition
import Mathlib.Tactic

/-!
# Block decomposition

This module formalizes blocks of a simple graph. Two edges are related when they are equal or lie on a common cycle, and the equivalence closure gives the block partition. It defines the quotient of edges into blocks, proves edge-partition and incidence-counting results, and constructs the subgraph and vertex set of each block. The final results relate block incidences to cut-vertex multiplicities and recover the graph from its block subgraphs.
-/

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)












def SameBlockStep (e₁ e₂ : Sym2 V) : Prop :=
  e₁ = e₂ ∨ ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ e₁ ∈ c.edges ∧ e₂ ∈ c.edges


theorem SameBlockStep.refl (e : Sym2 V) : G.SameBlockStep e e := Or.inl rfl


theorem SameBlockStep.symm {e₁ e₂ : Sym2 V} (h : G.SameBlockStep e₁ e₂) :
    G.SameBlockStep e₂ e₁ := by
  rcases h with heq | ⟨u, c, hc, h1, h2⟩
  · exact Or.inl heq.symm
  · exact Or.inr ⟨u, c, hc, h2, h1⟩









def SameBlock (e₁ e₂ : Sym2 V) : Prop :=
  Relation.EqvGen G.SameBlockStep e₁ e₂




theorem SameBlock.refl (e : Sym2 V) : G.SameBlock e e := Relation.EqvGen.refl e


theorem SameBlock.symm {e₁ e₂ : Sym2 V} (h : G.SameBlock e₁ e₂) :
    G.SameBlock e₂ e₁ := Relation.EqvGen.symm _ _ h


theorem SameBlock.trans {e₁ e₂ e₃ : Sym2 V}
    (h12 : G.SameBlock e₁ e₂) (h23 : G.SameBlock e₂ e₃) :
    G.SameBlock e₁ e₃ := Relation.EqvGen.trans _ _ _ h12 h23


theorem SameBlock.equivalence : Equivalence G.SameBlock :=
  Relation.EqvGen.is_equivalence G.SameBlockStep




theorem SameBlockStep.sameBlock {e₁ e₂ : Sym2 V} (h : G.SameBlockStep e₁ e₂) :
    G.SameBlock e₁ e₂ := Relation.EqvGen.rel _ _ h


theorem SameBlock.of_common_cycle {e₁ e₂ : Sym2 V} {u : V} {c : G.Walk u u}
    (hc : c.IsCycle) (h1 : e₁ ∈ c.edges) (h2 : e₂ ∈ c.edges) :
    G.SameBlock e₁ e₂ :=
  SameBlockStep.sameBlock G (Or.inr ⟨u, c, hc, h1, h2⟩)













section Whitney

variable [DecidableEq V]

omit [DecidableEq V] in




lemma Walk.exists_split_at_edge {u v a b : V} (hab : G.Adj a b) :
    ∀ (w : G.Walk u v), s(a, b) ∈ w.edges →
    (∃ (w₁ : G.Walk u a) (w₂ : G.Walk b v),
      w = w₁.append (Walk.cons hab w₂) ∧
      w.edges = w₁.edges ++ s(a,b) :: w₂.edges) ∨
    (∃ (w₁ : G.Walk u b) (w₂ : G.Walk a v),
      w = w₁.append (Walk.cons hab.symm w₂) ∧
      w.edges = w₁.edges ++ s(b,a) :: w₂.edges)
  | .nil, he => by simp [Walk.edges] at he
  | .cons (v := v') h0 p, he => by
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with h_eq | h_in
    · rcases (Sym2.eq_iff.mp h_eq) with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · subst ha; subst hb
        exact .inl ⟨.nil, p, by simp, by simp [Walk.edges_cons]⟩
      · subst ha; subst hb
        exact .inr ⟨.nil, p, by simp, by simp [Walk.edges_cons]⟩
    · rcases Walk.exists_split_at_edge hab p h_in with
        ⟨w₁, w₂, hp_eq, hedges⟩ | ⟨w₁, w₂, hp_eq, hedges⟩
      · exact .inl ⟨.cons h0 w₁, w₂, by rw [hp_eq]; rfl,
          by simp [Walk.edges_cons, hedges]⟩
      · exact .inr ⟨.cons h0 w₁, w₂, by rw [hp_eq]; rfl,
          by simp [Walk.edges_cons, hedges]⟩

omit [DecidableEq V] in










theorem Walk.exists_walk_of_cycle_through_edge
    {u a b : V} {c : G.Walk u u} (hc : c.IsCycle)
    (hab : G.Adj a b) (he : s(a, b) ∈ c.edges)
    {f : Sym2 V} (hfc : f ∈ c.edges) (hfne : f ≠ s(a, b)) :
    ∃ w : G.Walk a b, w.IsPath ∧ s(a, b) ∉ w.edges ∧ f ∈ w.edges := by
  have htrail : c.IsTrail := hc.isTrail
  have hnodup : c.edges.Nodup := htrail.edges_nodup
  
  have hnodup_tail : c.support.tail.Nodup := hc.support_nodup
  rcases Walk.exists_split_at_edge (G := G) hab c he with
    ⟨w₁, w₂, hc_eq, hedges⟩ | ⟨w₁, w₂, hc_eq, hedges⟩
  · 
    refine ⟨(w₂.append w₁).reverse, ?_, ?_, ?_⟩
    · 
      
      
      
      rw [Walk.isPath_reverse_iff, Walk.isPath_def]
      rw [hc_eq, Walk.support_append, Walk.support_cons, List.tail_append_of_ne_nil,
          List.tail_cons] at hnodup_tail
      · 
        
        rw [List.nodup_append] at hnodup_tail
        obtain ⟨hnd₁_tail, hnd₂, hdisj⟩ := hnodup_tail
        rw [Walk.support_append, List.nodup_append]
        refine ⟨hnd₂, hnd₁_tail, ?_⟩
        intro v hv₂ v' hv₁ heq
        subst heq
        exact hdisj v hv₁ v hv₂ rfl
      · exact w₁.support_ne_nil
    · simp only [Walk.edges_reverse, List.mem_reverse, Walk.edges_append,
        List.mem_append, not_or]
      rw [hedges, List.nodup_append] at hnodup
      obtain ⟨_, hcons, hdisj⟩ := hnodup
      simp only [List.nodup_cons] at hcons
      refine ⟨hcons.1, ?_⟩
      intro h
      exact hdisj _ h _ (by simp) rfl
    · simp only [Walk.edges_reverse, List.mem_reverse, Walk.edges_append,
        List.mem_append]
      rw [hedges] at hfc
      simp only [List.mem_append, List.mem_cons] at hfc
      rcases hfc with h1 | heq | h2
      · exact Or.inr h1
      · exact absurd heq hfne
      · exact Or.inl h2
  · 
    refine ⟨w₂.append w₁, ?_, ?_, ?_⟩
    · 
      rw [Walk.isPath_def]
      rw [hc_eq, Walk.support_append, Walk.support_cons, List.tail_append_of_ne_nil,
          List.tail_cons] at hnodup_tail
      · rw [Walk.support_append]
        rw [List.nodup_append] at hnodup_tail
        obtain ⟨hnd₁_tail, hnd₂, hdisj⟩ := hnodup_tail
        rw [List.nodup_append]
        refine ⟨hnd₂, hnd₁_tail, ?_⟩
        intro v hv₂ v' hv₁ heq
        subst heq
        exact hdisj v hv₁ v hv₂ rfl
      · exact w₁.support_ne_nil
    · simp only [Walk.edges_append, List.mem_append, not_or]
      rw [hedges, List.nodup_append] at hnodup
      obtain ⟨_, hcons, hdisj⟩ := hnodup
      simp only [List.nodup_cons] at hcons
      refine ⟨?_, ?_⟩
      · intro h
        exact hcons.1 (by rw [Sym2.eq_swap]; exact h)
      · intro h
        exact hdisj _ h _ (by simp [Sym2.eq_swap]) rfl
    · simp only [Walk.edges_append, List.mem_append]
      rw [hedges] at hfc
      simp only [List.mem_append, List.mem_cons] at hfc
      rcases hfc with h1 | heq | h2
      · exact Or.inr h1
      · rw [Sym2.eq_swap] at heq
        exact absurd heq hfne
      · exact Or.inl h2

omit [DecidableEq V] in










theorem Walk.spliceEdge_with_path
    {a b x : V}
    (c : (G ⊔ SimpleGraph.edge a b).Walk x x) (hc : c.IsTrail)
    (he : s(a, b) ∈ c.edges)
    (p : G.Walk a b) (hp_avoid : s(a, b) ∉ p.edges) :
    ∃ c' : G.Walk x x,
      ∀ e, e ∈ c'.edges ↔ (e ∈ c.edges ∧ e ≠ s(a, b)) ∨ e ∈ p.edges := by
  
  have hnodup : c.edges.Nodup := hc.edges_nodup
  
  have hab : (G ⊔ SimpleGraph.edge a b).Adj a b := c.adj_of_mem_edges he
  
  have hab_ne : a ≠ b := hab.ne
  
  
  have h_edge_in_G : ∀ e, e ∈ (G ⊔ SimpleGraph.edge a b).edgeSet → e ≠ s(a, b) →
      e ∈ G.edgeSet := by
    intro e he_sup he_ne
    rw [SimpleGraph.edgeSet_sup, Set.mem_union] at he_sup
    rcases he_sup with h_in_G | h_in_edge
    · exact h_in_G
    · 
      rw [SimpleGraph.edge_edgeSet_of_ne hab_ne] at h_in_edge
      simp at h_in_edge
      exact absurd h_in_edge he_ne
  
  rcases Walk.exists_split_at_edge (G := G ⊔ SimpleGraph.edge a b) hab c he with
    ⟨w₁, w₂, hc_eq, hedges⟩ | ⟨w₁, w₂, hc_eq, hedges⟩
  · 
    
    rw [hedges, List.nodup_append] at hnodup
    obtain ⟨hnd₁, hnd_cons, hdisj⟩ := hnodup
    simp only [List.nodup_cons, List.mem_cons] at hnd_cons
    obtain ⟨h_ab_notin_w₂, hnd₂⟩ := hnd_cons
    
    have h_ab_notin_w₁ : s(a, b) ∉ w₁.edges := by
      intro h
      exact hdisj _ h _ List.mem_cons_self rfl
    
    have hw₁_in_G : ∀ e ∈ w₁.edges, e ∈ G.edgeSet := by
      intro e he_w₁
      apply h_edge_in_G e (w₁.edges_subset_edgeSet he_w₁)
      intro h_eq; rw [h_eq] at he_w₁; exact h_ab_notin_w₁ he_w₁
    have hw₂_in_G : ∀ e ∈ w₂.edges, e ∈ G.edgeSet := by
      intro e he_w₂
      apply h_edge_in_G e (w₂.edges_subset_edgeSet he_w₂)
      intro h_eq; rw [h_eq] at he_w₂; exact h_ab_notin_w₂ he_w₂
    let w₁' : G.Walk x a := w₁.transfer G hw₁_in_G
    let w₂' : G.Walk b x := w₂.transfer G hw₂_in_G
    refine ⟨(w₁'.append p).append w₂', ?_⟩
    
    have hw₁'_edges : w₁'.edges = w₁.edges := w₁.edges_transfer hw₁_in_G
    have hw₂'_edges : w₂'.edges = w₂.edges := w₂.edges_transfer hw₂_in_G
    intro e
    simp only [Walk.edges_append, List.mem_append, hw₁'_edges, hw₂'_edges, hedges,
      List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · 
        refine Or.inl ⟨?_, ?_⟩
        · exact Or.inl h
        · intro h_eq; rw [h_eq] at h; exact h_ab_notin_w₁ h
      · exact Or.inr h
      · 
        refine Or.inl ⟨?_, ?_⟩
        · exact Or.inr (Or.inr h)
        · intro h_eq; rw [h_eq] at h; exact h_ab_notin_w₂ h
    · rintro (⟨h_in_c, h_ne⟩ | h_p)
      · rcases h_in_c with h_w₁ | h_eq | h_w₂
        · exact Or.inl (Or.inl h_w₁)
        · exact absurd h_eq h_ne
        · exact Or.inr h_w₂
      · exact Or.inl (Or.inr h_p)
  · 
    
    rw [hedges, List.nodup_append] at hnodup
    obtain ⟨hnd₁, hnd_cons, hdisj⟩ := hnodup
    simp only [List.nodup_cons, List.mem_cons] at hnd_cons
    obtain ⟨h_ba_notin_w₂, hnd₂⟩ := hnd_cons
    have h_ba_notin_w₁ : s(b, a) ∉ w₁.edges := by
      intro h
      exact hdisj _ h _ List.mem_cons_self rfl
    
    have h_ab_notin_w₁ : s(a, b) ∉ w₁.edges := by
      rw [Sym2.eq_swap]; exact h_ba_notin_w₁
    have h_ab_notin_w₂ : s(a, b) ∉ w₂.edges := by
      rw [Sym2.eq_swap]; exact h_ba_notin_w₂
    have hw₁_in_G : ∀ e ∈ w₁.edges, e ∈ G.edgeSet := by
      intro e he_w₁
      apply h_edge_in_G e (w₁.edges_subset_edgeSet he_w₁)
      intro h_eq; rw [h_eq] at he_w₁; exact h_ab_notin_w₁ he_w₁
    have hw₂_in_G : ∀ e ∈ w₂.edges, e ∈ G.edgeSet := by
      intro e he_w₂
      apply h_edge_in_G e (w₂.edges_subset_edgeSet he_w₂)
      intro h_eq; rw [h_eq] at he_w₂; exact h_ab_notin_w₂ he_w₂
    let w₁' : G.Walk x b := w₁.transfer G hw₁_in_G
    let w₂' : G.Walk a x := w₂.transfer G hw₂_in_G
    refine ⟨(w₁'.append p.reverse).append w₂', ?_⟩
    have hw₁'_edges : w₁'.edges = w₁.edges := w₁.edges_transfer hw₁_in_G
    have hw₂'_edges : w₂'.edges = w₂.edges := w₂.edges_transfer hw₂_in_G
    intro e
    simp only [Walk.edges_append, List.mem_append, hw₁'_edges, hw₂'_edges, hedges,
      List.mem_cons, Walk.edges_reverse, List.mem_reverse]
    constructor
    · rintro ((h | h) | h)
      · refine Or.inl ⟨?_, ?_⟩
        · exact Or.inl h
        · intro h_eq; rw [h_eq] at h; exact h_ab_notin_w₁ h
      · exact Or.inr h
      · refine Or.inl ⟨?_, ?_⟩
        · exact Or.inr (Or.inr h)
        · intro h_eq; rw [h_eq] at h; exact h_ab_notin_w₂ h
    · rintro (⟨h_in_c, h_ne⟩ | h_p)
      · rcases h_in_c with h_w₁ | h_eq | h_w₂
        · exact Or.inl (Or.inl h_w₁)
        · 
          exfalso; apply h_ne; rw [h_eq, Sym2.eq_swap]
        · exact Or.inr h_w₂
      · exact Or.inl (Or.inr h_p)




private lemma Walk.append_reverse_isTrail
    {a b : V} {p₁ p₂ : G.Walk a b} (hp₁ : p₁.IsTrail) (hp₂ : p₂.IsTrail)
    (hdisj : ∀ e ∈ p₁.edges, e ∉ p₂.edges) :
    (p₁.append p₂.reverse).IsTrail := by
  rw [Walk.isTrail_def, Walk.edges_append, Walk.edges_reverse, List.nodup_append]
  refine ⟨hp₁.edges_nodup, List.nodup_reverse.mpr hp₂.edges_nodup, ?_⟩
  intro e he1 e' he2 heq
  rw [List.mem_reverse] at he2
  rw [heq] at he1
  exact hdisj e' he1 he2











private theorem Walk.append_reverse_isCycle_of_disjoint
    {a b : V} {p₁ p₂ : G.Walk a b} (hp₁ : p₁.IsPath) (hp₂ : p₂.IsPath)
    (hne : a ≠ b)
    (hv_disj : ∀ v, v ∈ p₁.support → v ≠ a → v ≠ b → v ∉ p₂.support)
    (he_disj : ∀ e ∈ p₁.edges, e ∉ p₂.edges) :
    (p₁.append p₂.reverse).IsCycle := by
  have hw_trail : (p₁.append p₂.reverse).IsTrail :=
    Walk.append_reverse_isTrail G hp₁.isTrail hp₂.isTrail he_disj
  have hw_ne_nil : p₁.append p₂.reverse ≠ Walk.nil := by
    intro h
    have hlen := congr_arg Walk.length h
    simp [Walk.length_append, Walk.length_reverse, Walk.length_nil] at hlen
    have : p₁.length = 0 := by omega
    exact hne (Walk.eq_of_length_eq_zero this)
  rw [Walk.isCycle_def]
  refine ⟨hw_trail, hw_ne_nil, ?_⟩
  rw [Walk.support_append, List.tail_append_of_ne_nil p₁.support_ne_nil]
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact List.Nodup.sublist (List.tail_sublist _) hp₁.support_nodup
  · rw [Walk.support_reverse]
    exact List.Nodup.sublist (List.tail_sublist _) (List.nodup_reverse.mpr hp₂.support_nodup)
  · intro z hz₁ z' hz₂ heq
    subst heq
    have hz_in_p₁ : z ∈ p₁.support := List.mem_of_mem_tail hz₁
    have hz_in_p₂_rev : z ∈ p₂.reverse.support := List.mem_of_mem_tail hz₂
    have hz_in_p₂ : z ∈ p₂.support := by
      rw [Walk.support_reverse] at hz_in_p₂_rev
      exact List.mem_reverse.mp hz_in_p₂_rev
    have hz_ne_a : z ≠ a := by
      intro heq
      subst heq
      have h_count : p₁.support.count z = 1 :=
        List.count_eq_one_of_mem hp₁.support_nodup hz_in_p₁
      have h_in_tail : z ∈ p₁.support.tail := hz₁
      have h_in_head : p₁.support.head p₁.support_ne_nil = z := p₁.head_support
      have hsup : p₁.support = z :: p₁.support.tail := by
        conv_lhs => rw [← List.cons_head_tail p₁.support_ne_nil]
        rw [h_in_head]
      rw [hsup, List.count_cons_self] at h_count
      have : p₁.support.tail.count z = 0 := by omega
      exact absurd h_in_tail (List.count_eq_zero.mp this)
    have hz_ne_b : z ≠ b := by
      intro heq
      subst heq
      have hp₂rev_nodup : p₂.reverse.support.Nodup := by
        rw [Walk.support_reverse]
        exact List.nodup_reverse.mpr hp₂.support_nodup
      have h_count : p₂.reverse.support.count z = 1 :=
        List.count_eq_one_of_mem hp₂rev_nodup hz_in_p₂_rev
      have h_in_head : p₂.reverse.support.head p₂.reverse.support_ne_nil = z :=
        p₂.reverse.head_support
      have hsup : p₂.reverse.support = z :: p₂.reverse.support.tail := by
        conv_lhs => rw [← List.cons_head_tail p₂.reverse.support_ne_nil]
        rw [h_in_head]
      rw [hsup, List.count_cons_self] at h_count
      have : p₂.reverse.support.tail.count z = 0 := by omega
      exact absurd hz₂ (List.count_eq_zero.mp this)
    exact hv_disj z hz_in_p₁ hz_ne_a hz_ne_b hz_in_p₂

















theorem Walk.spliceEdge_isCycle_extract
    {a b x : V}
    (c : (G ⊔ SimpleGraph.edge a b).Walk x x) (hc : c.IsCycle)
    (he_ab : s(a, b) ∈ c.edges)
    {e₁ e₃ : Sym2 V} (he₁ : e₁ ∈ c.edges) (he₃ : e₃ ∈ c.edges)
    (he₁_ne : e₁ ≠ s(a, b)) (he₃_ne : e₃ ≠ s(a, b)) (hne : e₁ ≠ e₃)
    (p : G.Walk a b) (hp_path : p.IsPath) (hp_avoid : s(a, b) ∉ p.edges)
    (hp_internal : ∀ v ∈ p.support, v ≠ a → v ≠ b → v ∉ c.support) :
    ∃ (v : V) (c' : G.Walk v v), c'.IsCycle ∧ e₁ ∈ c'.edges ∧ e₃ ∈ c'.edges := by
  have hab : (G ⊔ SimpleGraph.edge a b).Adj a b := c.adj_of_mem_edges he_ab
  have hab_ne : a ≠ b := hab.ne
  have h_edge_in_G : ∀ e, e ∈ (G ⊔ SimpleGraph.edge a b).edgeSet → e ≠ s(a, b) →
      e ∈ G.edgeSet := by
    intro e he_sup he_ne
    rw [SimpleGraph.edgeSet_sup, Set.mem_union] at he_sup
    rcases he_sup with h_in_G | h_in_edge
    · exact h_in_G
    · rw [SimpleGraph.edge_edgeSet_of_ne hab_ne] at h_in_edge
      simp at h_in_edge
      exact absurd h_in_edge he_ne
  have htrail : c.IsTrail := hc.isTrail
  have hnodup_edges : c.edges.Nodup := htrail.edges_nodup
  have hnodup_supp : c.support.tail.Nodup := hc.support_nodup
  rcases Walk.exists_split_at_edge (G := G ⊔ SimpleGraph.edge a b) hab c he_ab with
    ⟨w₁, w₂, hc_eq, hedges⟩ | ⟨w₁, w₂, hc_eq, hedges⟩
  · 
    rw [hedges, List.nodup_append] at hnodup_edges
    obtain ⟨hnd₁_e, hnd_cons_e, hdisj_e⟩ := hnodup_edges
    simp only [List.nodup_cons, List.mem_cons] at hnd_cons_e
    obtain ⟨h_ab_notin_w₂, hnd₂_e⟩ := hnd_cons_e
    have h_ab_notin_w₁ : s(a, b) ∉ w₁.edges := by
      intro h
      exact hdisj_e _ h _ List.mem_cons_self rfl
    have hw₁_in_G : ∀ e ∈ w₁.edges, e ∈ G.edgeSet := by
      intro e he_w₁
      apply h_edge_in_G e (w₁.edges_subset_edgeSet he_w₁)
      intro h_eq; rw [h_eq] at he_w₁; exact h_ab_notin_w₁ he_w₁
    have hw₂_in_G : ∀ e ∈ w₂.edges, e ∈ G.edgeSet := by
      intro e he_w₂
      apply h_edge_in_G e (w₂.edges_subset_edgeSet he_w₂)
      intro h_eq; rw [h_eq] at he_w₂; exact h_ab_notin_w₂ he_w₂
    let w₁' : G.Walk x a := w₁.transfer G hw₁_in_G
    let w₂' : G.Walk b x := w₂.transfer G hw₂_in_G
    have hw₁'_edges : w₁'.edges = w₁.edges := w₁.edges_transfer hw₁_in_G
    have hw₂'_edges : w₂'.edges = w₂.edges := w₂.edges_transfer hw₂_in_G
    have hw₁'_support : w₁'.support = w₁.support := w₁.support_transfer hw₁_in_G
    have hw₂'_support : w₂'.support = w₂.support := w₂.support_transfer hw₂_in_G
    
    let q : G.Walk a b := (w₂'.append w₁').reverse
    
    have hc_supp : c.support = w₁.support ++ w₂.support := by
      rw [hc_eq, Walk.support_append, Walk.support_cons]
      simp [List.tail_cons]
    
    have hsupp_tail_eq : c.support.tail = w₁.support.tail ++ w₂.support := by
      rw [hc_supp, List.tail_append_of_ne_nil w₁.support_ne_nil]
    
    have hq_path : q.IsPath := by
      rw [show q = (w₂'.append w₁').reverse from rfl, Walk.isPath_reverse_iff,
          Walk.isPath_def, Walk.support_append, hw₁'_support, hw₂'_support]
      rw [hsupp_tail_eq, List.nodup_append] at hnodup_supp
      obtain ⟨hnd₁_tail, hnd₂_supp, hdisj_supp⟩ := hnodup_supp
      rw [List.nodup_append]
      refine ⟨hnd₂_supp, hnd₁_tail, ?_⟩
      intro v hv₂ v' hv₁ heq
      subst heq
      exact hdisj_supp v hv₁ v hv₂ rfl
    
    have hq_edges_set : ∀ e, e ∈ q.edges ↔ e ∈ w₁.edges ∨ e ∈ w₂.edges := by
      intro e
      simp only [q, Walk.edges_reverse, List.mem_reverse, Walk.edges_append,
        List.mem_append, hw₁'_edges, hw₂'_edges]
      tauto
    
    have h_ab_notin_q : s(a, b) ∉ q.edges := by
      intro h
      rcases (hq_edges_set _).mp h with h₁ | h₂
      · exact h_ab_notin_w₁ h₁
      · exact h_ab_notin_w₂ h₂
    
    have he₁_in_q : e₁ ∈ q.edges := by
      rw [hedges] at he₁
      simp only [List.mem_append, List.mem_cons] at he₁
      rcases he₁ with h | h | h
      · exact (hq_edges_set _).mpr (Or.inl h)
      · exact absurd h he₁_ne
      · exact (hq_edges_set _).mpr (Or.inr h)
    have he₃_in_q : e₃ ∈ q.edges := by
      rw [hedges] at he₃
      simp only [List.mem_append, List.mem_cons] at he₃
      rcases he₃ with h | h | h
      · exact (hq_edges_set _).mpr (Or.inl h)
      · exact absurd h he₃_ne
      · exact (hq_edges_set _).mpr (Or.inr h)
    
    have hq_supp_sub : ∀ v, v ∈ q.support → v ∈ c.support := by
      intro v hv
      simp only [q, Walk.support_reverse, List.mem_reverse,
        Walk.support_append, hw₁'_support, hw₂'_support, List.mem_append] at hv
      rw [hc_supp, List.mem_append]
      rcases hv with h | h
      · exact Or.inr h
      · 
        exact Or.inl (List.mem_of_mem_tail h)
    
    have hv_disj : ∀ v, v ∈ q.support → v ≠ a → v ≠ b → v ∉ p.support := by
      intro v hv hva hvb hvp
      exact hp_internal v hvp hva hvb (hq_supp_sub v hv)
    
    have he_disj : ∀ e ∈ q.edges, e ∉ p.edges := by
      intro e heq hep
      
      obtain ⟨u₁, u₂⟩ := e
      have hu₁_p : u₁ ∈ p.support := p.fst_mem_support_of_mem_edges hep
      have hu₂_p : u₂ ∈ p.support := p.snd_mem_support_of_mem_edges hep
      have hu₁_q : u₁ ∈ q.support := q.fst_mem_support_of_mem_edges heq
      have hu₂_q : u₂ ∈ q.support := q.snd_mem_support_of_mem_edges heq
      have hu₁_c : u₁ ∈ c.support := hq_supp_sub _ hu₁_q
      have hu₂_c : u₂ ∈ c.support := hq_supp_sub _ hu₂_q
      
      have hu₁_ab : u₁ = a ∨ u₁ = b := by
        by_contra hcontr
        push_neg at hcontr
        exact hp_internal u₁ hu₁_p hcontr.1 hcontr.2 hu₁_c
      have hu₂_ab : u₂ = a ∨ u₂ = b := by
        by_contra hcontr
        push_neg at hcontr
        exact hp_internal u₂ hu₂_p hcontr.1 hcontr.2 hu₂_c
      
      have huv_adj : G.Adj u₁ u₂ := p.adj_of_mem_edges hep
      have huv_ne : u₁ ≠ u₂ := huv_adj.ne
      have h_e_eq_ab : s(u₁, u₂) = s(a, b) := by
        rcases hu₁_ab with rfl | rfl <;> rcases hu₂_ab with rfl | rfl
        · exact absurd rfl huv_ne
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl huv_ne
      exact hp_avoid (h_e_eq_ab ▸ hep)
    
    have hcycle : (q.append p.reverse).IsCycle := by
      have := Walk.append_reverse_isCycle_of_disjoint
        (G := G) (p₁ := q) (p₂ := p) hq_path hp_path hab_ne hv_disj he_disj
      exact this
    refine ⟨a, q.append p.reverse, hcycle, ?_, ?_⟩
    · simp only [Walk.edges_append, List.mem_append]
      exact Or.inl he₁_in_q
    · simp only [Walk.edges_append, List.mem_append]
      exact Or.inl he₃_in_q
  · 
    rw [hedges, List.nodup_append] at hnodup_edges
    obtain ⟨hnd₁_e, hnd_cons_e, hdisj_e⟩ := hnodup_edges
    simp only [List.nodup_cons, List.mem_cons] at hnd_cons_e
    obtain ⟨h_ba_notin_w₂, hnd₂_e⟩ := hnd_cons_e
    have h_ba_notin_w₁ : s(b, a) ∉ w₁.edges := by
      intro h
      exact hdisj_e _ h _ List.mem_cons_self rfl
    have h_ab_notin_w₁ : s(a, b) ∉ w₁.edges := by
      rw [Sym2.eq_swap]; exact h_ba_notin_w₁
    have h_ab_notin_w₂ : s(a, b) ∉ w₂.edges := by
      rw [Sym2.eq_swap]; exact h_ba_notin_w₂
    have hw₁_in_G : ∀ e ∈ w₁.edges, e ∈ G.edgeSet := by
      intro e he_w₁
      apply h_edge_in_G e (w₁.edges_subset_edgeSet he_w₁)
      intro h_eq; rw [h_eq] at he_w₁; exact h_ab_notin_w₁ he_w₁
    have hw₂_in_G : ∀ e ∈ w₂.edges, e ∈ G.edgeSet := by
      intro e he_w₂
      apply h_edge_in_G e (w₂.edges_subset_edgeSet he_w₂)
      intro h_eq; rw [h_eq] at he_w₂; exact h_ab_notin_w₂ he_w₂
    let w₁' : G.Walk x b := w₁.transfer G hw₁_in_G
    let w₂' : G.Walk a x := w₂.transfer G hw₂_in_G
    have hw₁'_edges : w₁'.edges = w₁.edges := w₁.edges_transfer hw₁_in_G
    have hw₂'_edges : w₂'.edges = w₂.edges := w₂.edges_transfer hw₂_in_G
    have hw₁'_support : w₁'.support = w₁.support := w₁.support_transfer hw₁_in_G
    have hw₂'_support : w₂'.support = w₂.support := w₂.support_transfer hw₂_in_G
    
    let q : G.Walk a b := w₂'.append w₁'
    have hc_supp : c.support = w₁.support ++ w₂.support := by
      rw [hc_eq, Walk.support_append, Walk.support_cons]
      simp [List.tail_cons]
    have hsupp_tail_eq : c.support.tail = w₁.support.tail ++ w₂.support := by
      rw [hc_supp, List.tail_append_of_ne_nil w₁.support_ne_nil]
    have hq_path : q.IsPath := by
      rw [show q = w₂'.append w₁' from rfl, Walk.isPath_def, Walk.support_append,
          hw₁'_support, hw₂'_support]
      rw [hsupp_tail_eq, List.nodup_append] at hnodup_supp
      obtain ⟨hnd₁_tail, hnd₂_supp, hdisj_supp⟩ := hnodup_supp
      rw [List.nodup_append]
      refine ⟨hnd₂_supp, hnd₁_tail, ?_⟩
      intro v hv₂ v' hv₁ heq
      subst heq
      exact hdisj_supp v hv₁ v hv₂ rfl
    have hq_edges_set : ∀ e, e ∈ q.edges ↔ e ∈ w₁.edges ∨ e ∈ w₂.edges := by
      intro e
      simp only [q, Walk.edges_append, List.mem_append, hw₁'_edges, hw₂'_edges]
      tauto
    have he₁_in_q : e₁ ∈ q.edges := by
      rw [hedges] at he₁
      simp only [List.mem_append, List.mem_cons] at he₁
      rcases he₁ with h | h | h
      · exact (hq_edges_set _).mpr (Or.inl h)
      · 
        exfalso; apply he₁_ne; rw [h, Sym2.eq_swap]
      · exact (hq_edges_set _).mpr (Or.inr h)
    have he₃_in_q : e₃ ∈ q.edges := by
      rw [hedges] at he₃
      simp only [List.mem_append, List.mem_cons] at he₃
      rcases he₃ with h | h | h
      · exact (hq_edges_set _).mpr (Or.inl h)
      · exfalso; apply he₃_ne; rw [h, Sym2.eq_swap]
      · exact (hq_edges_set _).mpr (Or.inr h)
    have hq_supp_sub : ∀ v, v ∈ q.support → v ∈ c.support := by
      intro v hv
      simp only [q, Walk.support_append, hw₁'_support, hw₂'_support,
        List.mem_append] at hv
      rw [hc_supp, List.mem_append]
      rcases hv with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_of_mem_tail h)
    have hv_disj : ∀ v, v ∈ q.support → v ≠ a → v ≠ b → v ∉ p.support := by
      intro v hv hva hvb hvp
      exact hp_internal v hvp hva hvb (hq_supp_sub v hv)
    have he_disj : ∀ e ∈ q.edges, e ∉ p.edges := by
      intro e heq hep
      obtain ⟨u₁, u₂⟩ := e
      have hu₁_p : u₁ ∈ p.support := p.fst_mem_support_of_mem_edges hep
      have hu₂_p : u₂ ∈ p.support := p.snd_mem_support_of_mem_edges hep
      have hu₁_q : u₁ ∈ q.support := q.fst_mem_support_of_mem_edges heq
      have hu₂_q : u₂ ∈ q.support := q.snd_mem_support_of_mem_edges heq
      have hu₁_c : u₁ ∈ c.support := hq_supp_sub _ hu₁_q
      have hu₂_c : u₂ ∈ c.support := hq_supp_sub _ hu₂_q
      have hu₁_ab : u₁ = a ∨ u₁ = b := by
        by_contra hcontr
        push_neg at hcontr
        exact hp_internal u₁ hu₁_p hcontr.1 hcontr.2 hu₁_c
      have hu₂_ab : u₂ = a ∨ u₂ = b := by
        by_contra hcontr
        push_neg at hcontr
        exact hp_internal u₂ hu₂_p hcontr.1 hcontr.2 hu₂_c
      have huv_adj : G.Adj u₁ u₂ := p.adj_of_mem_edges hep
      have huv_ne : u₁ ≠ u₂ := huv_adj.ne
      have h_e_eq_ab : s(u₁, u₂) = s(a, b) := by
        rcases hu₁_ab with rfl | rfl <;> rcases hu₂_ab with rfl | rfl
        · exact absurd rfl huv_ne
        · rfl
        · exact Sym2.eq_swap
        · exact absurd rfl huv_ne
      exact hp_avoid (h_e_eq_ab ▸ hep)
    have hcycle : (q.append p.reverse).IsCycle :=
      Walk.append_reverse_isCycle_of_disjoint
        (G := G) (p₁ := q) (p₂ := p) hq_path hp_path hab_ne hv_disj he_disj
    refine ⟨a, q.append p.reverse, hcycle, ?_, ?_⟩
    · simp only [Walk.edges_append, List.mem_append]
      exact Or.inl he₁_in_q
    · simp only [Walk.edges_append, List.mem_append]
      exact Or.inl he₃_in_q















omit [DecidableEq V] in


private lemma Walk.length_ge_three_of_two_edges {u : V}
    {w : G.Walk u u} {e₁ e₂ : Sym2 V}
    (h1 : e₁ ∈ w.edges) (h2 : e₂ ∈ w.edges) (hne : e₁ ≠ e₂) :
    3 ≤ w.length := by
  
  have hge2 : 2 ≤ w.length := by
    by_contra hlt
    push Not at hlt
    interval_cases hwl : w.length
    · 
      rw [Walk.length_eq_zero_iff.mp hwl] at h1
      simp [Walk.edges] at h1
    · 
      have hlen : w.edges.length = 1 := by rw [Walk.length_edges]; exact hwl
      rcases List.length_eq_one_iff.mp hlen with ⟨a, ha⟩
      rw [ha] at h1 h2
      simp at h1 h2
      exact hne (h1.trans h2.symm)
  
  rcases hge2.lt_or_eq with hgt | heq
  · omega
  · exfalso
    
    have heq2 : w.length = 2 := heq.symm
    match w, heq2 with
    | .cons (v := v) h0 (.cons h0' .nil), _ =>
      simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons,
        List.not_mem_nil, or_false] at h1 h2
      
      have hab : s(u, v) = s(v, u) := Sym2.eq_swap
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> (
        apply hne
        rw [h1, h2]
        try exact hab
        try exact hab.symm)

omit [DecidableEq V] in


private lemma Walk.not_isCycle_iff_of_ne_nil {u : V} {w : G.Walk u u} (hwne : w ≠ .nil) :
    ¬ w.IsCycle ↔ ¬ w.IsTrail ∨ ¬ w.support.tail.Nodup := by
  rw [isCycle_def]
  constructor
  · intro h
    by_cases htrail : w.IsTrail
    · refine Or.inr ?_
      intro hnodup
      exact h ⟨htrail, hwne, hnodup⟩
    · exact Or.inl htrail
  · rintro (h | h) ⟨htrail, _, hnodup⟩
    · exact h htrail
    · exact h hnodup

omit [DecidableEq V] in




private lemma Walk.isPath_length_eq_one_of_mem_edges_start_end
    {u v : V} (w : G.Walk v u) (hpath : w.IsPath) (he : s(u, v) ∈ w.edges) :
    w.length = 1 := by
  match w, hpath, he with
  | .nil, _, he => simp [Walk.edges] at he
  | .cons (v := mid) h0 p, hpath, he =>
    
    
    simp only [Walk.edges_cons, List.mem_cons] at he
    rcases he with heq | hin
    · 
      rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · 
        subst h1; subst h2
        exact absurd h0 (SimpleGraph.irrefl _)
      · 
        
        subst h1
        have hp_path : p.IsPath := hpath.of_cons
        have hp_nil : p = Walk.nil := (Walk.isPath_iff_eq_nil p).mp hp_path
        rw [hp_nil]; simp [Walk.length_cons, Walk.length_nil]
    · 
      exfalso
      have hv_in : v ∈ p.support := p.snd_mem_support_of_mem_edges hin
      rw [Walk.cons_isPath_iff] at hpath
      exact hpath.2 hv_in


























private lemma Walk.exists_internal_repeat
    {u : V} (w : G.Walk u u) (hlen : 3 ≤ w.length) (hcyc : ¬ w.IsCycle) :
    ∃ (x : V) (w₁ w₂ : G.Walk x x),
      w₁.length + w₂.length = w.length ∧
      List.Perm (w₁.edges ++ w₂.edges) w.edges ∧
      0 < w₁.length ∧ 0 < w₂.length := by
  
  match w, hlen, hcyc with
  | .nil, hlen, _ => simp at hlen
  | .cons (v := mid) h0 w', hlen, hcyc =>
    
    have hw'_len : 2 ≤ w'.length := by
      simp [Walk.length_cons] at hlen
      omega
    
    have hw'_not_path : ¬ w'.IsPath := by
      intro hpath
      
      have : s(u, mid) ∈ w'.edges := by
        rw [Walk.cons_isCycle_iff w' h0] at hcyc
        push Not at hcyc
        exact hcyc hpath
      
      have : w'.length = 1 :=
        Walk.isPath_length_eq_one_of_mem_edges_start_end G w' hpath this
      omega
    
    have hw'_not_nodup : ¬ w'.support.Nodup := by
      intro h
      exact hw'_not_path (Walk.IsPath.mk' h)
    
    obtain ⟨x, hx_dup⟩ := List.exists_duplicate_iff_not_nodup.mpr hw'_not_nodup
    have hx_count_w' : 2 ≤ w'.support.count x := by
      rw [← List.duplicate_iff_two_le_count]
      exact hx_dup
    have hx_mem_w' : x ∈ w'.support := hx_dup.mem
    
    have hx_mem_w : x ∈ (Walk.cons h0 w').support := by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hx_mem_w'
    
    set w_full : G.Walk u u := Walk.cons h0 w' with hw_full
    have hx_count_w_full_tail : 2 ≤ w_full.support.tail.count x := by
      rw [hw_full, Walk.support_cons, List.tail_cons]
      exact hx_count_w'
    set w_rot : G.Walk x x := w_full.rotate x hx_mem_w with hw_rot
    
    have hrot_edges_perm : List.Perm w_rot.edges w_full.edges :=
      (Walk.rotate_edges w_full x hx_mem_w).perm
    
    have hrot_len : w_rot.length = w_full.length := by
      have h1 := w_rot.length_edges
      have h2 := w_full.length_edges
      have h3 := hrot_edges_perm.length_eq
      omega
    
    have hx_count_rot_tail : 2 ≤ w_rot.support.tail.count x := by
      have := Walk.support_rotate w_full x hx_mem_w
      
      have hperm := this.perm
      rw [hperm.count_eq x]
      exact hx_count_w_full_tail
    
    have hrot_ne_nil : w_rot ≠ Walk.nil := by
      intro hn
      have hl : w_rot.length = 0 := by rw [hn]; rfl
      rw [hrot_len, hw_full, Walk.length_cons] at hl
      omega
    
    match hw_rot_eq : w_rot, hrot_ne_nil, hrot_len, hrot_edges_perm, hx_count_rot_tail with
    | .cons (v := x') h0' w_rot_tail', _, hrot_len, hrot_edges_perm, hx_count_rot_tail =>
      
      
      have hx_mem_tail : x ∈ w_rot_tail'.support := by
        
        have : x ∈ (Walk.cons h0' w_rot_tail').support.tail := by
          have h := hx_count_rot_tail
          rw [Walk.support_cons, List.tail_cons] at h
          
          exact List.count_pos_iff.mp (by omega)
        rw [Walk.support_cons, List.tail_cons] at this
        exact this
      
      set w₁ : G.Walk x x := .cons h0' (w_rot_tail'.takeUntil x hx_mem_tail) with hw₁_def
      set w₂ : G.Walk x x := w_rot_tail'.dropUntil x hx_mem_tail with hw₂_def
      
      have htake_dropeq : (w_rot_tail'.takeUntil x hx_mem_tail).length
          + (w_rot_tail'.dropUntil x hx_mem_tail).length = w_rot_tail'.length := by
        have := w_rot_tail'.take_spec hx_mem_tail
        have := congr_arg Walk.length this
        rw [Walk.length_append] at this
        omega
      have hlen_sum : w₁.length + w₂.length = w_full.length := by
        rw [hw₁_def, hw₂_def, Walk.length_cons]
        have hrot_eq_len : w_rot_tail'.length + 1 = w_rot.length := by
          rw [show w_rot = Walk.cons h0' w_rot_tail' from hw_rot_eq, Walk.length_cons]
        omega
      
      have hedges_perm : List.Perm (w₁.edges ++ w₂.edges) w_full.edges := by
        
        
        
        
        
        have hspec : (w_rot_tail'.takeUntil x hx_mem_tail).edges ++
            (w_rot_tail'.dropUntil x hx_mem_tail).edges = w_rot_tail'.edges := by
          have := w_rot_tail'.take_spec hx_mem_tail
          have := congr_arg Walk.edges this
          rw [Walk.edges_append] at this
          exact this
        have hconcat : w₁.edges ++ w₂.edges = (Walk.cons h0' w_rot_tail').edges := by
          rw [hw₁_def, hw₂_def, Walk.edges_cons]
          rw [List.cons_append, hspec]
          rw [Walk.edges_cons]
        rw [hconcat]
        exact hrot_edges_perm
      
      have hw₁_pos : 0 < w₁.length := by
        rw [hw₁_def, Walk.length_cons]
        omega
      have hw₂_pos : 0 < w₂.length := by
        rw [hw₂_def]
        
        
        by_contra h_zero
        push Not at h_zero
        have hdrop_len_zero : (w_rot_tail'.dropUntil x hx_mem_tail).length = 0 := by omega
        have hdrop_nil : w_rot_tail'.dropUntil x hx_mem_tail = Walk.nil :=
          Walk.length_eq_zero_iff.mp hdrop_len_zero
        have htake_eq_full :
            (w_rot_tail'.takeUntil x hx_mem_tail).support = w_rot_tail'.support := by
          have hspec := w_rot_tail'.take_spec hx_mem_tail
          rw [hdrop_nil, Walk.append_nil] at hspec
          rw [hspec]
        have hcount_one : w_rot_tail'.support.count x = 1 := by
          rw [← htake_eq_full]
          exact Walk.count_support_takeUntil_eq_one _ hx_mem_tail
        have h2 : 2 ≤ w_rot_tail'.support.count x := by
          have h := hx_count_rot_tail
          rw [Walk.support_cons, List.tail_cons] at h
          exact h
        omega
      exact ⟨x, w₁, w₂, hlen_sum, hedges_perm, hw₁_pos, hw₂_pos⟩






































private theorem Walk.exists_isCycle_through_edge_in_trail
    {u : V} (w : G.Walk u u) (hw_trail : w.IsTrail)
    {f : Sym2 V} (hf : f ∈ w.edges) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ f ∈ c.edges := by
  obtain ⟨a, b⟩ := f
  have hab : G.Adj a b := w.adj_of_mem_edges hf
  
  have hnodup : w.edges.Nodup := hw_trail.edges_nodup
  
  rcases Walk.exists_split_at_edge G hab w hf with
    ⟨w₁, w₂, _, hedges⟩ | ⟨w₁, w₂, _, hedges⟩
  · 
    rw [hedges, List.nodup_append] at hnodup
    obtain ⟨_, hcons_nodup, hdisj⟩ := hnodup
    simp only [List.nodup_cons] at hcons_nodup
    
    have h_notin_w₂ : s(a, b) ∉ w₂.edges := hcons_nodup.1
    have h_notin_w₁ : s(a, b) ∉ w₁.edges := by
      intro h
      exact hdisj _ h _ (by simp) rfl
    
    have h_reach : (G \ fromEdgeSet {s(a, b)}).Reachable a b := by
      rw [SimpleGraph.reachable_delete_edges_iff_exists_walk]
      refine ⟨(w₂.append w₁).reverse, ?_⟩
      simp only [Walk.edges_reverse, List.mem_reverse, Walk.edges_append,
        List.mem_append, not_or]
      exact ⟨h_notin_w₂, h_notin_w₁⟩
    obtain ⟨v, c, hc, hec⟩ :=
      (adj_and_reachable_delete_edges_iff_exists_cycle (G := G) (v := a) (w := b)).mp
        ⟨hab, h_reach⟩
    exact ⟨v, c, hc, hec⟩
  · 
    rw [hedges, List.nodup_append] at hnodup
    obtain ⟨_, hcons_nodup, hdisj⟩ := hnodup
    simp only [List.nodup_cons] at hcons_nodup
    have h_notin_w₂ : s(b, a) ∉ w₂.edges := hcons_nodup.1
    have h_notin_w₁ : s(b, a) ∉ w₁.edges := by
      intro h
      exact hdisj _ h _ (by simp) rfl
    
    have h_reach : (G \ fromEdgeSet {s(a, b)}).Reachable a b := by
      rw [SimpleGraph.reachable_delete_edges_iff_exists_walk]
      refine ⟨w₂.append w₁, ?_⟩
      simp only [Walk.edges_append, List.mem_append, not_or]
      rw [Sym2.eq_swap] 
      exact ⟨h_notin_w₂, h_notin_w₁⟩
    obtain ⟨v, c, hc, hec⟩ :=
      (adj_and_reachable_delete_edges_iff_exists_cycle (G := G) (v := a) (w := b)).mp
        ⟨hab, h_reach⟩
    exact ⟨v, c, hc, hec⟩












noncomputable def unionSupportFinset
    {a b : V} (w₁ w₂ : G.Walk a b) : Finset V :=
  w₁.support.toFinset ∪ w₂.support.toFinset


private lemma mem_unionSupportFinset_start
    {a b : V} (w₁ w₂ : G.Walk a b) :
    a ∈ G.unionSupportFinset w₁ w₂ := by
  simp [unionSupportFinset, w₁.start_mem_support]


private lemma mem_unionSupportFinset_end
    {a b : V} (w₁ w₂ : G.Walk a b) :
    b ∈ G.unionSupportFinset w₁ w₂ := by
  simp [unionSupportFinset, w₁.end_mem_support]


private lemma mem_unionSupportFinset_of_mem_left
    {a b : V} (w₁ w₂ : G.Walk a b) {v : V} (h : v ∈ w₁.support) :
    v ∈ G.unionSupportFinset w₁ w₂ := by
  simp [unionSupportFinset, h]

private lemma mem_unionSupportFinset_of_mem_right
    {a b : V} (w₁ w₂ : G.Walk a b) {v : V} (h : v ∈ w₂.support) :
    v ∈ G.unionSupportFinset w₁ w₂ := by
  simp [unionSupportFinset, h]




private noncomputable def Walk.toInduced
    {a b : V} (w : G.Walk a b) (s : Set V)
    (hsub : ∀ x ∈ w.support, x ∈ s)
    (ha : a ∈ s) (hb : b ∈ s) :
    (G.induce s).Walk ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction w with
  | nil =>
      exact Walk.nil
  | cons hadj w' ih =>
      rename_i u v w
      
      
      have hv_in : v ∈ s := hsub v (by simp)
      have hw_sub : ∀ x ∈ w'.support, x ∈ s := by
        intro x hx
        exact hsub x (by simp [hx])
      have ha_in : u ∈ s := ha
      have hb_in : w ∈ s := hb
      have hadj_ind : (G.induce s).Adj ⟨u, ha_in⟩ ⟨v, hv_in⟩ := by
        rw [induce_adj]; exact hadj
      exact Walk.cons hadj_ind (ih hw_sub hv_in hb_in)








private theorem induce_unionSupport_connected
    {a b : V} (w₁ w₂ : G.Walk a b) :
    (G.induce (↑(G.unionSupportFinset w₁ w₂) : Set V)).Connected := by
  set s : Set V := (↑(G.unionSupportFinset w₁ w₂) : Set V) with hs_def
  
  have hv_char : ∀ v : V, v ∈ s ↔ v ∈ w₁.support ∨ v ∈ w₂.support := by
    intro v
    simp [hs_def, unionSupportFinset]
  have ha_mem : a ∈ s := by
    rw [hv_char]; exact Or.inl w₁.start_mem_support
  rw [connected_iff]
  refine ⟨?_, ⟨⟨a, ha_mem⟩⟩⟩
  intro ⟨u, hu_mem⟩ ⟨v, hv_mem⟩
  
  suffices h : ∀ w : V, ∀ hw : w ∈ s,
      (G.induce s).Reachable ⟨a, ha_mem⟩ ⟨w, hw⟩ by
    exact (h u hu_mem).symm.trans (h v hv_mem)
  intro w hw_mem
  have hw_orig := hw_mem
  rw [hv_char] at hw_mem
  rcases hw_mem with hw₁ | hw₂
  · 
    have hsub : ∀ x ∈ (w₁.takeUntil w hw₁).support, x ∈ s := by
      intro x hx
      have : x ∈ w₁.support := w₁.support_takeUntil_subset hw₁ hx
      rw [hv_char]; exact Or.inl this
    exact ⟨(w₁.takeUntil w hw₁).toInduced G s hsub ha_mem hw_orig⟩
  · have hsub : ∀ x ∈ (w₂.takeUntil w hw₂).support, x ∈ s := by
      intro x hx
      have : x ∈ w₂.support := w₂.support_takeUntil_subset hw₂ hx
      rw [hv_char]; exact Or.inr this
    exact ⟨(w₂.takeUntil w hw₂).toInduced G s hsub ha_mem hw_orig⟩








private lemma Walk.IsPath.start_notMem_support_dropUntil
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) {y : V}
    (hy : y ∈ p.support) (hya : y ≠ a) :
    a ∉ (p.dropUntil y hy).support := by
  intro ha_drop
  
  have hsup_eq : p.support =
      (p.takeUntil y hy).support ++ (p.dropUntil y hy).support.tail := by
    conv_lhs => rw [← p.take_spec hy]
    rw [Walk.support_append]
  have hNodup : p.support.Nodup := hp.support_nodup
  
  have ha_take : a ∈ (p.takeUntil y hy).support := (p.takeUntil y hy).start_mem_support
  
  have hdrop_head : (p.dropUntil y hy).support.head
      (p.dropUntil y hy).support_ne_nil = y := (p.dropUntil y hy).head_support
  
  have hdrop_cons : (p.dropUntil y hy).support =
      y :: (p.dropUntil y hy).support.tail := by
    conv_lhs => rw [← List.cons_head_tail (p.dropUntil y hy).support_ne_nil]
    rw [hdrop_head]
  
  rw [hdrop_cons] at ha_drop
  rcases List.mem_cons.mp ha_drop with ha_eq | ha_tail
  · exact hya ha_eq.symm
  · 
    rw [hsup_eq] at hNodup
    have hdisj := List.disjoint_of_nodup_append hNodup
    exact hdisj ha_take ha_tail





private lemma Walk.IsPath.end_notMem_support_takeUntil
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) {y : V}
    (hy : y ∈ p.support) (hyb : y ≠ b) :
    b ∉ (p.takeUntil y hy).support :=
  Walk.endpoint_notMem_support_takeUntil hp hy (Ne.symm hyb)





private lemma Walk.IsPath.mem_takeUntil_or_dropUntil_of_ne
    {a b : V} {p : G.Walk a b} (hp : p.IsPath) {y v : V}
    (hy : y ∈ p.support) (hv : v ∈ p.support) (hvy : v ≠ y) :
    (v ∈ (p.takeUntil y hy).support ∧ v ∉ (p.dropUntil y hy).support) ∨
    (v ∉ (p.takeUntil y hy).support ∧ v ∈ (p.dropUntil y hy).support) := by
  have hsup_eq : p.support =
      (p.takeUntil y hy).support ++ (p.dropUntil y hy).support.tail := by
    conv_lhs => rw [← p.take_spec hy]
    rw [Walk.support_append]
  have hNodup : p.support.Nodup := hp.support_nodup
  
  have hv_split : v ∈ (p.takeUntil y hy).support ∨ v ∈ (p.dropUntil y hy).support.tail := by
    rw [hsup_eq] at hv; exact List.mem_append.mp hv
  
  have hdrop_head : (p.dropUntil y hy).support.head
      (p.dropUntil y hy).support_ne_nil = y := (p.dropUntil y hy).head_support
  have hdrop_cons : (p.dropUntil y hy).support =
      y :: (p.dropUntil y hy).support.tail := by
    conv_lhs => rw [← List.cons_head_tail (p.dropUntil y hy).support_ne_nil]
    rw [hdrop_head]
  rw [hsup_eq] at hNodup
  have hdisj := List.disjoint_of_nodup_append hNodup
  rcases hv_split with hvt | hvd
  · left
    refine ⟨hvt, ?_⟩
    rw [hdrop_cons]
    intro hvd'
    rcases List.mem_cons.mp hvd' with hveq | hvt'
    · exact hvy hveq
    · exact hdisj hvt hvt'
  · right
    refine ⟨?_, ?_⟩
    · intro hvt
      exact hdisj hvt hvd
    · rw [hdrop_cons]; exact List.mem_cons_of_mem _ hvd












private noncomputable def Walk.toInducedSupEdge
    {u v : V} (w : G.Walk u v) (s : Set V) (x y : V)
    (hsub : ∀ z ∈ w.support, z ∈ s)
    (hu : u ∈ s) (hv : v ∈ s) :
    ((G ⊔ SimpleGraph.edge x y).induce s).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil =>
      exact Walk.nil
  | @cons u' v' w'' hadj w' ih =>
      have hv'_in : v' ∈ s := hsub v' (by simp)
      have hw_sub : ∀ z ∈ w'.support, z ∈ s := by
        intro z hz
        exact hsub z (by simp [hz])
      have hu_in : u' ∈ s := hu
      have hw_in : w'' ∈ s := hv
      have hadj_ind : ((G ⊔ SimpleGraph.edge x y).induce s).Adj ⟨u', hu_in⟩ ⟨v', hv'_in⟩ := by
        rw [induce_adj]
        exact Or.inl hadj
      exact Walk.cons hadj_ind (ih hw_sub hv'_in hw_in)

















private theorem induce_unionSupport_sup_edge_no_cut_vertex
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    (v : V) (hv_mem : v ∈ G.unionSupportFinset w₁ w₂)
    (x y : V) (hx : x ∈ G.unionSupportFinset w₁ w₂)
    (hy : y ∈ G.unionSupportFinset w₁ w₂)
    (hxv : x ≠ v) (hyv : y ≠ v) :
    ∃ w : (G ⊔ SimpleGraph.edge a b).Walk x y,
      ∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂ ∧ z ≠ v := by
  
  set S : Set V := (↑(G.unionSupportFinset w₁ w₂) : Set V) with hS_def
  
  have hS_char : ∀ u : V, u ∈ S ↔ u ∈ w₁.support ∨ u ∈ w₂.support := by
    intro u; simp [hS_def, unionSupportFinset]
  
  have ha_S : a ∈ S := by rw [hS_char]; exact Or.inl w₁.start_mem_support
  have hb_S : b ∈ S := by rw [hS_char]; exact Or.inl w₁.end_mem_support
  
  have hab_sup : (G ⊔ SimpleGraph.edge a b).Adj a b := by
    right
    rw [SimpleGraph.edge_adj]
    refine ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
  
  
  
  
  
  
  
  
  
  
  by_cases hva : v = a
  · 
    
    have hub_reach : ∀ u : V, u ∈ S → u ≠ v →
        ∃ w : (G ⊔ SimpleGraph.edge a b).Walk u b,
          ∀ z ∈ w.support, z ∈ S ∧ z ≠ v := by
      intro u hu huv
      have hua : u ≠ a := hva ▸ huv
      rw [hS_char] at hu
      rcases hu with hu₁ | hu₂
      · 
        
        have ha_notin : a ∉ (w₁.dropUntil u hu₁).support :=
          Walk.IsPath.start_notMem_support_dropUntil G hp₁ hu₁ hua
        refine ⟨(w₁.dropUntil u hu₁).mapLe
          (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
        intro z hz
        rw [Walk.support_mapLe_eq_support] at hz
        refine ⟨?_, ?_⟩
        · rw [hS_char]
          exact Or.inl (w₁.support_dropUntil_subset hu₁ hz)
        · intro hzv
          
          have hza : z = a := hzv.trans hva
          exact ha_notin (hza ▸ hz)
      · 
        have ha_notin : a ∉ (w₂.dropUntil u hu₂).support :=
          Walk.IsPath.start_notMem_support_dropUntil G hp₂ hu₂ hua
        refine ⟨(w₂.dropUntil u hu₂).mapLe
          (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
        intro z hz
        rw [Walk.support_mapLe_eq_support] at hz
        refine ⟨?_, ?_⟩
        · rw [hS_char]
          exact Or.inr (w₂.support_dropUntil_subset hu₂ hz)
        · intro hzv
          have hza : z = a := hzv.trans hva
          exact ha_notin (hza ▸ hz)
    
    obtain ⟨wxb, hxb_sub⟩ := hub_reach x hx hxv
    obtain ⟨wyb, hyb_sub⟩ := hub_reach y hy hyv
    refine ⟨wxb.append wyb.reverse, ?_⟩
    intro z hz
    rw [Walk.support_append] at hz
    rcases List.mem_append.mp hz with hz₁ | hz₂
    · exact hxb_sub z hz₁
    · have hz₂' : z ∈ wyb.reverse.support := List.mem_of_mem_tail hz₂
      rw [Walk.support_reverse, List.mem_reverse] at hz₂'
      exact hyb_sub z hz₂'
  · by_cases hvb : v = b
    · 
      have hub_reach : ∀ u : V, u ∈ S → u ≠ v →
          ∃ w : (G ⊔ SimpleGraph.edge a b).Walk u a,
            ∀ z ∈ w.support, z ∈ S ∧ z ≠ v := by
        intro u hu huv
        have hub : u ≠ b := hvb ▸ huv
        rw [hS_char] at hu
        rcases hu with hu₁ | hu₂
        · have hb_notin : b ∉ (w₁.takeUntil u hu₁).support :=
            Walk.IsPath.end_notMem_support_takeUntil G hp₁ hu₁ hub
          refine ⟨(w₁.takeUntil u hu₁).reverse.mapLe
            (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
          intro z hz
          rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse] at hz
          refine ⟨?_, ?_⟩
          · rw [hS_char]
            exact Or.inl (w₁.support_takeUntil_subset hu₁ hz)
          · intro hzv
            have hzb : z = b := hzv.trans hvb
            exact hb_notin (hzb ▸ hz)
        · have hb_notin : b ∉ (w₂.takeUntil u hu₂).support :=
            Walk.IsPath.end_notMem_support_takeUntil G hp₂ hu₂ hub
          refine ⟨(w₂.takeUntil u hu₂).reverse.mapLe
            (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
          intro z hz
          rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse] at hz
          refine ⟨?_, ?_⟩
          · rw [hS_char]
            exact Or.inr (w₂.support_takeUntil_subset hu₂ hz)
          · intro hzv
            have hzb : z = b := hzv.trans hvb
            exact hb_notin (hzb ▸ hz)
      obtain ⟨wxa, hxa_sub⟩ := hub_reach x hx hxv
      obtain ⟨wya, hya_sub⟩ := hub_reach y hy hyv
      refine ⟨wxa.append wya.reverse, ?_⟩
      intro z hz
      rw [Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz₁ | hz₂
      · exact hxa_sub z hz₁
      · have hz₂' : z ∈ wya.reverse.support := List.mem_of_mem_tail hz₂
        rw [Walk.support_reverse, List.mem_reverse] at hz₂'
        exact hya_sub z hz₂'
    · 
      
      
      
      push_neg at hva hvb
      
      have hub_reach : ∀ u : V, u ∈ S → u ≠ v →
          (∃ w : (G ⊔ SimpleGraph.edge a b).Walk u a,
              ∀ z ∈ w.support, z ∈ S ∧ z ≠ v) ∨
          (∃ w : (G ⊔ SimpleGraph.edge a b).Walk u b,
              ∀ z ∈ w.support, z ∈ S ∧ z ≠ v) := by
        intro u hu huv
        rw [hS_char] at hu
        rcases hu with hu₁ | hu₂
        · 
          by_cases hu_eq_a : u = a
          · 
            subst hu_eq_a
            left
            refine ⟨Walk.nil, ?_⟩
            intro z hz
            simp at hz; subst hz
            exact ⟨ha_S, Ne.symm hva⟩
          by_cases hu_eq_b : u = b
          · subst hu_eq_b
            right
            refine ⟨Walk.nil, ?_⟩
            intro z hz
            simp at hz; subst hz
            exact ⟨hb_S, Ne.symm hvb⟩
          
          by_cases hv_in_w₁ : v ∈ w₁.support
          · 
            have hvu : v ≠ u := Ne.symm huv
            rcases Walk.IsPath.mem_takeUntil_or_dropUntil_of_ne G hp₁ hu₁ hv_in_w₁ hvu with
              ⟨hv_take, hv_ndrop⟩ | ⟨hv_ntake, hv_drop⟩
            · 
              right
              refine ⟨(w₁.dropUntil u hu₁).mapLe
                (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
              intro z hz
              rw [Walk.support_mapLe_eq_support] at hz
              refine ⟨?_, ?_⟩
              · rw [hS_char]
                exact Or.inl (w₁.support_dropUntil_subset hu₁ hz)
              · intro hzv; exact hv_ndrop (hzv ▸ hz)
            · 
              left
              refine ⟨(w₁.takeUntil u hu₁).reverse.mapLe
                (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
              intro z hz
              rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse] at hz
              refine ⟨?_, ?_⟩
              · rw [hS_char]
                exact Or.inl (w₁.support_takeUntil_subset hu₁ hz)
              · intro hzv; exact hv_ntake (hzv ▸ hz)
          · 
            right
            refine ⟨(w₁.dropUntil u hu₁).mapLe
              (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
            intro z hz
            rw [Walk.support_mapLe_eq_support] at hz
            refine ⟨?_, ?_⟩
            · rw [hS_char]
              exact Or.inl (w₁.support_dropUntil_subset hu₁ hz)
            · intro hzv
              exact hv_in_w₁ (hzv ▸ w₁.support_dropUntil_subset hu₁ hz)
        · 
          by_cases hu_eq_a : u = a
          · subst hu_eq_a
            left
            refine ⟨Walk.nil, ?_⟩
            intro z hz
            simp at hz; subst hz
            exact ⟨ha_S, Ne.symm hva⟩
          by_cases hu_eq_b : u = b
          · subst hu_eq_b
            right
            refine ⟨Walk.nil, ?_⟩
            intro z hz
            simp at hz; subst hz
            exact ⟨hb_S, Ne.symm hvb⟩
          by_cases hv_in_w₂ : v ∈ w₂.support
          · have hvu : v ≠ u := Ne.symm huv
            rcases Walk.IsPath.mem_takeUntil_or_dropUntil_of_ne G hp₂ hu₂ hv_in_w₂ hvu with
              ⟨hv_take, hv_ndrop⟩ | ⟨hv_ntake, hv_drop⟩
            · right
              refine ⟨(w₂.dropUntil u hu₂).mapLe
                (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
              intro z hz
              rw [Walk.support_mapLe_eq_support] at hz
              refine ⟨?_, ?_⟩
              · rw [hS_char]
                exact Or.inr (w₂.support_dropUntil_subset hu₂ hz)
              · intro hzv; exact hv_ndrop (hzv ▸ hz)
            · left
              refine ⟨(w₂.takeUntil u hu₂).reverse.mapLe
                (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
              intro z hz
              rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse] at hz
              refine ⟨?_, ?_⟩
              · rw [hS_char]
                exact Or.inr (w₂.support_takeUntil_subset hu₂ hz)
              · intro hzv; exact hv_ntake (hzv ▸ hz)
          · right
            refine ⟨(w₂.dropUntil u hu₂).mapLe
              (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_⟩
            intro z hz
            rw [Walk.support_mapLe_eq_support] at hz
            refine ⟨?_, ?_⟩
            · rw [hS_char]
              exact Or.inr (w₂.support_dropUntil_subset hu₂ hz)
            · intro hzv
              exact hv_in_w₂ (hzv ▸ w₂.support_dropUntil_subset hu₂ hz)
      
      obtain hx_reach := hub_reach x hx hxv
      obtain hy_reach := hub_reach y hy hyv
      
      let wab : (G ⊔ SimpleGraph.edge a b).Walk a b := Walk.cons hab_sup Walk.nil
      have wab_sub : ∀ z ∈ wab.support, z ∈ S ∧ z ≠ v := by
        intro z hz
        simp [wab] at hz
        rcases hz with hz | hz
        · subst hz; exact ⟨ha_S, Ne.symm hva⟩
        · subst hz; exact ⟨hb_S, Ne.symm hvb⟩
      rcases hx_reach with ⟨wxa, hxa⟩ | ⟨wxb, hxb⟩
      · rcases hy_reach with ⟨wya, hya⟩ | ⟨wyb, hyb⟩
        · 
          refine ⟨wxa.append wya.reverse, ?_⟩
          intro z hz
          rw [Walk.support_append] at hz
          rcases List.mem_append.mp hz with hz₁ | hz₂
          · exact hxa z hz₁
          · have hz₂' : z ∈ wya.reverse.support := List.mem_of_mem_tail hz₂
            rw [Walk.support_reverse, List.mem_reverse] at hz₂'
            exact hya z hz₂'
        · 
          refine ⟨(wxa.append wab).append wyb.reverse, ?_⟩
          intro z hz
          rw [Walk.support_append, Walk.support_append] at hz
          rcases List.mem_append.mp hz with hz_xab | hz_y
          · rcases List.mem_append.mp hz_xab with hz_xa | hz_ab
            · exact hxa z hz_xa
            · have : z ∈ wab.support := List.mem_of_mem_tail hz_ab
              exact wab_sub z this
          · have hz_y' : z ∈ wyb.reverse.support := List.mem_of_mem_tail hz_y
            rw [Walk.support_reverse, List.mem_reverse] at hz_y'
            exact hyb z hz_y'
      · rcases hy_reach with ⟨wya, hya⟩ | ⟨wyb, hyb⟩
        · 
          refine ⟨(wxb.append wab.reverse).append wya.reverse, ?_⟩
          intro z hz
          rw [Walk.support_append, Walk.support_append] at hz
          rcases List.mem_append.mp hz with hz_xba | hz_y
          · rcases List.mem_append.mp hz_xba with hz_xb | hz_ba
            · exact hxb z hz_xb
            · have hz_ba' : z ∈ wab.reverse.support := List.mem_of_mem_tail hz_ba
              rw [Walk.support_reverse, List.mem_reverse] at hz_ba'
              exact wab_sub z hz_ba'
          · have hz_y' : z ∈ wya.reverse.support := List.mem_of_mem_tail hz_y
            rw [Walk.support_reverse, List.mem_reverse] at hz_y'
            exact hya z hz_y'
        · 
          refine ⟨wxb.append wyb.reverse, ?_⟩
          intro z hz
          rw [Walk.support_append] at hz
          rcases List.mem_append.mp hz with hz₁ | hz₂
          · exact hxb z hz₁
          · have hz₂' : z ∈ wyb.reverse.support := List.mem_of_mem_tail hz₂
            rw [Walk.support_reverse, List.mem_reverse] at hz₂'
            exact hyb z hz₂'




















section NPivotStep2

variable [Fintype V] [DecidableRel G.Adj]




private noncomputable def Walk.toInducedOfSupEdge
    {u v : V} (a b : V) (w : (G ⊔ SimpleGraph.edge a b).Walk u v) (s : Set V)
    (hsub : ∀ z ∈ w.support, z ∈ s)
    (hu : u ∈ s) (hv : v ∈ s) :
    ((G ⊔ SimpleGraph.edge a b).induce s).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil =>
      exact Walk.nil
  | @cons u' v' w'' hadj w' ih =>
      have hv'_in : v' ∈ s := hsub v' (by simp)
      have hw_sub : ∀ z ∈ w'.support, z ∈ s := by
        intro z hz
        exact hsub z (by simp [hz])
      have hu_in : u' ∈ s := hu
      have hw_in : w'' ∈ s := hv
      have hadj_ind :
          ((G ⊔ SimpleGraph.edge a b).induce s).Adj ⟨u', hu_in⟩ ⟨v', hv'_in⟩ := by
        rw [induce_adj]
        exact hadj
      exact Walk.cons hadj_ind (ih hw_sub hv'_in hw_in)

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in

private lemma Walk.toInducedOfSupEdge_support_map
    {u v : V} (a b : V) (w : (G ⊔ SimpleGraph.edge a b).Walk u v) (s : Set V)
    (hsub : ∀ z ∈ w.support, z ∈ s) (hu : u ∈ s) (hv : v ∈ s) :
    (Walk.toInducedOfSupEdge G a b w s hsub hu hv).support.map Subtype.val =
      w.support := by
  induction w with
  | nil => simp [Walk.toInducedOfSupEdge]
  | @cons u' v' w'' hadj w' ih =>
      simp only [Walk.toInducedOfSupEdge, Walk.support_cons, List.map_cons]
      have hv'_in : v' ∈ s := hsub v' (by simp)
      have hw_sub : ∀ z ∈ w'.support, z ∈ s := fun z hz => hsub z (by simp [hz])
      congr 1
      exact ih hw_sub hv'_in hv

omit [DecidableEq V] [Fintype V] [DecidableRel G.Adj] in


private lemma Walk.toInducedOfSupEdge_edges_map
    {u v : V} (a b : V) (w : (G ⊔ SimpleGraph.edge a b).Walk u v) (s : Set V)
    (hsub : ∀ z ∈ w.support, z ∈ s) (hu : u ∈ s) (hv : v ∈ s) :
    (Walk.toInducedOfSupEdge G a b w s hsub hu hv).edges.map (Sym2.map Subtype.val) =
      w.edges := by
  induction w with
  | nil => simp [Walk.toInducedOfSupEdge]
  | @cons u' v' w'' hadj w' ih =>
      simp only [Walk.toInducedOfSupEdge, Walk.edges_cons, List.map_cons,
        Sym2.map_pair_eq]
      have hv'_in : v' ∈ s := hsub v' (by simp)
      have hw_sub : ∀ z ∈ w'.support, z ∈ s := fun z hz => hsub z (by simp [hz])
      congr 1
      exact ih hw_sub hv'_in hv
















private theorem two_disjoint_paths_in_induce_unionSupport
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    (u v : V) (hu : u ∈ G.unionSupportFinset w₁ w₂)
    (hv : v ∈ G.unionSupportFinset w₁ w₂) (huv : u ≠ v) :
    Nonempty (((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).STDisjointPaths
        ⟨u, hu⟩ ⟨v, hv⟩ 2) := by
  set S : Set V := (↑(G.unionSupportFinset w₁ w₂) : Set V) with hS_def
  
  have hS_char : ∀ x : V, x ∈ S ↔ x ∈ w₁.support ∨ x ∈ w₂.support := by
    intro x; simp [hS_def, unionSupportFinset]
  set H' : SimpleGraph S := (G ⊔ SimpleGraph.edge a b).induce S with hH'_def
  
  
  refine menger_st_of_separator_bound H' ⟨u, hu⟩ ⟨v, hv⟩ 2 ?_ ?_
  · 
    intro heq
    exact huv (Subtype.mk.injEq .. |>.mp heq)
  · 
    
    intro S' hS'u hS'v hsep
    
    by_contra hlt
    push Not at hlt
    
    have hcard_le : S'.card ≤ 1 := by omega
    
    have hcard_cases : S'.card = 0 ∨ S'.card = 1 := by omega
    rcases hcard_cases with hcard0 | hcard1
    · 
      rw [Finset.card_eq_zero] at hcard0
      subst hcard0
      
      have hconn := induce_unionSupport_connected G w₁ w₂
      
      
      have hle : G.induce S ≤ (G ⊔ SimpleGraph.edge a b).induce S := by
        intro x y h
        
        exact Or.inl h
      have hreach :
          ((G ⊔ SimpleGraph.edge a b).induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
        Reachable.mono hle (hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩)
      obtain ⟨w_induce⟩ := hreach
      
      have := hsep ⟨u, hu⟩ (Finset.mem_singleton.mpr rfl) ⟨v, hv⟩
        (Finset.mem_singleton.mpr rfl) hS'u hS'v w_induce
      obtain ⟨_, _, hmem⟩ := this
      exact Finset.notMem_empty _ hmem
    · 
      rw [Finset.card_eq_one] at hcard1
      obtain ⟨⟨z, hz_mem⟩, hS'_eq⟩ := hcard1
      subst hS'_eq
      
      obtain ⟨w_SupEdge, hw_sub⟩ :=
        induce_unionSupport_sup_edge_no_cut_vertex G w₁ w₂ hp₁ hp₂ hne
          hw₁_avoid hw₂_avoid z hz_mem u v hu hv
          (by
            
            intro heq
            have : (⟨u, hu⟩ : ↥S) = ⟨z, hz_mem⟩ := Subtype.ext heq
            exact hS'u (Finset.mem_singleton.mpr this))
          (by
            intro heq
            have : (⟨v, hv⟩ : ↥S) = ⟨z, hz_mem⟩ := Subtype.ext heq
            exact hS'v (Finset.mem_singleton.mpr this))
      
      have hw_in_S : ∀ x ∈ w_SupEdge.support, x ∈ S := fun x hx =>
        (hw_sub x hx).1
      let w_induce := Walk.toInducedOfSupEdge G a b w_SupEdge S hw_in_S hu hv
      
      have hmem_sep := hsep ⟨u, hu⟩ (Finset.mem_singleton.mpr rfl) ⟨v, hv⟩
        (Finset.mem_singleton.mpr rfl) hS'u hS'v w_induce
      obtain ⟨⟨q, hq_S⟩, hq_supp, hq_in_sep⟩ := hmem_sep
      have hq_eq_z : q = z := by
        rw [Finset.mem_singleton] at hq_in_sep
        exact Subtype.mk.injEq .. |>.mp hq_in_sep
      
      have hmap := Walk.toInducedOfSupEdge_support_map G a b w_SupEdge S hw_in_S hu hv
      have hz_in_orig : z ∈ w_SupEdge.support := by
        have hz_map : q ∈ w_induce.support.map Subtype.val :=
          List.mem_map.mpr ⟨⟨q, hq_S⟩, hq_supp, rfl⟩
        rw [hmap] at hz_map
        exact hq_eq_z ▸ hz_map
      
      exact (hw_sub z hz_in_orig).2 rfl

end NPivotStep2













section EdgeNotBridge







private theorem edge_not_bridge_in_induce_unionSupport
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₁ b₁ : V} (he₁ : s(a₁, b₁) ∈ w₁.edges)
    (x y : V) (hx : x ∈ G.unionSupportFinset w₁ w₂)
    (hy : y ∈ G.unionSupportFinset w₁ w₂) :
    ∃ w : (G ⊔ SimpleGraph.edge a b).Walk x y,
      (∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂) ∧
      s(a₁, b₁) ∉ w.edges := by
  set S : Set V := (↑(G.unionSupportFinset w₁ w₂) : Set V) with hS_def
  have hS_char : ∀ u : V, u ∈ S ↔ u ∈ w₁.support ∨ u ∈ w₂.support := by
    intro u; simp [hS_def, unionSupportFinset]
  have hS_iff : ∀ u : V, u ∈ S ↔ u ∈ G.unionSupportFinset w₁ w₂ := by
    intro u; rfl
  have ha_S : a ∈ G.unionSupportFinset w₁ w₂ :=
    G.mem_unionSupportFinset_start w₁ w₂
  have hb_S : b ∈ G.unionSupportFinset w₁ w₂ :=
    G.mem_unionSupportFinset_end w₁ w₂
  
  have hab_sup : (G ⊔ SimpleGraph.edge a b).Adj a b := by
    right
    rw [SimpleGraph.edge_adj]
    refine ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
  
  have he₁_ne_ab : s(a₁, b₁) ≠ s(a, b) := by
    intro heq; rw [heq] at he₁; exact hw₁_avoid he₁
  
  
  have hub_reach_w :
      ∀ (w_i : G.Walk a b), w_i.IsPath → s(a, b) ∉ w_i.edges →
      (∀ q ∈ w_i.support, q ∈ G.unionSupportFinset w₁ w₂) →
      ∀ u : V, u ∈ w_i.support →
      (∃ w : (G ⊔ SimpleGraph.edge a b).Walk u a,
          (∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂) ∧
          s(a₁, b₁) ∉ w.edges) ∨
      (∃ w : (G ⊔ SimpleGraph.edge a b).Walk u b,
          (∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂) ∧
          s(a₁, b₁) ∉ w.edges) := by
    intro w_i hp_i hw_avoid h_supp_in u hu_in
    
    by_cases h_e₁_take : s(a₁, b₁) ∈ (w_i.takeUntil u hu_in).edges
    · 
      have h_trail : w_i.IsTrail := hp_i.isTrail
      have h_nodup : w_i.edges.Nodup := h_trail.edges_nodup
      have h_eq : w_i.edges =
          (w_i.takeUntil u hu_in).edges ++ (w_i.dropUntil u hu_in).edges := by
        conv_lhs => rw [← w_i.take_spec hu_in]
        rw [Walk.edges_append]
      rw [h_eq] at h_nodup
      have hdisj := List.disjoint_of_nodup_append h_nodup
      have h_e₁_drop : s(a₁, b₁) ∉ (w_i.dropUntil u hu_in).edges :=
        fun h => hdisj h_e₁_take h
      
      let wd := w_i.dropUntil u hu_in
      refine Or.inr ⟨wd.mapLe (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_, ?_⟩
      · intro z hz
        rw [Walk.support_mapLe_eq_support] at hz
        exact h_supp_in z (w_i.support_dropUntil_subset hu_in hz)
      · 
        intro h
        rw [Walk.edges_mapLe_eq_edges] at h
        exact h_e₁_drop h
    · 
      let wt := w_i.takeUntil u hu_in
      refine Or.inl ⟨wt.reverse.mapLe (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b), ?_, ?_⟩
      · intro z hz
        rw [Walk.support_mapLe_eq_support, Walk.support_reverse, List.mem_reverse] at hz
        exact h_supp_in z (w_i.support_takeUntil_subset hu_in hz)
      · intro h
        rw [Walk.edges_mapLe_eq_edges, Walk.edges_reverse, List.mem_reverse] at h
        exact h_e₁_take h
  
  have hsupp_w₁ : ∀ q ∈ w₁.support, q ∈ G.unionSupportFinset w₁ w₂ :=
    fun q hq => G.mem_unionSupportFinset_of_mem_left w₁ w₂ hq
  have hsupp_w₂ : ∀ q ∈ w₂.support, q ∈ G.unionSupportFinset w₁ w₂ :=
    fun q hq => G.mem_unionSupportFinset_of_mem_right w₁ w₂ hq
  
  have hub_reach : ∀ u : V, u ∈ G.unionSupportFinset w₁ w₂ →
      (∃ w : (G ⊔ SimpleGraph.edge a b).Walk u a,
          (∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂) ∧
          s(a₁, b₁) ∉ w.edges) ∨
      (∃ w : (G ⊔ SimpleGraph.edge a b).Walk u b,
          (∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂) ∧
          s(a₁, b₁) ∉ w.edges) := by
    intro u hu
    have hu_or : u ∈ w₁.support ∨ u ∈ w₂.support := by
      simp [unionSupportFinset] at hu; exact hu
    rcases hu_or with hu₁ | hu₂
    · exact hub_reach_w w₁ hp₁ hw₁_avoid hsupp_w₁ u hu₁
    · exact hub_reach_w w₂ hp₂ hw₂_avoid hsupp_w₂ u hu₂
  
  let wab : (G ⊔ SimpleGraph.edge a b).Walk a b :=
    Walk.cons hab_sup Walk.nil
  have wab_supp : ∀ z ∈ wab.support, z ∈ G.unionSupportFinset w₁ w₂ := by
    intro z hz
    simp [wab] at hz
    rcases hz with hz | hz <;> subst hz
    · exact ha_S
    · exact hb_S
  have wab_no_e₁ : s(a₁, b₁) ∉ wab.edges := by
    
    show s(a₁, b₁) ∉ (Walk.cons hab_sup (Walk.nil : (G ⊔ SimpleGraph.edge a b).Walk b b)).edges
    rw [Walk.edges_cons, Walk.edges_nil]
    intro h
    rcases List.mem_cons.mp h with h_eq | h_mem
    · exact he₁_ne_ab h_eq
    · exact List.not_mem_nil h_mem
  
  rcases hub_reach x hx with ⟨wxa, hxa_sub, hxa_e⟩ | ⟨wxb, hxb_sub, hxb_e⟩
  · rcases hub_reach y hy with ⟨wya, hya_sub, hya_e⟩ | ⟨wyb, hyb_sub, hyb_e⟩
    · 
      refine ⟨wxa.append wya.reverse, ?_, ?_⟩
      · intro z hz
        rw [Walk.support_append] at hz
        rcases List.mem_append.mp hz with hz₁ | hz₂
        · exact hxa_sub z hz₁
        · have hz₂' : z ∈ wya.reverse.support := List.mem_of_mem_tail hz₂
          rw [Walk.support_reverse, List.mem_reverse] at hz₂'
          exact hya_sub z hz₂'
      · rw [Walk.edges_append]
        intro h
        rcases List.mem_append.mp h with h₁ | h₂
        · exact hxa_e h₁
        · rw [Walk.edges_reverse, List.mem_reverse] at h₂
          exact hya_e h₂
    · 
      refine ⟨(wxa.append wab).append wyb.reverse, ?_, ?_⟩
      · intro z hz
        rw [Walk.support_append, Walk.support_append] at hz
        rcases List.mem_append.mp hz with hz_xab | hz_y
        · rcases List.mem_append.mp hz_xab with hz_xa | hz_ab
          · exact hxa_sub z hz_xa
          · have : z ∈ wab.support := List.mem_of_mem_tail hz_ab
            exact wab_supp z this
        · have hz_y' : z ∈ wyb.reverse.support := List.mem_of_mem_tail hz_y
          rw [Walk.support_reverse, List.mem_reverse] at hz_y'
          exact hyb_sub z hz_y'
      · rw [Walk.edges_append, Walk.edges_append]
        intro h
        rcases List.mem_append.mp h with h_xab | h_y
        · rcases List.mem_append.mp h_xab with h_xa | h_ab
          · exact hxa_e h_xa
          · exact wab_no_e₁ h_ab
        · rw [Walk.edges_reverse, List.mem_reverse] at h_y
          exact hyb_e h_y
  · rcases hub_reach y hy with ⟨wya, hya_sub, hya_e⟩ | ⟨wyb, hyb_sub, hyb_e⟩
    · 
      refine ⟨(wxb.append wab.reverse).append wya.reverse, ?_, ?_⟩
      · intro z hz
        rw [Walk.support_append, Walk.support_append] at hz
        rcases List.mem_append.mp hz with hz_xba | hz_y
        · rcases List.mem_append.mp hz_xba with hz_xb | hz_ba
          · exact hxb_sub z hz_xb
          · have hz_ba' : z ∈ wab.reverse.support := List.mem_of_mem_tail hz_ba
            rw [Walk.support_reverse, List.mem_reverse] at hz_ba'
            exact wab_supp z hz_ba'
        · have hz_y' : z ∈ wya.reverse.support := List.mem_of_mem_tail hz_y
          rw [Walk.support_reverse, List.mem_reverse] at hz_y'
          exact hya_sub z hz_y'
      · rw [Walk.edges_append, Walk.edges_append]
        intro h
        rcases List.mem_append.mp h with h_xba | h_y
        · rcases List.mem_append.mp h_xba with h_xb | h_ba
          · exact hxb_e h_xb
          · rw [Walk.edges_reverse, List.mem_reverse] at h_ba
            exact wab_no_e₁ h_ba
        · rw [Walk.edges_reverse, List.mem_reverse] at h_y
          exact hya_e h_y
    · 
      refine ⟨wxb.append wyb.reverse, ?_, ?_⟩
      · intro z hz
        rw [Walk.support_append] at hz
        rcases List.mem_append.mp hz with hz₁ | hz₂
        · exact hxb_sub z hz₁
        · have hz₂' : z ∈ wyb.reverse.support := List.mem_of_mem_tail hz₂
          rw [Walk.support_reverse, List.mem_reverse] at hz₂'
          exact hyb_sub z hz₂'
      · rw [Walk.edges_append]
        intro h
        rcases List.mem_append.mp h with h₁ | h₂
        · exact hxb_e h₁
        · rw [Walk.edges_reverse, List.mem_reverse] at h₂
          exact hyb_e h₂




private theorem edge_not_bridge_in_induce_unionSupport_right
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₃ b₃ : V} (he₃ : s(a₃, b₃) ∈ w₂.edges)
    (x y : V) (hx : x ∈ G.unionSupportFinset w₁ w₂)
    (hy : y ∈ G.unionSupportFinset w₁ w₂) :
    ∃ w : (G ⊔ SimpleGraph.edge a b).Walk x y,
      (∀ z ∈ w.support, z ∈ G.unionSupportFinset w₁ w₂) ∧
      s(a₃, b₃) ∉ w.edges := by
  
  have hsym : ∀ v : V,
      v ∈ G.unionSupportFinset w₁ w₂ ↔ v ∈ G.unionSupportFinset w₂ w₁ := by
    intro v
    simp only [unionSupportFinset, Finset.mem_union]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hx' : x ∈ G.unionSupportFinset w₂ w₁ := (hsym x).mp hx
  have hy' : y ∈ G.unionSupportFinset w₂ w₁ := (hsym y).mp hy
  obtain ⟨w, hw_sub, hw_e⟩ := edge_not_bridge_in_induce_unionSupport
    G w₂ w₁ hp₂ hp₁ hne hw₂_avoid hw₁_avoid he₃ x y hx' hy'
  refine ⟨w, ?_, hw_e⟩
  intro z hz
  exact (hsym z).mpr (hw_sub z hz)

end EdgeNotBridge








section LiftToInduce

variable [Fintype V] [DecidableRel G.Adj]




private theorem induce_unionSupport_sup_edge_no_cut_vertex_in_induce
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    (v x y : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)) (hxv : x ≠ v) (hyv : y ≠ v) :
    ∃ w : ((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).Walk x y,
      ∀ q ∈ w.support, q ≠ v := by
  have hxv' : x.val ≠ v.val := fun h => hxv (Subtype.ext h)
  have hyv' : y.val ≠ v.val := fun h => hyv (Subtype.ext h)
  obtain ⟨w_sup, hw_sub⟩ :=
    induce_unionSupport_sup_edge_no_cut_vertex G w₁ w₂ hp₁ hp₂ hne
      hw₁_avoid hw₂_avoid v.val v.property x.val y.val x.property y.property hxv' hyv'
  have hw_in_S : ∀ z ∈ w_sup.support,
      z ∈ (↑(G.unionSupportFinset w₁ w₂) : Set V) :=
    fun z hz => (hw_sub z hz).1
  refine ⟨(Walk.toInducedOfSupEdge G a b w_sup
    (↑(G.unionSupportFinset w₁ w₂) : Set V) hw_in_S x.property y.property).copy
    (Subtype.ext rfl) (Subtype.ext rfl), ?_⟩
  intro q hq h_eq
  rw [Walk.support_copy] at hq
  have hmap := Walk.toInducedOfSupEdge_support_map G a b w_sup
    (↑(G.unionSupportFinset w₁ w₂) : Set V) hw_in_S x.property y.property
  have hq_in : q.val ∈ w_sup.support := by
    have hin_map : q.val ∈ (Walk.toInducedOfSupEdge G a b w_sup
        (↑(G.unionSupportFinset w₁ w₂) : Set V)
        hw_in_S x.property y.property).support.map Subtype.val :=
      List.mem_map.mpr ⟨q, hq, rfl⟩
    rwa [hmap] at hin_map
  exact (hw_sub q.val hq_in).2 (congr_arg Subtype.val h_eq)












omit [DecidableEq V] in


private lemma Walk.IsPath.length_ge_two_of_avoid_endpoint_edge
    {a b : V} {w : G.Walk a b} (hp : w.IsPath) (hne : a ≠ b)
    (havoid : s(a, b) ∉ w.edges) : 2 ≤ w.length := by
  by_contra hlt
  push Not at hlt
  interval_cases hwl : w.length
  · cases w with
    | nil => exact hne rfl
    | cons _ _ => simp [Walk.length] at hwl
  · cases w with
    | nil => simp [Walk.length] at hwl
    | @cons _ mid _ hadj p =>
      have hp_len : p.length = 0 := by simpa [Walk.length] using hwl
      have hmid : mid = b := by
        cases p with
        | nil => rfl
        | cons _ _ => simp [Walk.length] at hp_len
      subst hmid
      apply havoid
      simp [Walk.edges_cons]

omit [DecidableEq V] in


private lemma Walk.IsPath.exists_internal_vertex
    {a b : V} {w : G.Walk a b} (hp : w.IsPath) (hlen : 2 ≤ w.length) :
    ∃ z : V, z ∈ w.support ∧ z ≠ a ∧ z ≠ b := by
  have hsup_len : 3 ≤ w.support.length := by
    rw [Walk.length_support]; omega
  have hidx1 : 1 < w.support.length := by omega
  have hidx0 : 0 < w.support.length := by omega
  have hidx_last : w.support.length - 1 < w.support.length := by omega
  refine ⟨w.support[1], List.getElem_mem hidx1, ?_, ?_⟩
  · intro hza
    have hnd := hp.support_nodup
    have hhead : w.support.head w.support_ne_nil = a := w.head_support
    have h0_eq : w.support[0]'hidx0 = a := by
      rw [List.getElem_zero]; exact hhead
    have heq01 : w.support[0]'hidx0 = w.support[1] := h0_eq.trans hza.symm
    have : (0 : ℕ) = 1 := hnd.getElem_inj_iff.mp heq01
    exact absurd this (by decide)
  · intro hzb
    have hnd := hp.support_nodup
    have hlast_eq : w.support[w.support.length - 1]'hidx_last = b := by
      have := w.getLast_support
      rw [List.getLast_eq_getElem] at this
      exact this
    have heq1last : w.support[1] = w.support[w.support.length - 1]'hidx_last :=
      hzb.trans hlast_eq.symm
    have hidx_eq : (1 : ℕ) = w.support.length - 1 := hnd.getElem_inj_iff.mp heq1last
    omega




private noncomputable def Walk.toInducedSelf
    {U : Type*} {G' : SimpleGraph U} {u v : U}
    (w : G'.Walk u v) (T : Set U)
    (hsub : ∀ z ∈ w.support, z ∈ T)
    (hu : u ∈ T) (hv : v ∈ T) :
    (G'.induce T).Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact Walk.nil
  | @cons u' v' w'' hadj w' ih =>
      have hv'_in : v' ∈ T := hsub v' (by simp)
      have hw_sub : ∀ z ∈ w'.support, z ∈ T := fun z hz =>
        hsub z (by simp [hz])
      have hadj_ind : (G'.induce T).Adj ⟨u', hu⟩ ⟨v', hv'_in⟩ := by
        rw [induce_adj]; exact hadj
      exact Walk.cons hadj_ind (ih hw_sub hv'_in hv)














theorem induce_unionSupport_sup_edge_isVertexConnected_two
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges) :
    ((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).IsVertexConnected 2 := by
  set S : Set V := (↑(G.unionSupportFinset w₁ w₂) : Set V) with hS_def
  set H' : SimpleGraph ↥S := (G ⊔ SimpleGraph.edge a b).induce S with hH'_def
  
  have hS_char : ∀ u : V, u ∈ S ↔ u ∈ w₁.support ∨ u ∈ w₂.support := by
    intro u; simp [hS_def, unionSupportFinset]
  have ha_S : a ∈ S := by rw [hS_char]; exact Or.inl w₁.start_mem_support
  have hb_S : b ∈ S := by rw [hS_char]; exact Or.inl w₁.end_mem_support
  
  have hcard_S : 3 ≤ (G.unionSupportFinset w₁ w₂).card := by
    have hlen₁ : 2 ≤ w₁.length :=
      Walk.IsPath.length_ge_two_of_avoid_endpoint_edge G hp₁ hne hw₁_avoid
    obtain ⟨z, hz_w₁, hz_a, hz_b⟩ := Walk.IsPath.exists_internal_vertex G hp₁ hlen₁
    have hz_S : z ∈ S := by rw [hS_char]; exact Or.inl hz_w₁
    have ha_mem : a ∈ G.unionSupportFinset w₁ w₂ := ha_S
    have hb_mem : b ∈ G.unionSupportFinset w₁ w₂ := hb_S
    have hz_mem : z ∈ G.unionSupportFinset w₁ w₂ := hz_S
    have hsubset : ({a, b, z} : Finset V) ⊆ G.unionSupportFinset w₁ w₂ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha_mem
      · exact hb_mem
      · exact hz_mem
    have hcard_three : ({a, b, z} : Finset V).card = 3 := by
      rw [show ({a, b, z} : Finset V) = insert a (insert b {z}) from rfl]
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
          Finset.card_singleton]
      · rw [Finset.mem_singleton]
        exact fun h => hz_b h.symm
      · rw [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨hne, fun h => hz_a h.symm⟩
    calc 3 = ({a, b, z} : Finset V).card := hcard_three.symm
      _ ≤ (G.unionSupportFinset w₁ w₂).card := Finset.card_le_card hsubset
  
  have hfinV : Fintype.card ↥S = (G.unionSupportFinset w₁ w₂).card := by
    show Fintype.card ↑(↑(G.unionSupportFinset w₁ w₂) : Set V) =
      (G.unionSupportFinset w₁ w₂).card
    exact Fintype.card_coe _
  refine ⟨?_, ?_⟩
  · rw [hfinV]; omega
  · intro S' hS'
    have hcard_cases : S'.card = 0 ∨ S'.card = 1 := by omega
    rcases hcard_cases with hcard0 | hcard1
    · 
      rw [Finset.card_eq_zero] at hcard0
      subst hcard0
      change (H'.induce ((Finset.univ \ ∅ : Finset ↥S) : Set ↥S)).Connected
      rw [show ((Finset.univ \ ∅ : Finset ↥S) : Set ↥S) = Set.univ by
        ext z; simp]
      have hH'_conn : H'.Connected := by
        have hG_S_conn : (G.induce S).Connected :=
          induce_unionSupport_connected G w₁ w₂
        have hle : G.induce S ≤ H' := fun _ _ h => Or.inl h
        rw [connected_iff] at hG_S_conn ⊢
        refine ⟨?_, hG_S_conn.2⟩
        intro u v
        exact (hG_S_conn.1 u v).mono hle
      rw [connected_iff] at hH'_conn ⊢
      refine ⟨?_, ?_⟩
      · intro ⟨u, hu_univ⟩ ⟨v, hv_univ⟩
        have hreach : H'.Reachable u v := hH'_conn.1 u v
        obtain ⟨w⟩ := hreach
        exact ⟨Walk.toInducedSelf w (Set.univ : Set ↥S)
          (fun _ _ => Set.mem_univ _) hu_univ hv_univ⟩
      · obtain ⟨u⟩ := hH'_conn.2
        exact ⟨⟨u, Set.mem_univ _⟩⟩
    · 
      rw [Finset.card_eq_one] at hcard1
      obtain ⟨v, hS'_eq⟩ := hcard1
      subst hS'_eq
      set T : Set ↥S := ((Finset.univ \ ({v} : Finset ↥S) : Finset ↥S) : Set ↥S) with hT_def
      have hT_char : ∀ q : ↥S, q ∈ T ↔ q ≠ v := by
        intro q
        simp only [hT_def, Finset.coe_sdiff, Finset.coe_univ, Finset.coe_singleton,
          Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      rw [connected_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨⟨x, hx_S⟩, hx_ne⟩ ⟨⟨y, hy_S⟩, hy_ne⟩
        have hxv : (⟨x, hx_S⟩ : ↥S) ≠ v := (hT_char _).mp hx_ne
        have hyv : (⟨y, hy_S⟩ : ↥S) ≠ v := (hT_char _).mp hy_ne
        obtain ⟨w_H', hw_avoid⟩ :=
          induce_unionSupport_sup_edge_no_cut_vertex_in_induce
            G w₁ w₂ hp₁ hp₂ hne hw₁_avoid hw₂_avoid v ⟨x, hx_S⟩ ⟨y, hy_S⟩ hxv hyv
        have hw_in_T : ∀ q ∈ w_H'.support, q ∈ T := fun q hq =>
          (hT_char q).mpr (hw_avoid q hq)
        exact ⟨Walk.toInducedSelf w_H' T hw_in_T hx_ne hy_ne⟩
      · 
        by_cases hva : v = ⟨a, ha_S⟩
        · refine ⟨⟨⟨b, hb_S⟩, ?_⟩⟩
          rw [hT_char]
          intro h
          
          have hb_eq_va : b = v.val := congr_arg Subtype.val h
          rw [hva] at hb_eq_va
          exact hne hb_eq_va.symm
        · refine ⟨⟨⟨a, ha_S⟩, ?_⟩⟩
          rw [hT_char]
          exact fun h => hva h.symm




private theorem edge_not_bridge_in_induce_unionSupport_lifted
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₁ b₁ : V} (he₁ : s(a₁, b₁) ∈ w₁.edges)
    (ha₁_S : a₁ ∈ G.unionSupportFinset w₁ w₂)
    (hb₁_S : b₁ ∈ G.unionSupportFinset w₁ w₂)
    (x y : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)) :
    ∃ w : ((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).Walk x y,
      s(⟨a₁, ha₁_S⟩, ⟨b₁, hb₁_S⟩) ∉ w.edges := by
  obtain ⟨w_sup, hw_sub, hw_e⟩ :=
    edge_not_bridge_in_induce_unionSupport G w₁ w₂ hp₁ hp₂ hne
      hw₁_avoid hw₂_avoid he₁ x.val y.val x.property y.property
  refine ⟨(Walk.toInducedOfSupEdge G a b w_sup
    (↑(G.unionSupportFinset w₁ w₂) : Set V) hw_sub x.property y.property).copy
    (Subtype.ext rfl) (Subtype.ext rfl), ?_⟩
  intro h_in
  rw [Walk.edges_copy] at h_in
  apply hw_e
  have h_map :=
    Walk.toInducedOfSupEdge_edges_map G a b w_sup
      (↑(G.unionSupportFinset w₁ w₂) : Set V) hw_sub x.property y.property
  have h_lift : s(a₁, b₁) ∈ (Walk.toInducedOfSupEdge G a b w_sup
        (↑(G.unionSupportFinset w₁ w₂) : Set V)
        hw_sub x.property y.property).edges.map (Sym2.map Subtype.val) :=
    List.mem_map.mpr ⟨s(⟨a₁, ha₁_S⟩, ⟨b₁, hb₁_S⟩), h_in, by simp [Sym2.map_pair_eq]⟩
  rwa [h_map] at h_lift


private theorem edge_not_bridge_in_induce_unionSupport_lifted_right
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₃ b₃ : V} (he₃ : s(a₃, b₃) ∈ w₂.edges)
    (ha₃_S : a₃ ∈ G.unionSupportFinset w₁ w₂)
    (hb₃_S : b₃ ∈ G.unionSupportFinset w₁ w₂)
    (x y : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)) :
    ∃ w : ((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).Walk x y,
      s(⟨a₃, ha₃_S⟩, ⟨b₃, hb₃_S⟩) ∉ w.edges := by
  obtain ⟨w_sup, hw_sub, hw_e⟩ :=
    edge_not_bridge_in_induce_unionSupport_right G w₁ w₂ hp₁ hp₂ hne
      hw₁_avoid hw₂_avoid he₃ x.val y.val x.property y.property
  refine ⟨(Walk.toInducedOfSupEdge G a b w_sup
    (↑(G.unionSupportFinset w₁ w₂) : Set V) hw_sub x.property y.property).copy
    (Subtype.ext rfl) (Subtype.ext rfl), ?_⟩
  intro h_in
  rw [Walk.edges_copy] at h_in
  apply hw_e
  have h_map :=
    Walk.toInducedOfSupEdge_edges_map G a b w_sup
      (↑(G.unionSupportFinset w₁ w₂) : Set V) hw_sub x.property y.property
  have h_lift : s(a₃, b₃) ∈ (Walk.toInducedOfSupEdge G a b w_sup
        (↑(G.unionSupportFinset w₁ w₂) : Set V)
        hw_sub x.property y.property).edges.map (Sym2.map Subtype.val) :=
    List.mem_map.mpr ⟨s(⟨a₃, ha₃_S⟩, ⟨b₃, hb₃_S⟩), h_in, by simp [Sym2.map_pair_eq]⟩
  rwa [h_map] at h_lift

end LiftToInduce









section SubdivideOnce

variable [Fintype V] [DecidableRel G.Adj]







private theorem subdivide_e1_in_induce_no_cut_vertex
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₁ b₁ : V} (he₁ : s(a₁, b₁) ∈ w₁.edges)
    (ha₁_S : a₁ ∈ G.unionSupportFinset w₁ w₂)
    (hb₁_S : b₁ ∈ G.unionSupportFinset w₁ w₂)
    (z' x' y' : (↑(G.unionSupportFinset w₁ w₂) : Set V) ⊕ Unit)
    (hxz : x' ≠ z') (hyz : y' ≠ z') :
    ∃ w : (((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).subdivideEdge
        ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).Walk x' y',
      ∀ q ∈ w.support, q ≠ z' := by
  
  have hG_adj : G.Adj a₁ b₁ := w₁.adj_of_mem_edges he₁
  have hH'_adj : ((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).Adj
        ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩ := by
    rw [induce_adj]; exact Or.inl hG_adj
  
  have h_no_cut : ∀ (z x y : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)),
      x ≠ z → y ≠ z →
      ∃ w : ((G ⊔ SimpleGraph.edge a b).induce
          (↑(G.unionSupportFinset w₁ w₂) : Set V)).Walk x y,
        ∀ q ∈ w.support, q ≠ z := fun z x y hxz hyz =>
    induce_unionSupport_sup_edge_no_cut_vertex_in_induce
      G w₁ w₂ hp₁ hp₂ hne hw₁_avoid hw₂_avoid z x y hxz hyz
  
  have h_not_bridge : ∀ (x y : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)),
      ∃ w : ((G ⊔ SimpleGraph.edge a b).induce
          (↑(G.unionSupportFinset w₁ w₂) : Set V)).Walk x y,
        s(⟨a₁, ha₁_S⟩, ⟨b₁, hb₁_S⟩) ∉ w.edges := fun x y =>
    edge_not_bridge_in_induce_unionSupport_lifted
      G w₁ w₂ hp₁ hp₂ hne hw₁_avoid hw₂_avoid he₁ ha₁_S hb₁_S x y
  
  exact subdivideEdge_walk_avoiding (G := (G ⊔ SimpleGraph.edge a b).induce
    (↑(G.unionSupportFinset w₁ w₂) : Set V))
    ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩ hH'_adj h_no_cut h_not_bridge z' x' y' hxz hyz

end SubdivideOnce

















section EdgeNotBridgeAfterSubdivide

variable [Fintype V] [DecidableRel G.Adj]




private theorem edge_not_bridge_in_subdivided_H'
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₁ b₁ : V} (he₁ : s(a₁, b₁) ∈ w₁.edges)
    (ha₁_S : a₁ ∈ G.unionSupportFinset w₁ w₂)
    (hb₁_S : b₁ ∈ G.unionSupportFinset w₁ w₂)
    {a₃ b₃ : V} (he₃ : s(a₃, b₃) ∈ w₂.edges)
    (ha₃_S : a₃ ∈ G.unionSupportFinset w₁ w₂)
    (hb₃_S : b₃ ∈ G.unionSupportFinset w₁ w₂)
    (x' y' : (↑(G.unionSupportFinset w₁ w₂) : Set V) ⊕ Unit) :
    ∃ w : (((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).subdivideEdge
        ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).Walk x' y',
      s(Sum.inl (⟨a₃, ha₃_S⟩ :
          (↑(G.unionSupportFinset w₁ w₂) : Set V)),
        Sum.inl ⟨b₃, hb₃_S⟩) ∉ w.edges := by
  
  set H' : SimpleGraph (↑(G.unionSupportFinset w₁ w₂) : Set V) :=
    (G ⊔ SimpleGraph.edge a b).induce
      (↑(G.unionSupportFinset w₁ w₂) : Set V) with hH'_def
  have hG_adj : G.Adj a₁ b₁ := w₁.adj_of_mem_edges he₁
  have hH'_adj : H'.Adj ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩ := by
    rw [hH'_def, induce_adj]; exact Or.inl hG_adj
  
  have h_avoid_e3 : ∀ (u v : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)),
      ∃ w : H'.Walk u v,
        s(⟨a₃, ha₃_S⟩, ⟨b₃, hb₃_S⟩) ∉ w.edges := fun u v =>
    edge_not_bridge_in_induce_unionSupport_lifted_right
      G w₁ w₂ hp₁ hp₂ hne hw₁_avoid hw₂_avoid he₃ ha₃_S hb₃_S u v
  
  
  have h_lift_inl_inl : ∀ (u v : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)),
      ∃ w : (H'.subdivideEdge ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).Walk
              (Sum.inl u) (Sum.inl v),
        s(Sum.inl (⟨a₃, ha₃_S⟩ :
            (↑(G.unionSupportFinset w₁ w₂) : Set V)),
          Sum.inl ⟨b₃, hb₃_S⟩) ∉ w.edges := by
    intro u v
    obtain ⟨w0, h_w0_avoid⟩ := h_avoid_e3 u v
    let wp := w0.bypass
    have h_wp_path : wp.IsPath := w0.bypass_isPath
    have h_wp_avoid : s(⟨a₃, ha₃_S⟩, ⟨b₃, hb₃_S⟩) ∉ wp.edges := by
      intro h
      exact h_w0_avoid (w0.edges_bypass_subset h)
    obtain ⟨w', h_w'_avoid⟩ := Walk.liftSubdivide_avoiding_edge
      (G := H') (a := ⟨a₁, ha₁_S⟩) (b := ⟨b₁, hb₁_S⟩)
      (c := ⟨a₃, ha₃_S⟩) (d := ⟨b₃, hb₃_S⟩) hH'_adj wp h_wp_path h_wp_avoid
    refine ⟨w', ?_⟩
    
    intro h_in
    apply h_w'_avoid
    rw [Sym2.map_mk]
    exact h_in
  
  have h_a1_inr : (H'.subdivideEdge ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).Adj
      (Sum.inl (⟨a₁, ha₁_S⟩ : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)))
      (Sum.inr ()) :=
    (subdivideEdge_adj_inr_a H' ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).symm
  have h_inr_b1 : (H'.subdivideEdge ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).Adj
      (Sum.inr ())
      (Sum.inl (⟨b₁, hb₁_S⟩ : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V))) :=
    subdivideEdge_adj_inr_b H' ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩
  
  cases x' with
  | inl x₀ =>
    cases y' with
    | inl y₀ =>
      
      exact h_lift_inl_inl x₀ y₀
    | inr ty =>
      obtain rfl : ty = () := by cases ty; rfl
      
      obtain ⟨w_lift, h_w_lift_avoid⟩ := h_lift_inl_inl x₀ ⟨a₁, ha₁_S⟩
      refine ⟨w_lift.append (Walk.cons h_a1_inr Walk.nil), ?_⟩
      intro h_in
      rw [Walk.edges_append, Walk.edges_cons, Walk.edges_nil] at h_in
      rcases List.mem_append.mp h_in with h_in_lift | h_in_tail
      · exact h_w_lift_avoid h_in_lift
      · 
        rcases List.mem_singleton.mp h_in_tail with h_eq
        rw [Sym2.eq_iff] at h_eq
        rcases h_eq with ⟨_, h_eq⟩ | ⟨h_eq, _⟩
        · cases h_eq
        · cases h_eq
  | inr tx =>
    obtain rfl : tx = () := by cases tx; rfl
    cases y' with
    | inl y₀ =>
      
      obtain ⟨w_lift, h_w_lift_avoid⟩ := h_lift_inl_inl ⟨a₁, ha₁_S⟩ y₀
      refine ⟨Walk.cons h_a1_inr.symm w_lift, ?_⟩
      intro h_in
      rw [Walk.edges_cons] at h_in
      rcases List.mem_cons.mp h_in with h_eq | h_in_lift
      · 
        rw [Sym2.eq_iff] at h_eq
        rcases h_eq with ⟨h_eq, _⟩ | ⟨_, h_eq⟩
        · cases h_eq
        · cases h_eq
      · exact h_w_lift_avoid h_in_lift
    | inr ty =>
      obtain rfl : ty = () := by cases ty; rfl
      
      refine ⟨Walk.nil, ?_⟩
      intro h_in
      rw [Walk.edges_nil] at h_in
      exact List.not_mem_nil h_in

end EdgeNotBridgeAfterSubdivide










section SubdivideTwice

variable [Fintype V] [DecidableRel G.Adj]






private theorem subdivide_e3_in_subdivided_H'_no_cut_vertex
    {a b : V} (w₁ w₂ : G.Walk a b) (hp₁ : w₁.IsPath) (hp₂ : w₂.IsPath)
    (hne : a ≠ b)
    (hw₁_avoid : s(a, b) ∉ w₁.edges) (hw₂_avoid : s(a, b) ∉ w₂.edges)
    {a₁ b₁ : V} (he₁ : s(a₁, b₁) ∈ w₁.edges)
    (ha₁_S : a₁ ∈ G.unionSupportFinset w₁ w₂)
    (hb₁_S : b₁ ∈ G.unionSupportFinset w₁ w₂)
    {a₃ b₃ : V} (he₃ : s(a₃, b₃) ∈ w₂.edges)
    (ha₃_S : a₃ ∈ G.unionSupportFinset w₁ w₂)
    (hb₃_S : b₃ ∈ G.unionSupportFinset w₁ w₂)
    (hne13 : s(a₁, b₁) ≠ s(a₃, b₃))
    (z' x' y' : ((↑(G.unionSupportFinset w₁ w₂) : Set V) ⊕ Unit) ⊕ Unit)
    (hxz : x' ≠ z') (hyz : y' ≠ z') :
    ∃ w : ((((G ⊔ SimpleGraph.edge a b).induce
        (↑(G.unionSupportFinset w₁ w₂) : Set V)).subdivideEdge
        ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩).subdivideEdge
        (Sum.inl (⟨a₃, ha₃_S⟩ :
          (↑(G.unionSupportFinset w₁ w₂) : Set V)))
        (Sum.inl ⟨b₃, hb₃_S⟩)).Walk x' y',
      ∀ q ∈ w.support, q ≠ z' := by
  
  set H' : SimpleGraph (↑(G.unionSupportFinset w₁ w₂) : Set V) :=
    (G ⊔ SimpleGraph.edge a b).induce
      (↑(G.unionSupportFinset w₁ w₂) : Set V) with hH'_def
  set H'' : SimpleGraph
      ((↑(G.unionSupportFinset w₁ w₂) : Set V) ⊕ Unit) :=
    H'.subdivideEdge ⟨a₁, ha₁_S⟩ ⟨b₁, hb₁_S⟩ with hH''_def
  
  have hG_adj₃ : G.Adj a₃ b₃ := w₂.adj_of_mem_edges he₃
  have hH'_adj₃ : H'.Adj ⟨a₃, ha₃_S⟩ ⟨b₃, hb₃_S⟩ := by
    rw [hH'_def, induce_adj]; exact Or.inl hG_adj₃
  
  
  have hH'_ne13 : s((⟨a₁, ha₁_S⟩ : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)),
        ⟨b₁, hb₁_S⟩) ≠ s(⟨a₃, ha₃_S⟩, ⟨b₃, hb₃_S⟩) := by
    intro h_eq
    rw [Sym2.eq_iff] at h_eq
    apply hne13
    rw [Sym2.eq_iff]
    rcases h_eq with ⟨h_a, h_b⟩ | ⟨h_a, h_b⟩
    · left; exact ⟨congrArg Subtype.val h_a, congrArg Subtype.val h_b⟩
    · right; exact ⟨congrArg Subtype.val h_a, congrArg Subtype.val h_b⟩
  
  have hH''_adj : H''.Adj
      (Sum.inl (⟨a₃, ha₃_S⟩ : ↥(↑(G.unionSupportFinset w₁ w₂) : Set V)))
      (Sum.inl ⟨b₃, hb₃_S⟩) :=
    subdivideEdge_adj_inl_inl_of_ne (G := H')
      (a := ⟨a₁, ha₁_S⟩) (b := ⟨b₁, hb₁_S⟩) hH'_adj₃ hH'_ne13.symm
  
  have h_no_cut : ∀ (z x y : (↑(G.unionSupportFinset w₁ w₂) : Set V) ⊕ Unit),
      x ≠ z → y ≠ z →
      ∃ w : H''.Walk x y, ∀ q ∈ w.support, q ≠ z := fun z x y hxz hyz =>
    subdivide_e1_in_induce_no_cut_vertex
      G w₁ w₂ hp₁ hp₂ hne hw₁_avoid hw₂_avoid he₁ ha₁_S hb₁_S z x y hxz hyz
  
  have h_not_bridge : ∀ (x y : (↑(G.unionSupportFinset w₁ w₂) : Set V) ⊕ Unit),
      ∃ w : H''.Walk x y,
        s(Sum.inl (⟨a₃, ha₃_S⟩ :
            (↑(G.unionSupportFinset w₁ w₂) : Set V)),
          Sum.inl ⟨b₃, hb₃_S⟩) ∉ w.edges := fun x y =>
    edge_not_bridge_in_subdivided_H'
      G w₁ w₂ hp₁ hp₂ hne hw₁_avoid hw₂_avoid he₁ ha₁_S hb₁_S
      he₃ ha₃_S hb₃_S x y
  
  exact subdivideEdge_walk_avoiding (G := H'')
    (Sum.inl ⟨a₃, ha₃_S⟩) (Sum.inl ⟨b₃, hb₃_S⟩)
    hH''_adj h_no_cut h_not_bridge z' x' y' hxz hyz

end SubdivideTwice











end Whitney








def SameBlockSetoid : Setoid (Sym2 V) := ⟨G.SameBlock, SameBlock.equivalence G⟩




def Block : Type _ := Quotient G.SameBlockSetoid


def blockOf (e : Sym2 V) : G.Block := Quotient.mk G.SameBlockSetoid e



theorem blockOf_eq_iff {e₁ e₂ : Sym2 V} :
    G.blockOf e₁ = G.blockOf e₂ ↔ G.SameBlock e₁ e₂ :=
  Quotient.eq (r := G.SameBlockSetoid)








section Partition

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in




noncomputable def blocks : Finset G.Block :=
  G.edgeFinset.image G.blockOf

open Classical in

noncomputable def edgesInBlock (b : G.Block) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => G.blockOf e = b)

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem card_edgeFinset_eq_sum_blocks :
    G.edgeFinset.card = ∑ b ∈ G.blocks, (G.edgesInBlock b).card := by
  classical
  have hmaps : Set.MapsTo G.blockOf (↑G.edgeFinset) (↑G.blocks) := by
    intro e he
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  exact Finset.card_eq_sum_card_fiberwise hmaps

end Partition









section BlockSubgraph

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in


noncomputable def blockSubgraph (b : G.Block) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.edgesInBlock b : Set (Sym2 V))

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem blockSubgraph_le (b : G.Block) : G.blockSubgraph b ≤ G := by
  classical
  have hsub : (G.edgesInBlock b : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have he' : e ∈ G.edgesInBlock b := he
    have : e ∈ G.edgeFinset := (Finset.mem_filter.mp he').1
    exact (mem_edgeFinset).mp this
  calc G.blockSubgraph b
      = SimpleGraph.fromEdgeSet (G.edgesInBlock b : Set (Sym2 V)) := rfl
    _ ≤ SimpleGraph.fromEdgeSet G.edgeSet := SimpleGraph.fromEdgeSet_mono hsub
    _ = G := SimpleGraph.fromEdgeSet_edgeSet G

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem blockSubgraph_isPlanar (hplanar : G.IsPlanar) (b : G.Block) :
    (G.blockSubgraph b).IsPlanar :=
  hplanar.mono (G.blockSubgraph_le b)

end BlockSubgraph







section BlockVertices

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in

noncomputable def blockVertices (b : G.Block) : Finset V :=
  (G.edgesInBlock b).biUnion Sym2.toFinset

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in


theorem mem_blockVertices_iff {b : G.Block} {v : V} :
    v ∈ G.blockVertices b ↔ ∃ e ∈ G.edgesInBlock b, v ∈ e := by
  classical
  unfold blockVertices
  simp [Finset.mem_biUnion, Sym2.mem_toFinset]

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in




theorem card_blockVertices_le (b : G.Block) :
    (G.blockVertices b).card ≤ 2 * (G.edgesInBlock b).card := by
  classical
  unfold blockVertices
  refine (Finset.card_biUnion_le).trans ?_
  calc ∑ e ∈ G.edgesInBlock b, e.toFinset.card
      ≤ ∑ _ ∈ G.edgesInBlock b, 2 := by
          refine Finset.sum_le_sum ?_
          intro e _
          by_cases h : e.IsDiag
          · exact (Sym2.card_toFinset_of_isDiag e h).le.trans (by norm_num)
          · exact (Sym2.card_toFinset_of_not_isDiag e h).le
    _ = 2 * (G.edgesInBlock b).card := by
          rw [Finset.sum_const, smul_eq_mul]
          ring

end BlockVertices











section DoubleCount

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in

noncomputable def blocksAt (v : V) : Finset G.Block :=
  G.blocks.filter (fun b => v ∈ G.blockVertices b)

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in
theorem mem_blocksAt_iff {v : V} {b : G.Block} :
    b ∈ G.blocksAt v ↔ b ∈ G.blocks ∧ v ∈ G.blockVertices b := by
  classical
  unfold blocksAt
  exact Finset.mem_filter

open Classical in
omit [DecidableRel G.Adj] in





theorem sum_card_blockVertices_eq :
    ∑ b ∈ G.blocks, (G.blockVertices b).card =
    ∑ v : V, (G.blocksAt v).card := by
  classical
  
  have hLHS : ∀ b : G.Block,
      (G.blockVertices b).card =
        ∑ v : V, (if v ∈ G.blockVertices b then 1 else 0) := by
    intro b
    conv_lhs => rw [← Finset.filter_univ_mem (G.blockVertices b)]
    rw [Finset.card_filter]
  
  have hRHS : ∀ v : V,
      (G.blocksAt v).card =
        ∑ b ∈ G.blocks, (if v ∈ G.blockVertices b then 1 else 0) := by
    intro v
    unfold blocksAt
    rw [Finset.card_filter]
  
  calc ∑ b ∈ G.blocks, (G.blockVertices b).card
      = ∑ b ∈ G.blocks, ∑ v : V,
          (if v ∈ G.blockVertices b then 1 else 0) := by
        exact Finset.sum_congr rfl (fun b _ => hLHS b)
    _ = ∑ v : V, ∑ b ∈ G.blocks,
          (if v ∈ G.blockVertices b then 1 else 0) := Finset.sum_comm
    _ = ∑ v : V, (G.blocksAt v).card :=
        (Finset.sum_congr rfl (fun v _ => (hRHS v).symm))

end DoubleCount
















section CutVertexMultiplicity

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in


noncomputable def nontrivBlockVertices : Finset V :=
  Finset.univ.filter (fun v => 1 ≤ (G.blocksAt v).card)

open Classical in




noncomputable def cutVertexMultiplicity (v : V) : ℕ :=
  (G.blocksAt v).card - 1

open Classical in
omit [DecidableRel G.Adj] in


theorem card_blocksAt_eq_one_add_mult {v : V}
    (hv : v ∈ G.nontrivBlockVertices) :
    (G.blocksAt v).card = 1 + G.cutVertexMultiplicity v := by
  classical
  unfold cutVertexMultiplicity
  have h1 : 1 ≤ (G.blocksAt v).card := by
    unfold nontrivBlockVertices at hv
    exact (Finset.mem_filter.mp hv).2
  omega

open Classical in
omit [DecidableRel G.Adj] in


theorem card_blocksAt_eq_zero_of_not_mem {v : V}
    (hv : v ∉ G.nontrivBlockVertices) :
    (G.blocksAt v).card = 0 := by
  classical
  unfold nontrivBlockVertices at hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le,
             Nat.lt_one_iff] at hv
  exact hv

open Classical in
omit [DecidableRel G.Adj] in

theorem cutVertexMultiplicity_eq_zero_of_not_mem {v : V}
    (hv : v ∉ G.nontrivBlockVertices) :
    G.cutVertexMultiplicity v = 0 := by
  classical
  unfold cutVertexMultiplicity
  rw [G.card_blocksAt_eq_zero_of_not_mem hv]

open Classical in
omit [DecidableRel G.Adj] in





theorem sum_card_blocksAt_eq_card_nontriv_add_sum_mult :
    ∑ v : V, (G.blocksAt v).card =
    G.nontrivBlockVertices.card + ∑ v : V, G.cutVertexMultiplicity v := by
  classical
  
  have hsplit : ∀ v : V,
      (G.blocksAt v).card =
        (if v ∈ G.nontrivBlockVertices then 1 else 0) +
        G.cutVertexMultiplicity v := by
    intro v
    by_cases hv : v ∈ G.nontrivBlockVertices
    · simp [hv, G.card_blocksAt_eq_one_add_mult hv]
    · simp [hv, G.card_blocksAt_eq_zero_of_not_mem hv,
            G.cutVertexMultiplicity_eq_zero_of_not_mem hv]
  calc ∑ v : V, (G.blocksAt v).card
      = ∑ v : V, ((if v ∈ G.nontrivBlockVertices then 1 else 0) +
                  G.cutVertexMultiplicity v) := by
        exact Finset.sum_congr rfl (fun v _ => hsplit v)
    _ = (∑ v : V, if v ∈ G.nontrivBlockVertices then 1 else 0) +
          ∑ v : V, G.cutVertexMultiplicity v := Finset.sum_add_distrib
    _ = G.nontrivBlockVertices.card + ∑ v : V, G.cutVertexMultiplicity v := by
        congr 1
        rw [← Finset.card_filter, Finset.filter_univ_mem]

open Classical in
omit [DecidableRel G.Adj] in















theorem sum_card_blockVertices_eq_card_nontriv_add_sum_mult :
    ∑ b ∈ G.blocks, (G.blockVertices b).card =
    G.nontrivBlockVertices.card + ∑ v : V, G.cutVertexMultiplicity v := by
  rw [G.sum_card_blockVertices_eq, G.sum_card_blocksAt_eq_card_nontriv_add_sum_mult]

end CutVertexMultiplicity









section BlockSubgraphEdges

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in



theorem edgeSet_blockSubgraph (b : G.Block) :
    (G.blockSubgraph b).edgeSet = (G.edgesInBlock b : Set (Sym2 V)) := by
  classical
  unfold blockSubgraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  simp only [Set.mem_diff, Sym2.mem_diagSet]
  constructor
  · intro ⟨he, _⟩; exact he
  · intro he
    refine ⟨he, ?_⟩
    
    have he' : e ∈ G.edgesInBlock b := he
    have heG : e ∈ G.edgeSet :=
      (mem_edgeFinset).mp (Finset.mem_filter.mp he').1
    exact G.not_isDiag_of_mem_edgeSet heG

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in



theorem card_edgeFinset_blockSubgraph (b : G.Block) :
    (G.blockSubgraph b).edgeFinset.card = (G.edgesInBlock b).card := by
  classical
  
  apply Finset.card_bij (fun e _ => e) (fun e he => ?_)
    (fun _ _ _ _ heq => heq) (fun e he => ⟨e, ?_, rfl⟩)
  · 
    rw [mem_edgeFinset] at he
    have : e ∈ (G.edgesInBlock b : Set (Sym2 V)) :=
      (G.edgeSet_blockSubgraph b) ▸ he
    exact this
  · 
    rw [mem_edgeFinset]
    have : e ∈ (G.edgesInBlock b : Set (Sym2 V)) := he
    exact (G.edgeSet_blockSubgraph b).symm ▸ this

end BlockSubgraphEdges












section BlockDecomposition

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Fintype G.edgeSet]

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in





theorem block_decomposition :
    (∀ b ∈ G.blocks, (G.edgesInBlock b).Nonempty) ∧
    (G.blocks.biUnion G.edgesInBlock = G.edgeFinset) ∧
    (∀ b₁ ∈ G.blocks, ∀ b₂ ∈ G.blocks,
        b₁ ≠ b₂ → Disjoint (G.edgesInBlock b₁) (G.edgesInBlock b₂)) := by
  refine ⟨?_, ?_, ?_⟩
  
  · intro b hb
    simp only [SimpleGraph.blocks, Finset.mem_image] at hb
    obtain ⟨e, he, rfl⟩ := hb
    exact ⟨e, by simp [SimpleGraph.edgesInBlock, he]⟩
  
  · ext e
    simp only [Finset.mem_biUnion, SimpleGraph.blocks, SimpleGraph.edgesInBlock,
      Finset.mem_image, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rintro ⟨_b, _, he, _⟩; exact he
    · intro he
      refine ⟨G.blockOf e, ⟨e, he, rfl⟩, he, rfl⟩
  
  · intro b₁ _ b₂ _ hne
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [SimpleGraph.edgesInBlock, Finset.mem_filter] at he1 he2
    exact hne (he1.2.symm.trans he2.2)

open Classical in
omit [Fintype V] [DecidableRel G.Adj] in





theorem sup_blockSubgraph_eq :
    G.blocks.sup G.blockSubgraph = G := by
  apply le_antisymm
  · apply Finset.sup_le
    intro b hb
    exact G.blockSubgraph_le b
  · intro v w hvw
    have heG : s(v, w) ∈ G.edgeFinset := mem_edgeFinset.mpr hvw
    have heUnion : s(v, w) ∈ G.blocks.biUnion G.edgesInBlock := by
      rw [G.block_decomposition.2.1]
      exact heG
    obtain ⟨b, hb, heb⟩ := Finset.mem_biUnion.mp heUnion
    have hblock : (G.blockSubgraph b).Adj v w := by
      rw [← mem_edgeSet, G.edgeSet_blockSubgraph]
      exact heb
    exact (Finset.le_sup (s := G.blocks) (f := G.blockSubgraph) hb) hblock

end BlockDecomposition

end SimpleGraph
