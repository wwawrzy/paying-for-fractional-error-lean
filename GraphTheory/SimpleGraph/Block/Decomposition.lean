/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Wawrzyniak
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

/-!
# Edge subdivision and walks

For a simple graph, this module defines subdivision of one edge by a fresh vertex. It characterizes adjacency in the subdivided graph and develops the lifting and projection of walks, paths, and cycles. The results also handle walks that avoid the new vertex or the subdivided edge.
-/

namespace SimpleGraph

variable {V : Type*}














def subdivideEdge (G : SimpleGraph V) (a b : V) : SimpleGraph (V ⊕ Unit) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl w => G.Adj u w ∧ s(u, w) ≠ s(a, b)
    | Sum.inl u, Sum.inr _ => u = a ∨ u = b
    | Sum.inr _, Sum.inl w => w = a ∨ w = b
    | Sum.inr _, Sum.inr _ => False
  symm := by
    intro x y h
    match x, y with
    | Sum.inl u, Sum.inl w =>
        refine ⟨h.1.symm, ?_⟩
        rw [Sym2.eq_swap]
        exact h.2
    | Sum.inl u, Sum.inr _ => exact h
    | Sum.inr _, Sum.inl w => exact h
    | Sum.inr _, Sum.inr _ => exact h.elim
  loopless := by
    refine ⟨?_⟩
    intro x h
    match x, h with
    | Sum.inl u, h => exact G.loopless.irrefl u h.1
    | Sum.inr _, h => exact h.elim



section Lemmas

variable (G : SimpleGraph V) (a b : V)



@[simp] lemma subdivideEdge_adj_inl_inl (u w : V) :
    (G.subdivideEdge a b).Adj (Sum.inl u) (Sum.inl w) ↔
      G.Adj u w ∧ s(u, w) ≠ s(a, b) := Iff.rfl



@[simp] lemma subdivideEdge_adj_inl_inr (u : V) (t : Unit) :
    (G.subdivideEdge a b).Adj (Sum.inl u) (Sum.inr t) ↔ u = a ∨ u = b := Iff.rfl



@[simp] lemma subdivideEdge_adj_inr_inl (t : Unit) (w : V) :
    (G.subdivideEdge a b).Adj (Sum.inr t) (Sum.inl w) ↔ w = a ∨ w = b := Iff.rfl



@[simp] lemma subdivideEdge_adj_inr_inr (s t : Unit) :
    ¬ (G.subdivideEdge a b).Adj (Sum.inr s) (Sum.inr t) := by
  intro h
  exact h.elim



lemma subdivideEdge_not_adj_a_b :
    ¬ (G.subdivideEdge a b).Adj (Sum.inl a) (Sum.inl b) := by
  intro h
  exact h.2 rfl


lemma subdivideEdge_adj_inr_a :
    (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl a) :=
  Or.inl rfl


lemma subdivideEdge_adj_inr_b :
    (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl b) :=
  Or.inr rfl



lemma subdivideEdge_adj_inr_iff (t : Unit) (y : V ⊕ Unit) :
    (G.subdivideEdge a b).Adj (Sum.inr t) y ↔
      (∃ w : V, y = Sum.inl w ∧ (w = a ∨ w = b)) := by
  cases y with
  | inl w =>
      simp [subdivideEdge, Sum.inl.injEq]
  | inr _ =>
      simp [subdivideEdge]



lemma subdivideEdge_adj_inl_inl_of_ne {u w : V}
    (hG : G.Adj u w) (hne : s(u, w) ≠ s(a, b)) :
    (G.subdivideEdge a b).Adj (Sum.inl u) (Sum.inl w) :=
  ⟨hG, hne⟩

end Lemmas






instance subdivideEdge_decidableAdj
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (a b : V) :
    DecidableRel (G.subdivideEdge a b).Adj := by
  intro x y
  match x, y with
  | Sum.inl u, Sum.inl w =>
      change Decidable (G.Adj u w ∧ s(u, w) ≠ s(a, b))
      exact instDecidableAnd
  | Sum.inl _, Sum.inr _ =>
      change Decidable (_ ∨ _)
      exact instDecidableOr
  | Sum.inr _, Sum.inl _ =>
      change Decidable (_ ∨ _)
      exact instDecidableOr
  | Sum.inr _, Sum.inr _ =>
      change Decidable False
      exact instDecidableFalse






















section Lift

variable (G : SimpleGraph V) (a b : V)




def subdivideEdge.inlHom :
    G.deleteEdges {s(a, b)} →g G.subdivideEdge a b where
  toFun := Sum.inl
  map_rel' := by
    intro u w h
    
    rw [SimpleGraph.deleteEdges_adj] at h
    obtain ⟨hG, hne⟩ := h
    
    change G.Adj u w ∧ s(u, w) ≠ s(a, b)
    refine ⟨hG, ?_⟩
    simpa using hne


@[simp] lemma subdivideEdge.inlHom_apply (u : V) :
    (subdivideEdge.inlHom G a b) u = Sum.inl u := rfl



lemma subdivideEdge.inlHom_injective :
    Function.Injective (subdivideEdge.inlHom G a b) :=
  Sum.inl_injective



variable {G a b}







def Walk.liftSubdivide {u v : V} (w : G.Walk u v)
    (h_avoid : s(a, b) ∉ w.edges) :
    (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v) :=
  Walk.map (subdivideEdge.inlHom G a b)
    (w.toDeleteEdges {s(a, b)} (fun e he hmem => by
      simp only [Set.mem_singleton_iff] at hmem
      exact h_avoid (hmem ▸ he)))



private lemma Walk.support_toDeleteEdges_aux {u v : V} (s : Set (Sym2 V))
    (w : G.Walk u v) (hw : ∀ e ∈ w.edges, e ∉ s) :
    (w.toDeleteEdges s hw).support = w.support := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.toDeleteEdges_cons, Walk.support_cons]
    rw [ih]


@[simp] theorem Walk.liftSubdivide_support {u v : V} (w : G.Walk u v)
    (h_avoid : s(a, b) ∉ w.edges) :
    (w.liftSubdivide h_avoid).support = w.support.map Sum.inl := by
  change (Walk.map (subdivideEdge.inlHom G a b) _).support = _
  rw [Walk.support_map, Walk.support_toDeleteEdges_aux]
  rfl


private lemma Walk.length_toDeleteEdges_aux {u v : V} (s : Set (Sym2 V))
    (w : G.Walk u v) (hw : ∀ e ∈ w.edges, e ∉ s) :
    (w.toDeleteEdges s hw).length = w.length := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.toDeleteEdges_cons, Walk.length_cons]
    rw [ih]


@[simp] theorem Walk.liftSubdivide_length {u v : V} (w : G.Walk u v)
    (h_avoid : s(a, b) ∉ w.edges) :
    (w.liftSubdivide h_avoid).length = w.length := by
  change (Walk.map (subdivideEdge.inlHom G a b) _).length = _
  rw [Walk.length_map, Walk.length_toDeleteEdges_aux]


private lemma Walk.edges_toDeleteEdges_aux {u v : V} (s : Set (Sym2 V))
    (w : G.Walk u v) (hw : ∀ e ∈ w.edges, e ∉ s) :
    (w.toDeleteEdges s hw).edges = w.edges := by
  induction w with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.toDeleteEdges_cons, Walk.edges_cons]
    rw [ih]


theorem Walk.liftSubdivide_isPath {u v : V} {w : G.Walk u v}
    (h_avoid : s(a, b) ∉ w.edges) (hp : w.IsPath) :
    (w.liftSubdivide h_avoid).IsPath := by
  change (Walk.map (subdivideEdge.inlHom G a b) _).IsPath
  apply Walk.map_isPath_of_injective (subdivideEdge.inlHom_injective G a b)
  rw [Walk.isPath_def, Walk.support_toDeleteEdges_aux]
  exact hp.support_nodup


@[simp] theorem Walk.liftSubdivide_edges {u v : V} (w : G.Walk u v)
    (h_avoid : s(a, b) ∉ w.edges) :
    (w.liftSubdivide h_avoid).edges = w.edges.map (Sym2.map Sum.inl) := by
  change (Walk.map (subdivideEdge.inlHom G a b) _).edges = _
  rw [Walk.edges_map, Walk.edges_toDeleteEdges_aux]
  rfl




theorem Walk.liftSubdivide_support_inl {u v : V} (w : G.Walk u v)
    (h_avoid : s(a, b) ∉ w.edges) :
    ∀ x ∈ (w.liftSubdivide h_avoid).support, ∃ y : V, x = Sum.inl y := by
  intro x hx
  rw [Walk.liftSubdivide_support, List.mem_map] at hx
  obtain ⟨y, _, hy⟩ := hx
  exact ⟨y, hy.symm⟩



theorem Walk.liftSubdivide_inr_not_mem {u v : V} (w : G.Walk u v)
    (h_avoid : s(a, b) ∉ w.edges) (t : Unit) :
    Sum.inr t ∉ (w.liftSubdivide h_avoid).support := by
  intro hin
  obtain ⟨y, hy⟩ := Walk.liftSubdivide_support_inl w h_avoid _ hin
  cases hy

















private lemma Walk.exists_split_at_edge_local
    {G : SimpleGraph V} {u v a b : V} (hab : G.Adj a b) :
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
    · rcases Walk.exists_split_at_edge_local hab p h_in with
        ⟨w₁, w₂, hp_eq, hedges⟩ | ⟨w₁, w₂, hp_eq, hedges⟩
      · exact .inl ⟨.cons h0 w₁, w₂, by rw [hp_eq]; rfl,
          by simp [Walk.edges_cons, hedges]⟩
      · exact .inr ⟨.cons h0 w₁, w₂, by rw [hp_eq]; rfl,
          by simp [Walk.edges_cons, hedges]⟩









theorem Walk.liftSubdivide_through_of_trail {u v : V}
    (hab : G.Adj a b) (w : G.Walk u v) (h_trail : w.IsTrail)
    (h_through : s(a, b) ∈ w.edges) :
    ∃ w'' : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v),
      Sum.inr () ∈ w''.support ∧ w''.length = w.length + 1 := by
  
  rcases Walk.exists_split_at_edge_local (G := G) hab w h_through with
    ⟨w₁, w₂, hw_eq, hedges⟩ | ⟨w₁, w₂, hw_eq, hedges⟩
  · 
    
    have hnodup : w.edges.Nodup := h_trail.edges_nodup
    rw [hedges] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨hnd₁, hnd_cons, hdisj⟩ := hnodup
    simp only [List.nodup_cons] at hnd_cons
    obtain ⟨hne₁, _hnd₂⟩ := hnd_cons
    have h_avoid₁ : s(a, b) ∉ w₁.edges := fun h => hdisj _ h _ (by simp) rfl
    have h_avoid₂ : s(a, b) ∉ w₂.edges := hne₁
    
    let lw₁ := w₁.liftSubdivide h_avoid₁
    
    let lw₂ := w₂.liftSubdivide h_avoid₂
    
    have h_ar : (G.subdivideEdge a b).Adj (Sum.inl a) (Sum.inr ()) :=
      (subdivideEdge_adj_inr_a G a b).symm
    
    have h_rb : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl b) :=
      subdivideEdge_adj_inr_b G a b
    
    refine ⟨lw₁.append (Walk.cons h_ar (Walk.cons h_rb lw₂)), ?_, ?_⟩
    · 
      
      
      rw [Walk.support_append]
      simp [Walk.support_cons]
    · 
      simp only [Walk.length_append, Walk.length_cons]
      rw [Walk.liftSubdivide_length, Walk.liftSubdivide_length]
      rw [hw_eq, Walk.length_append, Walk.length_cons]
      ring
  · 
    have hnodup : w.edges.Nodup := h_trail.edges_nodup
    rw [hedges] at hnodup
    rw [List.nodup_append] at hnodup
    obtain ⟨hnd₁, hnd_cons, hdisj⟩ := hnodup
    simp only [List.nodup_cons] at hnd_cons
    obtain ⟨hne₁, _hnd₂⟩ := hnd_cons
    
    have h_avoid₂ : s(a, b) ∉ w₂.edges := by
      rw [Sym2.eq_swap]; exact hne₁
    have h_avoid₁ : s(a, b) ∉ w₁.edges := by
      intro h
      exact hdisj _ h _ (by simp [Sym2.eq_swap]) rfl
    let lw₁ := w₁.liftSubdivide h_avoid₁ 
    let lw₂ := w₂.liftSubdivide h_avoid₂ 
    
    have h_br : (G.subdivideEdge a b).Adj (Sum.inl b) (Sum.inr ()) :=
      (subdivideEdge_adj_inr_b G a b).symm
    
    have h_ra : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl a) :=
      subdivideEdge_adj_inr_a G a b
    refine ⟨lw₁.append (Walk.cons h_br (Walk.cons h_ra lw₂)), ?_, ?_⟩
    · rw [Walk.support_append]
      simp [Walk.support_cons]
    · simp only [Walk.length_append, Walk.length_cons]
      rw [Walk.liftSubdivide_length, Walk.liftSubdivide_length]
      rw [hw_eq, Walk.length_append, Walk.length_cons]
      ring

end Lift



















section Collapse

variable {G : SimpleGraph V} {a b : V}





noncomputable def Walk.projectInl :
    {u v : V} → (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v)) →
    (∀ x ∈ w.support, ∃ y : V, x = Sum.inl y) → G.Walk u v
  | _, _, .nil, _ => .nil
  | u, v, .cons (v := Sum.inl y) hadj p, h_inl =>
      have hadj_G : G.Adj u y ∧ s(u, y) ≠ s(a, b) := by
        rw [subdivideEdge_adj_inl_inl] at hadj; exact hadj
      .cons hadj_G.1 (Walk.projectInl p (fun z hz =>
        h_inl z (by
          rw [Walk.support_cons]
          exact List.mem_cons_of_mem _ hz)))
  | _, _, .cons (v := Sum.inr ()) _ _, h_inl => by
      exfalso
      obtain ⟨y, hy⟩ := h_inl (Sum.inr ()) (by
        simp [Walk.support_cons])
      cases hy



theorem Walk.projectInl_support :
    {u v : V} → (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v)) →
    (h : ∀ x ∈ w.support, ∃ y : V, x = Sum.inl y) →
    (w.projectInl h).support.map Sum.inl = w.support
  | _, _, .nil, _ => by simp [Walk.projectInl]
  | u, v, .cons (v := Sum.inl y) hadj p, h_inl => by
      simp only [Walk.projectInl, Walk.support_cons, List.map_cons]
      exact congr_arg _ (Walk.projectInl_support p _)
  | _, _, .cons (v := Sum.inr ()) _ _, h_inl => by
      exfalso
      obtain ⟨y, hy⟩ := h_inl (Sum.inr ()) (by
        simp [Walk.support_cons])
      cases hy


theorem Walk.projectInl_length :
    {u v : V} → (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v)) →
    (h : ∀ x ∈ w.support, ∃ y : V, x = Sum.inl y) →
    (w.projectInl h).length = w.length
  | _, _, .nil, _ => by simp [Walk.projectInl]
  | u, v, .cons (v := Sum.inl y) hadj p, h_inl => by
      simp only [Walk.projectInl, Walk.length_cons]
      exact congr_arg (· + 1) (Walk.projectInl_length p _)
  | _, _, .cons (v := Sum.inr ()) _ _, h_inl => by
      exfalso
      obtain ⟨y, hy⟩ := h_inl (Sum.inr ()) (by
        simp [Walk.support_cons])
      cases hy



theorem Walk.projectInl_edges :
    {u v : V} → (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v)) →
    (h : ∀ x ∈ w.support, ∃ y : V, x = Sum.inl y) →
    (w.projectInl h).edges.map (Sym2.map Sum.inl) = w.edges
  | _, _, .nil, _ => by simp [Walk.projectInl]
  | u, v, .cons (v := Sum.inl y) hadj p, h_inl => by
      simp only [Walk.projectInl, Walk.edges_cons, List.map_cons, Sym2.map_mk]
      exact congr_arg _ (Walk.projectInl_edges p _)
  | _, _, .cons (v := Sum.inr ()) _ _, h_inl => by
      exfalso
      obtain ⟨y, hy⟩ := h_inl (Sum.inr ()) (by
        simp [Walk.support_cons])
      cases hy



theorem Walk.projectInl_isPath
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h : ∀ x ∈ w.support, ∃ y : V, x = Sum.inl y) (hp : w.IsPath) :
    (w.projectInl h).IsPath := by
  rw [Walk.isPath_def]
  have hsup : (w.projectInl h).support.map Sum.inl = w.support :=
    Walk.projectInl_support w h
  have : ((w.projectInl h).support.map Sum.inl).Nodup := hsup ▸ hp.support_nodup
  exact List.Nodup.of_map _ this






private lemma Walk.head_inr_adj_inl
    {y : V ⊕ Unit} (hadj : (G.subdivideEdge a b).Adj (Sum.inr ()) y) :
    ∃ w : V, y = Sum.inl w ∧ (w = a ∨ w = b) := by
  rw [subdivideEdge_adj_inr_iff] at hadj
  exact hadj




private lemma Walk.tail_inr_adj_inl
    {x : V ⊕ Unit} (hadj : (G.subdivideEdge a b).Adj x (Sum.inr ())) :
    ∃ w : V, x = Sum.inl w ∧ (w = a ∨ w = b) := by
  have := Walk.head_inr_adj_inl (a := a) (b := b) (y := x) hadj.symm
  exact this






private lemma Walk.isPath_inl_to_inr_split
    {x' : V} (rest : (G.subdivideEdge a b).Walk (Sum.inl x') (Sum.inr ()))
    (h_path : rest.IsPath) :
    ∃ (y' : V) (p : (G.subdivideEdge a b).Walk (Sum.inl x') (Sum.inl y'))
      (h_last : (G.subdivideEdge a b).Adj (Sum.inl y') (Sum.inr ())),
      rest = p.append (Walk.cons h_last .nil) ∧
      (y' = a ∨ y' = b) ∧
      (∀ z ∈ p.support, ∃ w : V, z = Sum.inl w) ∧
      p.IsPath := by
  
  have h_rev_path : rest.reverse.IsPath := h_path.reverse
  
  
  
  cases h_rev_eq : rest.reverse with
  | cons h_lastR restR =>
    
    rw [h_rev_eq] at h_rev_path
    obtain ⟨y', hy'_eq, hy'_ab⟩ := Walk.head_inr_adj_inl (a := a) (b := b) h_lastR
    subst hy'_eq
    refine ⟨y', restR.reverse, h_lastR.symm, ?_, hy'_ab, ?_, ?_⟩
    · 
      have h_rr : rest = rest.reverse.reverse := (Walk.reverse_reverse rest).symm
      rw [h_rev_eq] at h_rr
      rw [h_rr]
      simp [Walk.reverse_cons]
    · intro z hz
      rw [Walk.support_reverse, List.mem_reverse] at hz
      have h_z_ne : z ≠ Sum.inr () := by
        intro h_eq_z
        subst h_eq_z
        have h_rev_nodup : (Walk.cons h_lastR restR).support.Nodup :=
          h_rev_path.support_nodup
        rw [Walk.support_cons, List.nodup_cons] at h_rev_nodup
        exact h_rev_nodup.1 hz
      cases z with
      | inl w => exact ⟨w, rfl⟩
      | inr u =>
          exfalso
          obtain rfl : u = () := rfl
          exact h_z_ne rfl
    · rw [Walk.cons_isPath_iff] at h_rev_path
      exact h_rev_path.1.reverse












theorem Walk.fromSubdivide_cycle
    (hab : G.Adj a b)
    {u : V ⊕ Unit} {c : (G.subdivideEdge a b).Walk u u}
    (hc : c.IsCycle) (h_inr : Sum.inr () ∈ c.support) :
    ∃ (v : V) (c' : G.Walk v v), c'.IsCycle ∧ s(a, b) ∈ c'.edges ∧
      (∀ e ∈ c'.edges, e = s(a, b) ∨
        ∃ u' w' : V, e = s(u', w') ∧ s(Sum.inl u', Sum.inl w') ∈ c.edges) ∧
      (∀ u' w' : V, s(Sum.inl u', Sum.inl w') ∈ c.edges → s(u', w') ∈ c'.edges) := by
  classical
  
  have hc' : (c.rotate (Sum.inr ()) h_inr).IsCycle := hc.rotate h_inr
  
  have h_edges_perm : (c.rotate (Sum.inr ()) h_inr).edges ~r c.edges :=
    c.rotate_edges (Sum.inr ()) h_inr
  
  generalize hc₁ : c.rotate (Sum.inr ()) h_inr = c₁ at hc' h_edges_perm
  match c₁, hc', h_edges_perm with
  | .nil, hc', _ =>
      exact absurd rfl hc'.ne_nil
  | .cons (v := z) h_first rest, hc', h_edges_perm =>
      
      
      obtain ⟨x', hx'_eq, hx'_ab⟩ := Walk.head_inr_adj_inl (a := a) (b := b) h_first
      subst hx'_eq
      
      rw [cons_isCycle_iff] at hc'
      obtain ⟨h_rest_path, _h_not_in⟩ := hc'
      
      obtain ⟨y', p, h_last, h_rest_eq, hy'_ab, h_p_inl, h_p_path⟩ :=
        Walk.isPath_inl_to_inr_split rest h_rest_path
      
      
      
      
      
      
      
      have h_x_ne_y : x' ≠ y' := by
        
        
        
        intro h_eq
        subst h_eq
        
        
        
        
        
        
        
        have h_p_nil : p = .nil := Walk.isPath_iff_eq_nil p |>.mp h_p_path
        subst h_p_nil
        
        simp at h_rest_eq
        
        
        have h_three := (hc.rotate h_inr).three_le_length
        rw [hc₁, h_rest_eq] at h_three
        simp [Walk.length_cons] at h_three
      
      let p_G : G.Walk x' y' := p.projectInl h_p_inl
      have h_p_G_path : p_G.IsPath := p.projectInl_isPath h_p_inl h_p_path
      
      
      
      have h_adj_yx : G.Adj y' x' := by
        rcases hx'_ab with rfl | rfl <;> rcases hy'_ab with rfl | rfl
        · exact absurd rfl h_x_ne_y
        · exact hab.symm
        · exact hab
        · exact absurd rfl h_x_ne_y
      let c_G : G.Walk x' x' := p_G.append (Walk.cons h_adj_yx .nil)
      
      
      
      
      have h_edge_not_in : s(x', y') ∉ p_G.edges := by
        intro h_in
        have h_map : (p_G.edges.map (Sym2.map (Sum.inl : V → V ⊕ Unit))) = p.edges :=
          Walk.projectInl_edges p h_p_inl
        have h_in_p : s(Sum.inl x', Sum.inl y') ∈ p.edges := by
          rw [← h_map]
          refine List.mem_map.mpr ⟨s(x', y'), h_in, ?_⟩
          simp [Sym2.map_mk]
        have h_adj_in_sub : (G.subdivideEdge a b).Adj (Sum.inl x') (Sum.inl y') :=
          p.adj_of_mem_edges h_in_p
        rw [subdivideEdge_adj_inl_inl] at h_adj_in_sub
        obtain ⟨_h_Gadj, h_ne_ab⟩ := h_adj_in_sub
        apply h_ne_ab
        rcases hx'_ab with rfl | rfl <;> rcases hy'_ab with rfl | rfl
        · exact absurd rfl h_x_ne_y
        · rfl
        · rw [Sym2.eq_swap]
        · exact absurd rfl h_x_ne_y
      refine ⟨x', c_G, ?_, ?_, ?_, ?_⟩
      · 
        rw [← Walk.isCycle_reverse]
        
        
        
        
        have h_rev_eq : c_G.reverse = Walk.cons h_adj_yx.symm p_G.reverse := by
          simp [c_G, Walk.reverse_append, Walk.reverse_cons]
        rw [h_rev_eq]
        rw [cons_isCycle_iff]
        refine ⟨h_p_G_path.reverse, ?_⟩
        
        simp only [Walk.edges_reverse, List.mem_reverse]
        exact h_edge_not_in
      · 
        
        have h_c_G_edges : c_G.edges = p_G.edges ++ [s(y', x')] := by
          simp [c_G, Walk.edges_append, Walk.edges_cons]
        rw [h_c_G_edges]
        
        have h_eq : s(y', x') = s(a, b) := by
          rcases hx'_ab with rfl | rfl <;> rcases hy'_ab with rfl | rfl
          · exact absurd rfl h_x_ne_y
          · rw [Sym2.eq_swap]
          · rfl
          · exact absurd rfl h_x_ne_y
        rw [← h_eq]
        exact List.mem_append_right _ (by simp)
      · 
        intro e he
        have h_c_G_edges : c_G.edges = p_G.edges ++ [s(y', x')] := by
          simp [c_G, Walk.edges_append, Walk.edges_cons]
        rw [h_c_G_edges] at he
        rw [List.mem_append] at he
        rcases he with he | he
        · 
          right
          
          have h_map : p_G.edges.map (Sym2.map (Sum.inl : V → V ⊕ Unit)) = p.edges :=
            Walk.projectInl_edges p h_p_inl
          
          have h_lift : Sym2.map (Sum.inl : V → V ⊕ Unit) e ∈ p.edges := by
            rw [← h_map]
            exact List.mem_map.mpr ⟨e, he, rfl⟩
          
          obtain ⟨u', w'⟩ := e
          refine ⟨u', w', rfl, ?_⟩
          
          have h_in_rest : s(Sum.inl u', Sum.inl w') ∈ rest.edges := by
            rw [h_rest_eq]
            rw [Walk.edges_append]
            refine List.mem_append_left _ ?_
            simpa [Sym2.map_mk] using h_lift
          have h_in_cons : s(Sum.inl u', Sum.inl w') ∈ (Walk.cons h_first rest).edges := by
            rw [Walk.edges_cons]
            exact List.mem_cons_of_mem _ h_in_rest
          
          exact (h_edges_perm.mem_iff).mp h_in_cons
        · 
          left
          simp at he
          rw [he]
          rcases hx'_ab with rfl | rfl <;> rcases hy'_ab with rfl | rfl
          · exact absurd rfl h_x_ne_y
          · rw [Sym2.eq_swap]
          · rfl
          · exact absurd rfl h_x_ne_y
      · 
        intro u' w' h_in
        
        have h_in_cons : s(Sum.inl u', Sum.inl w') ∈ (Walk.cons h_first rest).edges :=
          (h_edges_perm.mem_iff).mpr h_in
        
        rw [Walk.edges_cons] at h_in_cons
        rcases List.mem_cons.mp h_in_cons with h_eq_first | h_in_rest
        · 
          exfalso
          rw [Sym2.eq_iff] at h_eq_first
          
          rcases h_eq_first with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact Sum.inl_ne_inr h1
          · exact Sum.inl_ne_inr h2
        
        rw [h_rest_eq, Walk.edges_append, List.mem_append] at h_in_rest
        rcases h_in_rest with h_in_p | h_in_last
        · 
          have h_map : p_G.edges.map (Sym2.map (Sum.inl : V → V ⊕ Unit)) = p.edges :=
            Walk.projectInl_edges p h_p_inl
          
          have h_image : Sym2.map (Sum.inl : V → V ⊕ Unit) s(u', w') ∈ p.edges := by
            simpa [Sym2.map_mk] using h_in_p
          rw [← h_map] at h_image
          
          obtain ⟨e_pre, h_e_pre_in, h_e_eq⟩ := List.mem_map.mp h_image
          
          have h_inl_inj : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ Unit)) :=
            Sym2.map.injective Sum.inl_injective
          have h_e_eq' : e_pre = s(u', w') := h_inl_inj h_e_eq
          subst h_e_eq'
          
          have h_c_G_edges : c_G.edges = p_G.edges ++ [s(y', x')] := by
            simp [c_G, Walk.edges_append, Walk.edges_cons]
          rw [h_c_G_edges, List.mem_append]
          exact Or.inl h_e_pre_in
        · 
          exfalso
          rw [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at h_in_last
          rw [Sym2.eq_iff] at h_in_last
          rcases h_in_last with ⟨_, h2⟩ | ⟨h1, _⟩
          · cases h2
          · cases h1

end Collapse
























section Projection

variable {G : SimpleGraph V} {a b : V}









noncomputable def Walk.projectInl_of_inr_not_mem
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h_not_inr : Sum.inr () ∉ w.support) : G.Walk u v :=
  w.projectInl (by
    intro x hx
    cases x with
    | inl y => exact ⟨y, rfl⟩
    | inr t =>
        exfalso
        obtain rfl : t = () := by cases t; rfl
        exact h_not_inr hx)


theorem Walk.projectInl_of_inr_not_mem_support
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h_not_inr : Sum.inr () ∉ w.support) :
    (w.projectInl_of_inr_not_mem h_not_inr).support.map Sum.inl = w.support := by
  unfold Walk.projectInl_of_inr_not_mem
  exact Walk.projectInl_support w _


theorem Walk.projectInl_of_inr_not_mem_length
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h_not_inr : Sum.inr () ∉ w.support) :
    (w.projectInl_of_inr_not_mem h_not_inr).length = w.length := by
  unfold Walk.projectInl_of_inr_not_mem
  exact Walk.projectInl_length w _


theorem Walk.projectInl_of_inr_not_mem_edges
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h_not_inr : Sum.inr () ∉ w.support) :
    (w.projectInl_of_inr_not_mem h_not_inr).edges.map (Sym2.map Sum.inl) = w.edges := by
  unfold Walk.projectInl_of_inr_not_mem
  exact Walk.projectInl_edges w _


theorem Walk.projectInl_of_inr_not_mem_isPath
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h_not_inr : Sum.inr () ∉ w.support) (hp : w.IsPath) :
    (w.projectInl_of_inr_not_mem h_not_inr).IsPath := by
  unfold Walk.projectInl_of_inr_not_mem
  exact Walk.projectInl_isPath w _ hp




theorem Walk.projectInl_of_inr_not_mem_mem_support
    {u v : V} (w : (G.subdivideEdge a b).Walk (Sum.inl u) (Sum.inl v))
    (h_not_inr : Sum.inr () ∉ w.support) (v₀ : V) :
    v₀ ∈ (w.projectInl_of_inr_not_mem h_not_inr).support ↔
      (Sum.inl v₀ : V ⊕ Unit) ∈ w.support := by
  have hmap := Walk.projectInl_of_inr_not_mem_support w h_not_inr
  constructor
  · intro hv₀
    have hin_map : (Sum.inl v₀ : V ⊕ Unit) ∈
        (w.projectInl_of_inr_not_mem h_not_inr).support.map Sum.inl :=
      List.mem_map.mpr ⟨v₀, hv₀, rfl⟩
    rw [hmap] at hin_map
    exact hin_map
  · intro hv₀
    rw [← hmap] at hv₀
    obtain ⟨w', hw'_mem, hw'_eq⟩ := List.mem_map.mp hv₀
    have : w' = v₀ := Sum.inl_injective hw'_eq
    exact this ▸ hw'_mem

end Projection






















section AvoidVertex

variable {V : Type*} [DecidableEq V]




private lemma Walk.split_path_at_edge
    {G : SimpleGraph V} {a b x₀ y₀ : V} (hab : G.Adj a b)
    (wp : G.Walk x₀ y₀) (h_path : wp.IsPath) (h_through : s(a, b) ∈ wp.edges) :
    (∃ (w₁ : G.Walk x₀ a) (w₂ : G.Walk b y₀),
        wp = w₁.append (Walk.cons hab w₂) ∧
        s(a, b) ∉ w₁.edges ∧ s(a, b) ∉ w₂.edges ∧
        (∀ q ∈ w₁.support, q ∈ wp.support) ∧
        (∀ q ∈ w₂.support, q ∈ wp.support)) ∨
    (∃ (w₁ : G.Walk x₀ b) (w₂ : G.Walk a y₀),
        wp = w₁.append (Walk.cons hab.symm w₂) ∧
        s(a, b) ∉ w₁.edges ∧ s(a, b) ∉ w₂.edges ∧
        (∀ q ∈ w₁.support, q ∈ wp.support) ∧
        (∀ q ∈ w₂.support, q ∈ wp.support)) := by
  have h_trail : wp.IsTrail := h_path.isTrail
  rcases Walk.exists_split_at_edge_local (G := G) hab wp h_through with
    ⟨w₁, w₂, hw_eq, hedges⟩ | ⟨w₁, w₂, hw_eq, hedges⟩
  · left
    refine ⟨w₁, w₂, hw_eq, ?_, ?_, ?_, ?_⟩
    · 
      have hnodup : wp.edges.Nodup := h_trail.edges_nodup
      rw [hedges] at hnodup
      rw [List.nodup_append] at hnodup
      obtain ⟨_, _, hdisj⟩ := hnodup
      intro h
      exact hdisj _ h _ (by simp) rfl
    · 
      have hnodup : wp.edges.Nodup := h_trail.edges_nodup
      rw [hedges] at hnodup
      rw [List.nodup_append] at hnodup
      obtain ⟨_, hnd_cons, _⟩ := hnodup
      simp only [List.nodup_cons] at hnd_cons
      exact hnd_cons.1
    · intro q hq
      rw [hw_eq, Walk.support_append]
      exact List.mem_append_left _ hq
    · intro q hq
      rw [hw_eq, Walk.support_append, Walk.support_cons]
      simp only [List.tail_cons]
      exact List.mem_append_right _ hq
  · right
    refine ⟨w₁, w₂, hw_eq, ?_, ?_, ?_, ?_⟩
    · have hnodup : wp.edges.Nodup := h_trail.edges_nodup
      rw [hedges] at hnodup
      rw [List.nodup_append] at hnodup
      obtain ⟨_, _, hdisj⟩ := hnodup
      intro h
      exact hdisj _ h _ (by simp [Sym2.eq_swap]) rfl
    · have hnodup : wp.edges.Nodup := h_trail.edges_nodup
      rw [hedges] at hnodup
      rw [List.nodup_append] at hnodup
      obtain ⟨_, hnd_cons, _⟩ := hnodup
      simp only [List.nodup_cons] at hnd_cons
      intro h
      apply hnd_cons.1
      rwa [Sym2.eq_swap] at h
    · intro q hq
      rw [hw_eq, Walk.support_append]
      exact List.mem_append_left _ hq
    · intro q hq
      rw [hw_eq, Walk.support_append, Walk.support_cons]
      simp only [List.tail_cons]
      exact List.mem_append_right _ hq





private theorem Walk.liftSubdivide_avoiding_inl
    {G : SimpleGraph V} {a b z₀ x₀ y₀ : V}
    (hab : G.Adj a b)
    (wp : G.Walk x₀ y₀) (h_path : wp.IsPath)
    (h_avoid_z : ∀ q ∈ wp.support, q ≠ z₀) :
    ∃ w' : (G.subdivideEdge a b).Walk (Sum.inl x₀) (Sum.inl y₀),
      ∀ q ∈ w'.support, q ≠ Sum.inl z₀ := by
  by_cases h_through : s(a, b) ∈ wp.edges
  · 
    rcases Walk.split_path_at_edge hab wp h_path h_through with
      ⟨w₁, w₂, _hw_eq, h₁_avoid, h₂_avoid, h₁_sub, h₂_sub⟩ |
      ⟨w₁, w₂, _hw_eq, h₁_avoid, h₂_avoid, h₁_sub, h₂_sub⟩
    · 
      let lw₁ := w₁.liftSubdivide h₁_avoid
      let lw₂ := w₂.liftSubdivide h₂_avoid
      have h_ar : (G.subdivideEdge a b).Adj (Sum.inl a) (Sum.inr ()) :=
        (subdivideEdge_adj_inr_a G a b).symm
      have h_rb : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl b) :=
        subdivideEdge_adj_inr_b G a b
      refine ⟨lw₁.append (Walk.cons h_ar (Walk.cons h_rb lw₂)), ?_⟩
      intro q hq
      rw [Walk.support_append] at hq
      rcases List.mem_append.mp hq with h_in₁ | h_in₂
      · 
        have h_lw₁_supp : lw₁.support = w₁.support.map Sum.inl :=
          Walk.liftSubdivide_support w₁ h₁_avoid
        rw [h_lw₁_supp] at h_in₁
        obtain ⟨q', hq'_mem, hq'_eq⟩ := List.mem_map.mp h_in₁
        subst hq'_eq
        intro h_eq
        have hq'_ne_z : q' ≠ z₀ := h_avoid_z q' (h₁_sub q' hq'_mem)
        exact hq'_ne_z (Sum.inl_injective h_eq)
      · 
        
        
        rw [Walk.support_cons, Walk.support_cons] at h_in₂
        simp only [List.tail_cons] at h_in₂
        rcases List.mem_cons.mp h_in₂ with h_eq_r | h_in_lw₂
        · 
          intro h_eq
          rw [h_eq_r] at h_eq
          cases h_eq
        · 
          have h_lw₂_supp : lw₂.support = w₂.support.map Sum.inl :=
            Walk.liftSubdivide_support w₂ h₂_avoid
          rw [h_lw₂_supp] at h_in_lw₂
          obtain ⟨q', hq'_mem, hq'_eq⟩ := List.mem_map.mp h_in_lw₂
          subst hq'_eq
          intro h_eq
          have hq'_ne_z : q' ≠ z₀ := h_avoid_z q' (h₂_sub q' hq'_mem)
          exact hq'_ne_z (Sum.inl_injective h_eq)
    · 
      let lw₁ := w₁.liftSubdivide h₁_avoid
      let lw₂ := w₂.liftSubdivide h₂_avoid
      have h_br : (G.subdivideEdge a b).Adj (Sum.inl b) (Sum.inr ()) :=
        (subdivideEdge_adj_inr_b G a b).symm
      have h_ra : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl a) :=
        subdivideEdge_adj_inr_a G a b
      refine ⟨lw₁.append (Walk.cons h_br (Walk.cons h_ra lw₂)), ?_⟩
      intro q hq
      rw [Walk.support_append] at hq
      rcases List.mem_append.mp hq with h_in₁ | h_in₂
      · have h_lw₁_supp : lw₁.support = w₁.support.map Sum.inl :=
          Walk.liftSubdivide_support w₁ h₁_avoid
        rw [h_lw₁_supp] at h_in₁
        obtain ⟨q', hq'_mem, hq'_eq⟩ := List.mem_map.mp h_in₁
        subst hq'_eq
        intro h_eq
        have hq'_ne_z : q' ≠ z₀ := h_avoid_z q' (h₁_sub q' hq'_mem)
        exact hq'_ne_z (Sum.inl_injective h_eq)
      · rw [Walk.support_cons, Walk.support_cons] at h_in₂
        simp only [List.tail_cons] at h_in₂
        rcases List.mem_cons.mp h_in₂ with h_eq_r | h_in_lw₂
        · intro h_eq
          rw [h_eq_r] at h_eq
          cases h_eq
        · have h_lw₂_supp : lw₂.support = w₂.support.map Sum.inl :=
            Walk.liftSubdivide_support w₂ h₂_avoid
          rw [h_lw₂_supp] at h_in_lw₂
          obtain ⟨q', hq'_mem, hq'_eq⟩ := List.mem_map.mp h_in_lw₂
          subst hq'_eq
          intro h_eq
          have hq'_ne_z : q' ≠ z₀ := h_avoid_z q' (h₂_sub q' hq'_mem)
          exact hq'_ne_z (Sum.inl_injective h_eq)
  · 
    refine ⟨wp.liftSubdivide h_through, ?_⟩
    intro q hq
    have h_supp : (wp.liftSubdivide h_through).support = wp.support.map Sum.inl :=
      Walk.liftSubdivide_support wp h_through
    rw [h_supp] at hq
    obtain ⟨q', hq'_mem, hq'_eq⟩ := List.mem_map.mp hq
    subst hq'_eq
    intro h_eq
    have hq'_ne_z : q' ≠ z₀ := h_avoid_z q' hq'_mem
    exact hq'_ne_z (Sum.inl_injective h_eq)






theorem Walk.liftSubdivide_avoiding_edge
    {G : SimpleGraph V} {a b c d x₀ y₀ : V}
    (hab : G.Adj a b)
    (wp : G.Walk x₀ y₀) (h_path : wp.IsPath)
    (h_avoid_e : s(c, d) ∉ wp.edges) :
    ∃ w' : (G.subdivideEdge a b).Walk (Sum.inl x₀) (Sum.inl y₀),
      Sym2.map Sum.inl s(c, d) ∉ w'.edges := by
  by_cases h_through : s(a, b) ∈ wp.edges
  · 
    rcases Walk.split_path_at_edge hab wp h_path h_through with
      ⟨w₁, w₂, hw_eq, h₁_avoid, h₂_avoid, _h₁_sub, _h₂_sub⟩ |
      ⟨w₁, w₂, hw_eq, h₁_avoid, h₂_avoid, _h₁_sub, _h₂_sub⟩
    · 
      
      
      have h_e_w₁ : s(c, d) ∉ w₁.edges := by
        intro h
        apply h_avoid_e
        rw [hw_eq, Walk.edges_append, Walk.edges_cons]
        exact List.mem_append_left _ h
      have h_e_w₂ : s(c, d) ∉ w₂.edges := by
        intro h
        apply h_avoid_e
        rw [hw_eq, Walk.edges_append, Walk.edges_cons]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      let lw₁ := w₁.liftSubdivide h₁_avoid
      let lw₂ := w₂.liftSubdivide h₂_avoid
      have h_ar : (G.subdivideEdge a b).Adj (Sum.inl a) (Sum.inr ()) :=
        (subdivideEdge_adj_inr_a G a b).symm
      have h_rb : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl b) :=
        subdivideEdge_adj_inr_b G a b
      refine ⟨lw₁.append (Walk.cons h_ar (Walk.cons h_rb lw₂)), ?_⟩
      intro h_in
      rw [Walk.edges_append, Walk.edges_cons, Walk.edges_cons] at h_in
      rcases List.mem_append.mp h_in with h_in₁ | h_in_rest
      · 
        have h_lw₁_edges : lw₁.edges = w₁.edges.map (Sym2.map Sum.inl) :=
          Walk.liftSubdivide_edges w₁ h₁_avoid
        rw [h_lw₁_edges] at h_in₁
        obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp h_in₁
        
        have hcd_eq : e' = s(c, d) := by
          have hinj : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ Unit)) :=
            Sym2.map.injective Sum.inl_injective
          exact hinj he'_eq
        rw [hcd_eq] at he'_mem
        exact h_e_w₁ he'_mem
      · 
        rcases List.mem_cons.mp h_in_rest with h_eq_ar | h_in_rest2
        · 
          rw [Sym2.map_mk] at h_eq_ar
          rw [Sym2.eq_iff] at h_eq_ar
          rcases h_eq_ar with ⟨_, h_eq⟩ | ⟨h_eq, _⟩
          · cases h_eq
          · cases h_eq
        · rcases List.mem_cons.mp h_in_rest2 with h_eq_rb | h_in_lw₂
          · rw [Sym2.map_mk] at h_eq_rb
            rw [Sym2.eq_iff] at h_eq_rb
            rcases h_eq_rb with ⟨h_eq, _⟩ | ⟨_, h_eq⟩
            · cases h_eq
            · cases h_eq
          · have h_lw₂_edges : lw₂.edges = w₂.edges.map (Sym2.map Sum.inl) :=
              Walk.liftSubdivide_edges w₂ h₂_avoid
            rw [h_lw₂_edges] at h_in_lw₂
            obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp h_in_lw₂
            have hcd_eq : e' = s(c, d) := by
              have hinj : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ Unit)) :=
                Sym2.map.injective Sum.inl_injective
              exact hinj he'_eq
            rw [hcd_eq] at he'_mem
            exact h_e_w₂ he'_mem
    · 
      have h_e_w₁ : s(c, d) ∉ w₁.edges := by
        intro h
        apply h_avoid_e
        rw [hw_eq, Walk.edges_append, Walk.edges_cons]
        exact List.mem_append_left _ h
      have h_e_w₂ : s(c, d) ∉ w₂.edges := by
        intro h
        apply h_avoid_e
        rw [hw_eq, Walk.edges_append, Walk.edges_cons]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      let lw₁ := w₁.liftSubdivide h₁_avoid
      let lw₂ := w₂.liftSubdivide h₂_avoid
      have h_br : (G.subdivideEdge a b).Adj (Sum.inl b) (Sum.inr ()) :=
        (subdivideEdge_adj_inr_b G a b).symm
      have h_ra : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl a) :=
        subdivideEdge_adj_inr_a G a b
      refine ⟨lw₁.append (Walk.cons h_br (Walk.cons h_ra lw₂)), ?_⟩
      intro h_in
      rw [Walk.edges_append, Walk.edges_cons, Walk.edges_cons] at h_in
      rcases List.mem_append.mp h_in with h_in₁ | h_in_rest
      · have h_lw₁_edges : lw₁.edges = w₁.edges.map (Sym2.map Sum.inl) :=
          Walk.liftSubdivide_edges w₁ h₁_avoid
        rw [h_lw₁_edges] at h_in₁
        obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp h_in₁
        have hcd_eq : e' = s(c, d) := by
          have hinj : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ Unit)) :=
            Sym2.map.injective Sum.inl_injective
          exact hinj he'_eq
        rw [hcd_eq] at he'_mem
        exact h_e_w₁ he'_mem
      · rcases List.mem_cons.mp h_in_rest with h_eq_br | h_in_rest2
        · rw [Sym2.map_mk] at h_eq_br
          rw [Sym2.eq_iff] at h_eq_br
          rcases h_eq_br with ⟨_, h_eq⟩ | ⟨h_eq, _⟩
          · cases h_eq
          · cases h_eq
        · rcases List.mem_cons.mp h_in_rest2 with h_eq_ra | h_in_lw₂
          · rw [Sym2.map_mk] at h_eq_ra
            rw [Sym2.eq_iff] at h_eq_ra
            rcases h_eq_ra with ⟨h_eq, _⟩ | ⟨_, h_eq⟩
            · cases h_eq
            · cases h_eq
          · have h_lw₂_edges : lw₂.edges = w₂.edges.map (Sym2.map Sum.inl) :=
              Walk.liftSubdivide_edges w₂ h₂_avoid
            rw [h_lw₂_edges] at h_in_lw₂
            obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp h_in_lw₂
            have hcd_eq : e' = s(c, d) := by
              have hinj : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ Unit)) :=
                Sym2.map.injective Sum.inl_injective
              exact hinj he'_eq
            rw [hcd_eq] at he'_mem
            exact h_e_w₂ he'_mem
  · 
    refine ⟨wp.liftSubdivide h_through, ?_⟩
    intro h_in
    have h_edges : (wp.liftSubdivide h_through).edges = wp.edges.map (Sym2.map Sum.inl) :=
      Walk.liftSubdivide_edges wp h_through
    rw [h_edges] at h_in
    obtain ⟨e', he'_mem, he'_eq⟩ := List.mem_map.mp h_in
    have hcd_eq : e' = s(c, d) := by
      have hinj : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ Unit)) :=
        Sym2.map.injective Sum.inl_injective
      exact hinj he'_eq
    rw [hcd_eq] at he'_mem
    exact h_avoid_e he'_mem











theorem subdivideEdge_walk_avoiding
    {G : SimpleGraph V} (a b : V) (hab : G.Adj a b)
    (h_no_cut : ∀ z x y : V, x ≠ z → y ≠ z →
      ∃ w : G.Walk x y, ∀ q ∈ w.support, q ≠ z)
    (h_not_bridge : ∀ x y : V, ∃ w : G.Walk x y, s(a, b) ∉ w.edges)
    (z : V ⊕ Unit) (x y : V ⊕ Unit) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ w : (G.subdivideEdge a b).Walk x y, ∀ q ∈ w.support, q ≠ z := by
  
  cases z with
  | inr tz =>
    
    obtain rfl : tz = () := by cases tz; rfl
    
    have hx_inl : ∃ x₀ : V, x = Sum.inl x₀ := by
      cases x with
      | inl x₀ => exact ⟨x₀, rfl⟩
      | inr tx =>
          exfalso
          obtain rfl : tx = () := by cases tx; rfl
          exact hxz rfl
    have hy_inl : ∃ y₀ : V, y = Sum.inl y₀ := by
      cases y with
      | inl y₀ => exact ⟨y₀, rfl⟩
      | inr ty =>
          exfalso
          obtain rfl : ty = () := by cases ty; rfl
          exact hyz rfl
    obtain ⟨x₀, rfl⟩ := hx_inl
    obtain ⟨y₀, rfl⟩ := hy_inl
    
    obtain ⟨w0, h_w0_avoid⟩ := h_not_bridge x₀ y₀
    refine ⟨w0.liftSubdivide h_w0_avoid, ?_⟩
    intro q hq
    
    obtain ⟨q', hq'_eq⟩ := Walk.liftSubdivide_support_inl w0 h_w0_avoid q hq
    subst hq'_eq
    intro h_eq
    cases h_eq
  | inl z₀ =>
    
    
    cases x with
    | inl x₀ =>
      have hx₀_ne : x₀ ≠ z₀ := fun h => hxz (by rw [h])
      cases y with
      | inl y₀ =>
        have hy₀_ne : y₀ ≠ z₀ := fun h => hyz (by rw [h])
        
        obtain ⟨w0, h_w0_avoid⟩ := h_no_cut z₀ x₀ y₀ hx₀_ne hy₀_ne
        let wp := w0.bypass
        have h_wp_path : wp.IsPath := w0.bypass_isPath
        have h_wp_avoid : ∀ q ∈ wp.support, q ≠ z₀ := by
          intro q hq
          exact h_w0_avoid q (w0.support_bypass_subset hq)
        exact Walk.liftSubdivide_avoiding_inl hab wp h_wp_path h_wp_avoid
      | inr ty =>
        obtain rfl : ty = () := by cases ty; rfl
        
        
        
        by_cases h_za : z₀ = a
        · 
          have hb_ne_z : b ≠ z₀ := by
            intro h
            rw [h_za] at h
            exact G.loopless.irrefl b (h ▸ hab.symm)
          by_cases h_xb : x₀ = b
          · 
            have h_br : (G.subdivideEdge a b).Adj (Sum.inl x₀) (Sum.inr ()) := by
              rw [h_xb]; exact (subdivideEdge_adj_inr_b G a b).symm
            refine ⟨Walk.cons h_br Walk.nil, ?_⟩
            intro q hq
            rw [Walk.support_cons, Walk.support_nil] at hq
            rcases List.mem_cons.mp hq with h_eq | h_in
            · rw [h_eq]
              intro h_e
              exact hx₀_ne (Sum.inl_injective h_e)
            · rcases List.mem_singleton.mp h_in with h_eq
              rw [h_eq]
              intro h_e
              cases h_e
          · 
            obtain ⟨w0, h_w0_avoid⟩ := h_no_cut z₀ x₀ b hx₀_ne hb_ne_z
            let wp := w0.bypass
            have h_wp_path : wp.IsPath := w0.bypass_isPath
            have h_wp_avoid : ∀ q ∈ wp.support, q ≠ z₀ := by
              intro q hq
              exact h_w0_avoid q (w0.support_bypass_subset hq)
            obtain ⟨w_lift, h_w_lift_avoid⟩ :=
              Walk.liftSubdivide_avoiding_inl hab wp h_wp_path h_wp_avoid
            
            have h_br : (G.subdivideEdge a b).Adj (Sum.inl b) (Sum.inr ()) :=
              (subdivideEdge_adj_inr_b G a b).symm
            refine ⟨w_lift.append (Walk.cons h_br Walk.nil), ?_⟩
            intro q hq
            rw [Walk.support_append] at hq
            rcases List.mem_append.mp hq with h_in_lift | h_in_tail
            · exact h_w_lift_avoid q h_in_lift
            · rw [Walk.support_cons, Walk.support_nil] at h_in_tail
              simp only [List.tail_cons] at h_in_tail
              rcases List.mem_singleton.mp h_in_tail with h_eq
              rw [h_eq]
              intro h_e
              cases h_e
        · 
          have ha_ne_z : a ≠ z₀ := fun h => h_za h.symm
          by_cases h_xa : x₀ = a
          · have h_ar : (G.subdivideEdge a b).Adj (Sum.inl x₀) (Sum.inr ()) := by
              rw [h_xa]; exact (subdivideEdge_adj_inr_a G a b).symm
            refine ⟨Walk.cons h_ar Walk.nil, ?_⟩
            intro q hq
            rw [Walk.support_cons, Walk.support_nil] at hq
            rcases List.mem_cons.mp hq with h_eq | h_in
            · rw [h_eq]
              intro h_e
              exact hx₀_ne (Sum.inl_injective h_e)
            · rcases List.mem_singleton.mp h_in with h_eq
              rw [h_eq]
              intro h_e
              cases h_e
          · obtain ⟨w0, h_w0_avoid⟩ := h_no_cut z₀ x₀ a hx₀_ne ha_ne_z
            let wp := w0.bypass
            have h_wp_path : wp.IsPath := w0.bypass_isPath
            have h_wp_avoid : ∀ q ∈ wp.support, q ≠ z₀ := by
              intro q hq
              exact h_w0_avoid q (w0.support_bypass_subset hq)
            obtain ⟨w_lift, h_w_lift_avoid⟩ :=
              Walk.liftSubdivide_avoiding_inl hab wp h_wp_path h_wp_avoid
            have h_ar : (G.subdivideEdge a b).Adj (Sum.inl a) (Sum.inr ()) :=
              (subdivideEdge_adj_inr_a G a b).symm
            refine ⟨w_lift.append (Walk.cons h_ar Walk.nil), ?_⟩
            intro q hq
            rw [Walk.support_append] at hq
            rcases List.mem_append.mp hq with h_in_lift | h_in_tail
            · exact h_w_lift_avoid q h_in_lift
            · rw [Walk.support_cons, Walk.support_nil] at h_in_tail
              simp only [List.tail_cons] at h_in_tail
              rcases List.mem_singleton.mp h_in_tail with h_eq
              rw [h_eq]
              intro h_e
              cases h_e
    | inr tx =>
      obtain rfl : tx = () := by cases tx; rfl
      
      
      
      cases y with
      | inl y₀ =>
        have hy₀_ne : y₀ ≠ z₀ := fun h => hyz (by rw [h])
        
        by_cases h_za : z₀ = a
        · have hb_ne_z : b ≠ z₀ := by
            intro h
            rw [h_za] at h
            exact G.loopless.irrefl b (h ▸ hab.symm)
          by_cases h_yb : y₀ = b
          · have h_rb : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl y₀) := by
              rw [h_yb]; exact subdivideEdge_adj_inr_b G a b
            refine ⟨Walk.cons h_rb Walk.nil, ?_⟩
            intro q hq
            rw [Walk.support_cons, Walk.support_nil] at hq
            rcases List.mem_cons.mp hq with h_eq | h_in
            · rw [h_eq]
              intro h_e; cases h_e
            · rcases List.mem_singleton.mp h_in with h_eq
              rw [h_eq]
              intro h_e
              exact hy₀_ne (Sum.inl_injective h_e)
          · obtain ⟨w0, h_w0_avoid⟩ := h_no_cut z₀ b y₀ hb_ne_z hy₀_ne
            let wp := w0.bypass
            have h_wp_path : wp.IsPath := w0.bypass_isPath
            have h_wp_avoid : ∀ q ∈ wp.support, q ≠ z₀ := by
              intro q hq
              exact h_w0_avoid q (w0.support_bypass_subset hq)
            obtain ⟨w_lift, h_w_lift_avoid⟩ :=
              Walk.liftSubdivide_avoiding_inl hab wp h_wp_path h_wp_avoid
            have h_rb : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl b) :=
              subdivideEdge_adj_inr_b G a b
            refine ⟨Walk.cons h_rb w_lift, ?_⟩
            intro q hq
            rw [Walk.support_cons] at hq
            rcases List.mem_cons.mp hq with h_eq | h_in_lift
            · rw [h_eq]
              intro h_e; cases h_e
            · exact h_w_lift_avoid q h_in_lift
        · have ha_ne_z : a ≠ z₀ := fun h => h_za h.symm
          by_cases h_ya : y₀ = a
          · have h_ra : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl y₀) := by
              rw [h_ya]; exact subdivideEdge_adj_inr_a G a b
            refine ⟨Walk.cons h_ra Walk.nil, ?_⟩
            intro q hq
            rw [Walk.support_cons, Walk.support_nil] at hq
            rcases List.mem_cons.mp hq with h_eq | h_in
            · rw [h_eq]
              intro h_e; cases h_e
            · rcases List.mem_singleton.mp h_in with h_eq
              rw [h_eq]
              intro h_e
              exact hy₀_ne (Sum.inl_injective h_e)
          · obtain ⟨w0, h_w0_avoid⟩ := h_no_cut z₀ a y₀ ha_ne_z hy₀_ne
            let wp := w0.bypass
            have h_wp_path : wp.IsPath := w0.bypass_isPath
            have h_wp_avoid : ∀ q ∈ wp.support, q ≠ z₀ := by
              intro q hq
              exact h_w0_avoid q (w0.support_bypass_subset hq)
            obtain ⟨w_lift, h_w_lift_avoid⟩ :=
              Walk.liftSubdivide_avoiding_inl hab wp h_wp_path h_wp_avoid
            have h_ra : (G.subdivideEdge a b).Adj (Sum.inr ()) (Sum.inl a) :=
              subdivideEdge_adj_inr_a G a b
            refine ⟨Walk.cons h_ra w_lift, ?_⟩
            intro q hq
            rw [Walk.support_cons] at hq
            rcases List.mem_cons.mp hq with h_eq | h_in_lift
            · rw [h_eq]
              intro h_e; cases h_e
            · exact h_w_lift_avoid q h_in_lift
      | inr ty =>
        obtain rfl : ty = () := by cases ty; rfl
        
        refine ⟨Walk.nil, ?_⟩
        intro q hq
        rw [Walk.support_nil] at hq
        rcases List.mem_singleton.mp hq with h_eq
        rw [h_eq]
        intro h_e
        cases h_e

end AvoidVertex

end SimpleGraph
