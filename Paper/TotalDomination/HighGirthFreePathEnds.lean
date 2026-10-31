import Paper.TotalDomination.HighGirthFreeAccess

namespace Paper.TotalDomination.HighGirthSetup

theorem component_neighbor_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (z : K) :
    (G.neighborFinset z.val.val ∩ componentMembers G x identifier hfree K).card =
      (K.toSimpleGraph.neighborSet z).ncard := by
  classical
    letI : Fintype K := Fintype.ofFinite K
    let e : K ↪ V := ⟨fun a => a.val.val, by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact hab⟩
    have hmap : (K.toSimpleGraph.neighborFinset z).map e =
        G.neighborFinset z.val.val ∩ componentMembers G x identifier hfree K := by
      ext v
      constructor
      · intro hv
        obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hv
        have hadj : G.Adj z.val.val a.val.val := (K.toSimpleGraph.mem_neighborFinset z a).mp ha
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hadj,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩⟩
      · intro hv
        obtain ⟨hvn,hvK⟩ := Finset.mem_inter.mp hv
        obtain ⟨hvU,hvComp⟩ := (Finset.mem_filter.mp hvK).2
        let a : K := ⟨⟨v,hvU⟩,hvComp⟩
        have hadj : K.toSimpleGraph.Adj z a := (G.mem_neighborFinset _ _).mp hvn
        exact Finset.mem_map.mpr ⟨a,(K.toSimpleGraph.mem_neighborFinset z a).mpr hadj,rfl⟩
    rw [Set.ncard_eq_toFinset_card']
    change (G.neighborFinset z.val.val ∩ componentMembers G x identifier hfree K).card =
      (K.toSimpleGraph.neighborFinset z).card
    simpa only [Finset.card_map] using (congrArg Finset.card hmap).symm

theorem path_component_neighbor_counts
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real) (identifier : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty)
    (K : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : K) (p : K.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : K.toSimpleGraph = p.toSubgraph.spanningCoe) :
    (G.neighborFinset a.val.val ∩ componentMembers G x identifier hfree K).card ≤ 1 ∧
    (G.neighborFinset b.val.val ∩ componentMembers G x identifier hfree K).card ≤ 1 ∧
    ∀ i : Nat, i ≠ 0 → i < p.length →
      (G.neighborFinset (p.getVert i).val.val ∩ componentMembers G x identifier hfree K).card = 2 := by
  classical
    have hns : ∀ z : K, K.toSimpleGraph.neighborSet z = p.toSubgraph.neighborSet z := by
      intro z
      ext w
      exact Iff.of_eq (congrArg (fun F : SimpleGraph K => F.Adj z w) hgraph)
    have hc : ∀ z : K, (G.neighborFinset z.val.val ∩ componentMembers G x identifier hfree K).card =
        (p.toSubgraph.neighborSet z).ncard := by
      intro z
      exact (component_neighbor_card G x identifier hfree K z).trans (congrArg Set.ncard (hns z))
    have hbnd : (p.toSubgraph.neighborSet a).ncard ≤ 1 ∧ (p.toSubgraph.neighborSet b).ncard ≤ 1 := by
      by_cases hn : p.Nil
      · cases p with
        | nil => simp [SimpleGraph.Walk.toSubgraph]
        | cons h w => simp at hn
      · constructor
        · rw [hp.neighborSet_toSubgraph_startpoint hn]
          simp
        · rw [hp.neighborSet_toSubgraph_endpoint hn]
          simp
    refine ⟨(hc a).trans_le hbnd.1,(hc b).trans_le hbnd.2,?_⟩
    intro i hi hiL
    exact (hc (p.getVert i)).trans (hp.ncard_neighborSet_toSubgraph_internal_eq_two hi hiL)

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem free_path_end_hits
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) :
    hits G (I G x identifier hfree) a.val.val ≤ 1 ∧
    hits G (I G x identifier hfree) b.val.val ≤ 1 := by
  classical
  have hm : ∀ z : C, z.val.val ∈ componentMembers G x identifier hfree C := by
    intro z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
  have hc := path_component_neighbor_counts G x identifier hfree C a b p hp hgraph
  constructor
  · change (G.neighborFinset a.val.val ∩ residual G (I G x identifier hfree)).card ≤ 1
    rw [free_residual_row G x identifier hfree C hC (hm a)]
    exact hc.1
  · change (G.neighborFinset b.val.val ∩ residual G (I G x identifier hfree)).card ≤ 1
    rw [free_residual_row G x identifier hfree C hC (hm b)]
    exact hc.2.1

noncomputable def freeTerms
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Finset V := by
  classical
  exact (other G (I G x identifier hfree)).filter
    (fun v => (G.neighborFinset v ∩ componentMembers G x identifier hfree C).Nonempty)
noncomputable def freeCharge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : ℝ :=
  ∑ v ∈ freeTerms G x identifier hfree C, ((c G v : ℝ)-(hits G (I G x identifier hfree) v : ℝ))*x v
noncomputable def freeOversupply
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : ℝ :=
  ∑ r ∈ componentMembers G x identifier hfree C, ((∑ v ∈ G.neighborFinset r, x v)-1)

theorem component_subset_other
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) :
    componentMembers G x identifier hfree C ⊆ other G (I G x identifier hfree) := by
  classical
  intro v hv
  have hc := component_subset_core G x identifier hfree C hv
  have hk := HighGirthSelection.remaining_subset_candidates G hfree
    (Finset.mem_sdiff.mp (core_residual G x identifier hfree hc)).1
  exact Finset.mem_sdiff.mpr ⟨hk,(Finset.mem_sdiff.mp hc).2⟩

theorem nontrivial_path_ends_terms
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hn : ¬p.Nil) :
    a.val.val ∈ freeTerms G x identifier hfree C ∧ b.val.val ∈ freeTerms G x identifier hfree C := by
  classical
  have hm : ∀ z : C, z.val.val ∈ componentMembers G x identifier hfree C := by
    intro z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
  have term : ∀ (z w : C), C.toSimpleGraph.Adj z w → z.val.val ∈ freeTerms G x identifier hfree C := by
    intro z w ha
    exact Finset.mem_filter.mpr ⟨component_subset_other G x identifier hfree C (hm z),w.val.val,
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z.val.val w.val.val).mpr ha,hm w⟩⟩
  exact ⟨term a p.snd (p.adj_snd hn),term b p.reverse.snd (p.reverse.adj_snd (by simpa using hn))⟩

theorem positive_charge_vertex
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (hx : ∀ v, 0 ≤ x v) {v : V} (hv : v ∈ freeTerms G x identifier hfree C)
    (hpos : 0 < ((c G v : ℝ)-(hits G (I G x identifier hfree) v : ℝ))*x v) :
    c G v = 2 ∧ hits G (I G x identifier hfree) v = 1 := by
  classical
  obtain ⟨_,u,hu⟩ := Finset.mem_filter.mp hv
  have ha := (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp hu).1
  have hgapR : (hits G (I G x identifier hfree) v : ℝ) < c G v := by
    by_contra hn
    have hnon := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn)) (hx v)
    linarith
  have hgap : hits G (I G x identifier hfree) v < c G v := by exact_mod_cast hgapR
  exact free_positive_term G x identifier hfree C hC ⟨u,(Finset.mem_inter.mp hu).2,ha⟩ hgap

end Paper.TotalDomination.HighGirthSetup
