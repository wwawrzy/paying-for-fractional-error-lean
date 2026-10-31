import Paper.TotalDomination.HighGirthResidualEndpoint

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def componentMembers
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Finset V := by
  classical
  classical
  exact Finset.univ.filter (fun v => ∃ hv : v ∈ core G x identifier hfree,
    (G.induce (↑(core G x identifier hfree) : Set V)).connectedComponentMk ⟨v,hv⟩ = C)

noncomputable def freeComponent
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Prop :=
  ∀ u ∈ componentMembers G x identifier hfree C,
    u ∉ neighbors G (F G) ∧ u ∉ neighbors G (served G (I G x identifier hfree))

theorem component_subset_core
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) :
    componentMembers G x identifier hfree C ⊆ core G x identifier hfree := by
  classical
  intro u hu
  obtain ⟨hu,_⟩ := (Finset.mem_filter.mp hu).2
  exact hu

theorem component_adj_closed
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    {u v : V} (hu : u ∈ componentMembers G x identifier hfree C)
    (hv : v ∈ core G x identifier hfree) (ha : G.Adj u v) :
    v ∈ componentMembers G x identifier hfree C := by
  classical
  obtain ⟨hu,huc⟩ := (Finset.mem_filter.mp hu).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,hv,?_⟩
  have hadj : (G.induce (↑(core G x identifier hfree) : Set V)).Adj ⟨u,hu⟩ ⟨v,hv⟩ := ha
  exact (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans huc

theorem free_external_connectors
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    {u v : V} (hu : u ∈ componentMembers G x identifier hfree C)
    (hv : v ∉ componentMembers G x identifier hfree C) (ha : G.Adj u v) :
    v ∈ connectors G x identifier hfree := by
  classical
  have huS := component_subset_core G x identifier hfree C hu
  have hnF : v ∉ F G := fun hf => (hC u hu).1 ((mem_neighbors G).mpr ⟨v,hf,ha⟩)
  have hz : v ∈ Z G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnF⟩
  have hnR : v ∉ residual G (I G x identifier hfree) := by
    classical
    intro hr
    have hm := core_neighbor_partition G x identifier hfree huS hr ha
    rcases Finset.mem_union.mp hm with hcore | hy
    · exact hv (component_adj_closed G x identifier hfree C hu hcore ha)
    · exact (hC u hu).2 ((mem_neighbors G).mpr ⟨v,(Finset.mem_sdiff.mp hy).1,ha⟩)
  exact outside_neighbor_connector G x identifier hfree huS (Finset.mem_sdiff.mpr ⟨hz,hnR⟩) ha

theorem connectors_cost_two {v : V} (hv : v ∈ connectors G x identifier hfree) : c G v = 2 := by
  classical
  have hn := (Finset.mem_filter.mp hv).2.2.1
  obtain ⟨w,hw,ha⟩ := (mem_neighbors G).mp hn
  have hb : w ∈ B G := (Finset.mem_filter.mp hw).1
  apply HighGirthSelection.near_cost G
  exact Finset.mem_biUnion.mpr ⟨w,hb,(mem_closed G v w).mpr (Or.inr ha.symm)⟩

theorem free_cost_two
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    {u : V} (hu : u ∈ componentMembers G x identifier hfree C) : c G u = 2 := by
  classical
  have he : G.neighborFinset u ∩ F G = ∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact (hC u hu).1 ((mem_neighbors G).mpr
      ⟨v,(Finset.mem_inter.mp hv).2,(G.mem_neighborFinset u v).mp (Finset.mem_inter.mp hv).1⟩)
  simp [c,HighGirthSelection.boundaryCost,HighGirthSelection.hits,he]

theorem free_all_neighbors_internal
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    {u : V} (hu : u ∈ componentMembers G x identifier hfree C)
    (hn : u ∉ attachments G x identifier hfree) :
    ∀ v, G.Adj u v → v ∈ componentMembers G x identifier hfree C := by
  classical
  intro v ha
  by_contra hv
  have ht := free_external_connectors G x identifier hfree C hC hu hv ha
  exact hn (Finset.mem_inter.mpr ⟨component_subset_core G x identifier hfree C hu,
    (mem_neighbors G).mpr ⟨v,ht,ha⟩⟩)

theorem free_residual_row
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    {u : V} (hu : u ∈ componentMembers G x identifier hfree C) :
    G.neighborFinset u ∩ residual G (I G x identifier hfree) =
      G.neighborFinset u ∩ componentMembers G x identifier hfree C := by
  classical
  ext v
  constructor
  · intro hv
    have ha := (G.mem_neighborFinset u v).mp (Finset.mem_inter.mp hv).1
    have hc : v ∈ componentMembers G x identifier hfree C := by
      by_contra hn
      have ht := free_external_connectors G x identifier hfree C hC hu hn ha
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).2 (Finset.mem_filter.mp ht).2.2.1
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,hc⟩
  · intro hv
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
      core_residual G x identifier hfree (component_subset_core G x identifier hfree C (Finset.mem_inter.mp hv).2)⟩

theorem free_branch_weight
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    {u : V} (hu : u ∈ B G ∩ componentMembers G x identifier hfree C) : x u ≤ 2/3 := by
  classical
  have hs := component_subset_core G x identifier hfree C (Finset.mem_inter.mp hu).2
  have hn := core_not_first G x identifier hfree hs
  by_contra hx
  exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hu).1,lt_of_not_ge hx⟩)

theorem free_positive_term
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    {v : V} (hv : ∃ u ∈ componentMembers G x identifier hfree C, G.Adj v u)
    (hgap : hits G (I G x identifier hfree) v < c G v) :
    c G v = 2 ∧ hits G (I G x identifier hfree) v = 1 := by
  classical
  obtain ⟨u,hu,ha⟩ := hv
  have hc : c G v = 2 := by
    by_cases hv : v ∈ componentMembers G x identifier hfree C
    · exact free_cost_two G x identifier hfree C hC hv
    · exact connectors_cost_two G x identifier hfree
        (free_external_connectors G x identifier hfree C hC hu hv ha.symm)
  have hp : 0 < hits G (I G x identifier hfree) v := Finset.card_pos.mpr
    ⟨u,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr ha,
      core_residual G x identifier hfree (component_subset_core G x identifier hfree C hu)⟩⟩
  exact ⟨hc,by omega⟩

end Paper.TotalDomination.HighGirthSetup
