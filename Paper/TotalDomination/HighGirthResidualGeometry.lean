import Paper.TotalDomination.HighGirthSaving
import Paper.Endpoints.Girth.HighGirthPathCycle

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def core : Finset V := last G (I G x identifier hfree) \
  (first G (I G x identifier hfree) ∪ high G (I G x identifier hfree))
noncomputable def connectors : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ∉ first G (I G x identifier hfree) ∧
    v ∈ neighbors G (first G (I G x identifier hfree)) ∧
    v ∈ neighbors G (core G x identifier hfree))
noncomputable def attachments : Finset V := core G x identifier hfree ∩ neighbors G (connectors G x identifier hfree)

theorem core_residual : core G x identifier hfree ⊆ residual G (I G x identifier hfree) :=
  Finset.sdiff_subset.trans Finset.sdiff_subset

theorem core_not_first {u : V} (hu : u ∈ core G x identifier hfree) :
    u ∉ first G (I G x identifier hfree) := fun hw =>
  (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_left _ hw)

theorem core_not_high {u : V} (hu : u ∈ core G x identifier hfree) :
    u ∉ high G (I G x identifier hfree) := fun hh =>
  (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_right _ hh)

theorem no_first_neighbor {u v : V} (hu : u ∈ residual G (I G x identifier hfree))
    (ha : G.Adj u v) : v ∉ first G (I G x identifier hfree) := by
  intro hv
  exact (Finset.mem_sdiff.mp hu).2 ((mem_neighbors G).mpr ⟨v,hv,ha⟩)

theorem no_high_neighbor {u v : V} (hu : u ∈ last G (I G x identifier hfree))
    (ha : G.Adj u v) : v ∉ high G (I G x identifier hfree) := by
  intro hv
  exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mpr
    ⟨(Finset.mem_sdiff.mp hu).1,(mem_neighbors G).mpr ⟨v,hv,ha⟩⟩)

theorem low_residual_degree {v : V} (hv : v ∈ residual G (I G x identifier hfree))
    (hnear : v ∈ core G x identifier hfree ∨ ∃ u ∈ core G x identifier hfree, G.Adj v u) :
    hits G (I G x identifier hfree) v ≤ 2 := by
  have hnW : v ∉ first G (I G x identifier hfree) := by
    rcases hnear with hu | ⟨u,hu,ha⟩
    · exact core_not_first G x identifier hfree hu
    · exact no_first_neighbor G x identifier hfree (core_residual G x identifier hfree hu) ha.symm
  have hnH : v ∉ high G (I G x identifier hfree) := by
    rcases hnear with hu | ⟨u,hu,ha⟩
    · exact core_not_high G x identifier hfree hu
    · exact no_high_neighbor G x identifier hfree (Finset.mem_sdiff.mp hu).1 ha.symm
  have hk := HighGirthSelection.remaining_subset_candidates G hfree (Finset.mem_sdiff.mp hv).1
  by_contra hn
  exact hnH (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hk,hnW⟩,
    by change 3 ≤ hits G (I G x identifier hfree) v; omega⟩)

theorem core_neighbor_partition {u v : V} (hu : u ∈ core G x identifier hfree)
    (hv : v ∈ residual G (I G x identifier hfree)) (ha : G.Adj u v) :
    v ∈ core G x identifier hfree ∪ (served G (I G x identifier hfree) \ high G (I G x identifier hfree)) := by
  have hnW := no_first_neighbor G x identifier hfree (core_residual G x identifier hfree hu) ha
  have hnH := no_high_neighbor G x identifier hfree (Finset.mem_sdiff.mp hu).1 ha
  by_cases hy : v ∈ served G (I G x identifier hfree)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy,hnH⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hv,hy⟩,fun h => (Finset.mem_union.mp h).elim hnW hnH⟩)

theorem outside_neighbor_connector {u v : V} (hu : u ∈ core G x identifier hfree)
    (hv : v ∈ Z G \ residual G (I G x identifier hfree)) (ha : G.Adj u v) :
    v ∈ connectors G x identifier hfree := by
  have hN : v ∈ neighbors G (first G (I G x identifier hfree)) := by
    by_contra hn
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,hn⟩)
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,no_first_neighbor G x identifier hfree (core_residual G x identifier hfree hu) ha,
    hN,(mem_neighbors G).mpr ⟨u,hu,ha.symm⟩⟩

theorem branch_attachment {u : V} (hu : u ∈ B G ∩ core G x identifier hfree) :
    u ∈ attachments G x identifier hfree := by
  have hb := (Finset.mem_inter.mp hu).1
  have hc := (Finset.mem_inter.mp hu).2
  have hlow := low_residual_degree G x identifier hfree (core_residual G x identifier hfree hc) (Or.inl hc)
  have hdeg : 3 ≤ G.degree u := (Finset.mem_filter.mp hb).2
  have hex : ∃ v ∈ G.neighborFinset u, v ∉ residual G (I G x identifier hfree) := by
    by_contra hn
    push Not at hn
    have heq : G.neighborFinset u ∩ residual G (I G x identifier hfree) = G.neighborFinset u :=
      Finset.inter_eq_left.mpr hn
    change (G.neighborFinset u ∩ residual G (I G x identifier hfree)).card ≤ 2 at hlow
    rw [heq,SimpleGraph.card_neighborFinset_eq_degree] at hlow
    omega
  obtain ⟨v,hv,hnR⟩ := hex
  have ha := (G.mem_neighborFinset u v).mp hv
  have hnF : v ∉ F G := by
    intro hf
    exact Finset.disjoint_left.mp (HighGirthSelection.near_defect_disjoint G (subset_covered G (B G) hb))
      ((mem_closed G v u).mpr (Or.inr ha)) hf
  have hz : v ∈ Z G := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hnF⟩
  have ht := outside_neighbor_connector G x identifier hfree hc (Finset.mem_sdiff.mpr ⟨hz,hnR⟩) ha
  exact Finset.mem_inter.mpr ⟨hc,(mem_neighbors G).mpr ⟨v,ht,ha⟩⟩

theorem core_induced_degree :
    ∀ v : {u // u ∈ core G x identifier hfree},
      (G.induce (↑(core G x identifier hfree) : Set V)).degree v ≤ 2 := by
  classical
  intro v
  let U := core G x identifier hfree
  have hr := low_residual_degree G x identifier hfree
    (core_residual G x identifier hfree v.property) (Or.inl v.property)
  have hsub : G.neighborFinset v.val ∩ U ⊆ G.neighborFinset v.val ∩ residual G (I G x identifier hfree) :=
    Finset.inter_subset_inter_left (core_residual G x identifier hfree)
  have hc : (G.neighborFinset v.val ∩ U).card ≤ 2 := (Finset.card_le_card hsub).trans hr
  have heq : ((G.induce (↑U : Set V)).neighborFinset v).map
      (.subtype (· ∈ (↑U : Set V))) = G.neighborFinset v.val ∩ U := by
    ext a
    simp
  have hcard := congrArg Finset.card heq
  have hdeg : (G.induce (↑U : Set V)).degree v = (G.neighborFinset v.val ∩ U).card := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using hcard
  exact hdeg.trans_le hc

theorem core_components_path_or_cycle :
    ∀ C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent,
      (∃ (a b : C) (p : C.toSimpleGraph.Walk a b), p.IsPath ∧
        (∀ z : C, z ∈ p.support) ∧ C.toSimpleGraph = p.toSubgraph.spanningCoe) ∨
      (∃ (a : C) (p : C.toSimpleGraph.Walk a a), p.IsCycle ∧
        (∀ z : C, z ∈ p.support) ∧ C.toSimpleGraph = p.toSubgraph.spanningCoe) := by
  classical
  intro C
  let U := core G x identifier hfree
  let H := G.induce (↑U : Set V)
  letI : Fintype C := Fintype.ofFinite C
  have hH : ∀ v : {u // u ∈ U}, H.degree v ≤ 2 := core_induced_degree G x identifier hfree
  have hC : ∀ z : C, C.toSimpleGraph.degree z ≤ 2 := by
    intro z
    let f : C.toSimpleGraph.neighborSet z → H.neighborSet z.val := fun a => ⟨a.val.val,a.property⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : H.neighborSet z.val => a.val) hab
    have hle := Fintype.card_le_of_injective f hf
    have hle' : C.toSimpleGraph.degree z ≤ H.degree z.val := by
      simpa only [SimpleGraph.card_neighborSet_eq_degree] using hle
    exact hle'.trans (hH z.val)
  exact Paper.HighGirthPathCycle.connected_path_or_cycle C.toSimpleGraph C.connected_toSimpleGraph hC

end Paper.TotalDomination.HighGirthSetup
