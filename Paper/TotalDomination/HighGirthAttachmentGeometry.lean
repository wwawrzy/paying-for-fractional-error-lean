import Paper.TotalDomination.HighGirthPathBoundary

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem path_index_distance_bound
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hpath : isPathComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (i j r : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length)
    (hd : C.toSimpleGraph.dist (p.getVert i) (p.getVert j) ≤ r) : i ≤ j+r ∧ j ≤ i+r := by
  by_cases hij : i ≤ j
  · rw [ordered_index_distance G x identifier hfree C hpath a b p hp i j hij hj] at hd
    omega
  · rw [SimpleGraph.dist_comm,ordered_index_distance G x identifier hfree C hpath a b p hp j i (by omega) hi] at hd
    omega

theorem first_attachment_position_le_three
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hbefore : ∀ k, k < i → (p.getVert k).val.val ∉ attachments G x identifier hfree) : i ≤ 3 := by
  classical
  have hpath : isPathComponent G x identifier hfree C := ⟨a,b,p,hp,hcover,hgraph⟩
  have hex : ∃ z : C, z.val.val ∈ attachments G x identifier hfree ∧ C.toSimpleGraph.dist a z ≤ 3 := by
    rcases free_component_metric_access G x identifier hfree C hC a with ⟨z,hB,hd⟩ | ⟨z,hA,hd⟩
    · exact ⟨z,branch_attachment G x identifier hfree (Finset.mem_inter.mpr ⟨hB,z.val.property⟩),hd⟩
    · exact ⟨z,hA,by omega⟩
  obtain ⟨z,hA,hd⟩ := hex
  obtain ⟨k,hzk,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
  have hA' : (p.getVert k).val.val ∈ attachments G x identifier hfree := by simpa only [hzk] using hA
  have himin : i ≤ k := by
    by_contra hn
    exact hbefore k (by omega) hA'
  have hd' : C.toSimpleGraph.dist (p.getVert 0) (p.getVert k) ≤ 3 := by
    simpa only [SimpleGraph.Walk.getVert_zero,hzk] using hd
  have hbnd := path_index_distance_bound G x identifier hfree C hpath a b p hp 0 k 3 (by omega) hk hd'
  omega

theorem attachment_fiber_le_one
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hdistinct : Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C))
    {u : V} (hu : u ∈ componentMembers G x identifier hfree C) :
    (G.neighborFinset u ∩ connectors G x identifier hfree).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro t ht s hs
  have pair : ∀ v ∈ G.neighborFinset u ∩ connectors G x identifier hfree,
      (u,v) ∈ componentAttachmentPairs G x identifier hfree C := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨component_subset_core G x identifier hfree C hu,(Finset.mem_inter.mp hv).2⟩,
        (G.mem_neighborFinset u v).mp (Finset.mem_inter.mp hv).1⟩,hu⟩
  exact congrArg Prod.snd (hdistinct (pair t ht) (pair s hs) rfl)

theorem free_end_not_branch
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hfiber : (G.neighborFinset a.val.val ∩ connectors G x identifier hfree).card ≤ 1) :
    a.val.val ∉ B G := by
  classical
  have hm : a.val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
  have hsub : G.neighborFinset a.val.val ⊆
      (G.neighborFinset a.val.val ∩ componentMembers G x identifier hfree C) ∪
      (G.neighborFinset a.val.val ∩ connectors G x identifier hfree) := by
    intro v hv
    by_cases hc : v ∈ componentMembers G x identifier hfree C
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv,hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv,
        free_external_connectors G x identifier hfree C hC hm hc ((G.mem_neighborFinset _ _).mp hv)⟩)
  have hcard := Finset.card_le_card hsub
  have hU := Finset.card_union_le (G.neighborFinset a.val.val ∩ componentMembers G x identifier hfree C)
    (G.neighborFinset a.val.val ∩ connectors G x identifier hfree)
  have hc := (path_component_neighbor_counts G x identifier hfree C a b p hp hgraph).1
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  intro hB
  have hb := (Finset.mem_filter.mp hB).2
  omega

theorem endpoint_gap_seven_impossible
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hlen : 7 ≤ p.length)
    (hdistinct : Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C))
    (hbetween : ∀ k, 0 < k → k < 7 → (p.getVert k).val.val ∉ attachments G x identifier hfree) : False := by
  classical
  have hpath : isPathComponent G x identifier hfree C := ⟨a,b,p,hp,hcover,hgraph⟩
  have haC : a.val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
  have hnB := free_end_not_branch G x identifier hfree C hC a b p hp hgraph
    (attachment_fiber_le_one G x identifier hfree C hdistinct haC)
  rcases free_component_metric_access G x identifier hfree C hC (p.getVert 3) with ⟨z,hB,hd⟩ | ⟨z,hA,hd⟩
  · have hA := branch_attachment G x identifier hfree (Finset.mem_inter.mpr ⟨hB,z.val.property⟩)
    obtain ⟨k,hzk,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
    have hd' : C.toSimpleGraph.dist (p.getVert 3) (p.getVert k) ≤ 3 := by simpa only [hzk] using hd
    have hbnd := path_index_distance_bound G x identifier hfree C hpath a b p hp 3 k 3 (by omega) hk hd'
    by_cases he : k = 0
    · have hB' : (p.getVert k).val.val ∈ B G := by simpa only [hzk] using hB
      rw [he,SimpleGraph.Walk.getVert_zero] at hB'
      exact hnB hB'
    · exact hbetween k (by omega) (by omega) (by simpa only [hzk] using hA)
  · obtain ⟨k,hzk,hk⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hcover z)
    have hd' : C.toSimpleGraph.dist (p.getVert 3) (p.getVert k) ≤ 2 := by simpa only [hzk] using hd
    have hbnd := path_index_distance_bound G x identifier hfree C hpath a b p hp 3 k 2 (by omega) hk hd'
    exact hbetween k (by omega) (by omega) (by simpa only [hzk] using hA)

/-- All actual multiattachment bad-path cases, including the geometric
exclusions. One-attachment paths are handled separately. -/
theorem consecutive_gap_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hdistinct : Set.InjOn (fun q : V × V => q.1) (componentAttachmentPairs G x identifier hfree C))
    (i j : ℕ) (hij : i < j) (hj : j ≤ p.length)
    (hiA : (p.getVert i).val.val ∈ attachments G x identifier hfree)
    (hjA : (p.getVert j).val.val ∈ attachments G x identifier hfree)
    (hbefore : ∀ k, k < i → (p.getVert k).val.val ∉ attachments G x identifier hfree)
    (hbetween : ∀ k, i < k → k < j → (p.getVert k).val.val ∉ attachments G x identifier hfree)
    (hgap : j-i = 6 ∨ j-i = 7)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  have hi := first_attachment_position_le_three G x identifier hfree C hC a b p hp hcover hgraph i hbefore
  interval_cases i
  · have hj' : j = 6 ∨ j = 7 := by omega
    rcases hj' with rfl | rfl
    · exact endpoint_gap_six_charge G x identifier hfree C hC a b p hp hgraph hj
        (hbetween 1 (by decide) (by decide)) (hbetween 5 (by decide) (by decide)) hjA hx
    · exact False.elim (endpoint_gap_seven_impossible G x identifier hfree C hC a b p hp hcover hgraph hj hdistinct hbetween)
  · have ha0 : a.val.val ∉ attachments G x identifier hfree := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hbefore 0 (by decide)
    exact False.elim (first_attachment_one_impossible G x identifier hfree C hC a b p hp hgraph
      (by omega) ha0 hiA hx)
  · exact first_attachment_two_charge G x identifier hfree C hC a b p hp hgraph
      (by omega) (hbefore 1 (by decide)) hiA hx
  · have hj' : j = 9 ∨ j = 10 := by omega
    rcases hj' with rfl | rfl
    · have ha0 : a.val.val ∉ attachments G x identifier hfree := by
        simpa only [SimpleGraph.Walk.getVert_zero] using hbefore 0 (by decide)
      exact prefix_three_gap_six_charge G x identifier hfree C hC a b p hp hgraph hj ha0
        (hbetween 4 (by decide) (by decide)) (hbetween 8 (by decide) (by decide)) hjA hx hcap
    · exact prefix_three_gap_seven_charge G x identifier hfree C hC a b p hp hgraph hj
        (hbefore 1 (by decide)) (hbetween 5 (by decide) (by decide))
        (hbetween 9 (by decide) (by decide)) hjA hx

end Paper.TotalDomination.HighGirthSetup

#print axioms Paper.TotalDomination.HighGirthSetup.consecutive_gap_charge
