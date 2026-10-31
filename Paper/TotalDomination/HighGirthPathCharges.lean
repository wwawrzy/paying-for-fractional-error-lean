import Paper.TotalDomination.HighGirthPathCoordinates
import Paper.TotalDomination.HighGirthBadArithmetic

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem free_charge_nonneg
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hx : ∀ v, 0 ≤ x v) : 0 ≤ freeCharge G x identifier hfree C := by
  apply Finset.sum_nonneg
  intro v hv
  have hh : (hits G (I G x identifier hfree) v : ℝ) ≤ c G v := by
    exact_mod_cast other_hits_cost G x identifier hfree (Finset.mem_filter.mp hv).1
  exact mul_nonneg (sub_nonneg.mpr hh) (hx v)

theorem free_oversupply_nonneg
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    0 ≤ freeOversupply G x identifier hfree C := by
  apply Finset.sum_nonneg
  intro r hr
  exact sub_nonneg.mpr (hx.2 r (Finset.mem_sdiff.mp (core_residual G x identifier hfree
    (component_subset_core G x identifier hfree C hr))).1)

theorem free_row_excess_le
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    {r : V} (hr : r ∈ componentMembers G x identifier hfree C) :
    ((∑ v ∈ G.neighborFinset r, x v)-1) ≤ freeOversupply G x identifier hfree C := by
  apply Finset.single_le_sum _ hr
  intro u hu
  exact sub_nonneg.mpr (hx.2 u (Finset.mem_sdiff.mp (core_residual G x identifier hfree
    (component_subset_core G x identifier hfree C hu))).1)

theorem free_small_hit_weight
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (hx : ∀ v, 0 ≤ x v)
    {u : V} (hu : u ∈ componentMembers G x identifier hfree C)
    (hh : hits G (I G x identifier hfree) u ≤ 1) :
    x u ≤ ((c G u : ℝ)-(hits G (I G x identifier hfree) u : ℝ))*x u := by
  have hc := free_cost_two G x identifier hfree C hC hu
  have hhR : (hits G (I G x identifier hfree) u : ℝ) ≤ 1 := by exact_mod_cast hh
  have hmul := mul_nonneg (sub_nonneg.mpr hhR) (hx u)
  rw [hc]
  norm_num
  nlinarith

theorem free_path_ends_weight
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (hx : ∀ v, 0 ≤ x v)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hn : ¬p.Nil) :
    x a.val.val ≤ freeCharge G x identifier hfree C ∧ x b.val.val ≤ freeCharge G x identifier hfree C := by
  classical
  have hm : ∀ z : C, z.val.val ∈ componentMembers G x identifier hfree C := by
    intro z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
  have ht := nontrivial_path_ends_terms G x identifier hfree C a b p hn
  have hh := free_path_end_hits G x identifier hfree C hC a b p hp hgraph
  exact ⟨(free_small_hit_weight G x identifier hfree C hC hx (hm a) hh.1).trans
      (charge_term_le G x identifier hfree C hx ht.1),
    (free_small_hit_weight G x identifier hfree C hC hx (hm b) hh.2).trans
      (charge_term_le G x identifier hfree C hx ht.2)⟩

theorem internal_attachment_branch
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length)
    (hA : (p.getVert i).val.val ∈ attachments G x identifier hfree) :
    (p.getVert i).val.val ∈ B G := by
  classical
  have hc := (path_component_neighbor_counts G x identifier hfree C a b p hp hgraph).2.2 i hi hhi
  obtain ⟨t,ht,ha⟩ := (mem_neighbors G).mp (Finset.mem_inter.mp hA).2
  have hnot : t ∉ G.neighborFinset (p.getVert i).val.val ∩ componentMembers G x identifier hfree C := by
    intro hn
    exact Finset.disjoint_left.mp (core_connectors_disjoint G x identifier hfree)
      (component_subset_core G x identifier hfree C (Finset.mem_inter.mp hn).2) ht
  have hsub : insert t (G.neighborFinset (p.getVert i).val.val ∩ componentMembers G x identifier hfree C) ⊆
      G.neighborFinset (p.getVert i).val.val := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact (G.mem_neighborFinset _ _).mpr ha
    · exact (Finset.mem_inter.mp hv).1
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot,hc,SimpleGraph.card_neighborFinset_eq_degree] at hcard
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩

theorem internal_attachment_weight
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : i ≠ 0) (hhi : i < p.length)
    (hA : (p.getVert i).val.val ∈ attachments G x identifier hfree) :
    x (p.getVert i).val.val ≤ 2/3 := by
  classical
  have hb := internal_attachment_branch G x identifier hfree C a b p hp hgraph i hi hhi hA
  apply free_branch_weight G x identifier hfree C
  exact Finset.mem_inter.mpr ⟨hb,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(p.getVert i).val.property,(p.getVert i).property⟩⟩

/-- A complete actual graph subcase: the first attachment is an end and
the next attachment is six positions away. No scalar charge certificate is assumed. -/
theorem endpoint_gap_six_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : 6 ≤ p.length)
    (hn1 : (p.getVert 1).val.val ∉ attachments G x identifier hfree)
    (hn5 : (p.getVert 5).val.val ∉ attachments G x identifier hfree)
    (hA6 : (p.getVert 6).val.val ∈ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  classical
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hends := free_path_ends_weight G x identifier hfree C hC hx.1 a b p hp hgraph hn
  have h1 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 1 (by decide) (by omega) hn1 hx
  have h5 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 5 (by decide) (by omega) hn5 hx
  have h3 := internal_excess_constraint G x identifier hfree C a b p hp hgraph 3 (by decide) (by omega) hx.1
  norm_num only [Nat.reduceSub,Nat.reduceAdd,SimpleGraph.Walk.getVert_zero] at h1
  change 1 ≤ x (p.getVert 4).val.val+x (p.getVert 6).val.val at h5
  change x (p.getVert 2).val.val+x (p.getVert 4).val.val ≤
    1+((∑ v ∈ G.neighborFinset (p.getVert 3).val.val, x v)-1) at h3
  have hchain := HighGirthBadArithmetic.gap_six _ _ _ _ _ h1 h3 h5
  have hm3 : (p.getVert 3).val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(p.getVert 3).val.property,(p.getVert 3).property⟩
  have hΩ3 := free_row_excess_le G x identifier hfree C hx hm3
  have hterminal : x (p.getVert 6).val.val ≤ 2/3 ∨ x (p.getVert 6).val.val ≤ freeCharge G x identifier hfree C := by
    by_cases he : 6 = p.length
    · right
      have hb : p.getVert 6 = b := by simp [he]
      simpa only [hb] using hends.2
    · left
      exact internal_attachment_weight G x identifier hfree C a b p hp hgraph 6 (by decide) (by omega) hA6
  apply HighGirthBadArithmetic.terminal_payment (freeCharge G x identifier hfree C)
    (freeOversupply G x identifier hfree C) (x (p.getVert 6).val.val)
    (x a.val.val+((∑ v ∈ G.neighborFinset (p.getVert 3).val.val, x v)-1))
    (free_charge_nonneg G x identifier hfree C hx.1) (free_oversupply_nonneg G x identifier hfree C hx)
  · linarith
  · linarith [hends.1]
  · exact hterminal

end Paper.TotalDomination.HighGirthSetup
