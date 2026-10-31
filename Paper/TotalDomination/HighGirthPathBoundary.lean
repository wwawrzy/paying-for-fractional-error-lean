import Paper.TotalDomination.HighGirthPathCharges

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem start_neighbor_sum
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hn : ¬p.Nil) :
    (∑ v ∈ G.neighborFinset a.val.val ∩ componentMembers G x identifier hfree C, x v) = x p.snd.val.val := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  have heq : C.toSimpleGraph.neighborFinset a = {p.snd} := by
    ext w
    have he : C.toSimpleGraph.Adj a w ↔ p.toSubgraph.Adj a w :=
      Iff.of_eq (congrArg (fun H : SimpleGraph C => H.Adj a w) hgraph)
    rw [SimpleGraph.mem_neighborFinset,he]
    change w ∈ p.toSubgraph.neighborSet a ↔ _
    rw [hp.neighborSet_toSubgraph_startpoint hn]
    simp
  rw [component_neighbor_sum G x identifier hfree C,heq,Finset.sum_singleton]

theorem start_fractional_constraint
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hn : ¬p.Nil)
    (hA : a.val.val ∉ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) : 1 ≤ x p.snd.val.val := by
  classical
  have hm : a.val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val.property,a.property⟩
  have hz := (Finset.mem_sdiff.mp (core_residual G x identifier hfree
    (component_subset_core G x identifier hfree C hm))).1
  have hrow := hx.2 a.val.val hz
  change 1 ≤ ∑ v ∈ G.neighborFinset a.val.val, x v at hrow
  have hs : G.neighborFinset a.val.val ⊆ componentMembers G x identifier hfree C := by
    intro v hv
    exact free_all_neighbors_internal G x identifier hfree C hC hm hA v ((G.mem_neighborFinset _ _).mp hv)
  rw [← Finset.inter_eq_left.mpr hs,start_neighbor_sum G x identifier hfree C a b p hp hgraph hn] at hrow
  exact hrow

theorem first_attachment_one_impossible
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : 1 < p.length)
    (hA0 : a.val.val ∉ attachments G x identifier hfree)
    (hA1 : (p.getVert 1).val.val ∈ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) : False := by
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hrow := start_fractional_constraint G x identifier hfree C hC a b p hp hgraph hn hA0 hx
  have hcap := internal_attachment_weight G x identifier hfree C a b p hp hgraph 1 (by decide) hlen hA1
  change (1:ℝ) ≤ x (p.getVert 1).val.val at hrow
  linarith

theorem first_attachment_two_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : 2 < p.length)
    (hA1 : (p.getVert 1).val.val ∉ attachments G x identifier hfree)
    (hA2 : (p.getVert 2).val.val ∈ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hrow := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 1 (by decide) (by omega) hA1 hx
  norm_num only [Nat.reduceSub,Nat.reduceAdd,SimpleGraph.Walk.getVert_zero] at hrow
  have hcap := internal_attachment_weight G x identifier hfree C a b p hp hgraph 2 (by decide) hlen hA2
  have hQ := (free_path_ends_weight G x identifier hfree C hC hx.1 a b p hp hgraph hn).1
  have hΩ := free_oversupply_nonneg G x identifier hfree C hx
  linarith

theorem attachment_terminal_bound
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (hx : ∀ v, 0 ≤ x v)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (i : ℕ) (hi : 0 < i) (hlen : i ≤ p.length)
    (hA : (p.getVert i).val.val ∈ attachments G x identifier hfree) :
    x (p.getVert i).val.val ≤ 2/3 ∨ x (p.getVert i).val.val ≤ freeCharge G x identifier hfree C := by
  classical
  by_cases he : i = p.length
  · right
    have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
    have hQ := (free_path_ends_weight G x identifier hfree C hC hx a b p hp hgraph hn).2
    have hb : p.getVert i = b := by simp [he]
    simpa only [hb] using hQ
  · left
    exact internal_attachment_weight G x identifier hfree C a b p hp hgraph i (by omega) (by omega) hA

theorem path_two_row_excess_le
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) (hne : i ≠ j) :
    ((∑ v ∈ G.neighborFinset (p.getVert i).val.val, x v)-1) +
      ((∑ v ∈ G.neighborFinset (p.getVert j).val.val, x v)-1) ≤ freeOversupply G x identifier hfree C := by
  classical
  let row := fun r => ((∑ v ∈ G.neighborFinset r, x v)-1)
  have hm : ∀ z : C, z.val.val ∈ componentMembers G x identifier hfree C := by
    intro z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
  have hneq : (p.getVert i).val.val ≠ (p.getVert j).val.val := by
    intro he
    have he' : p.getVert i = p.getVert j := Subtype.ext (Subtype.ext he)
    exact hne (hp.getVert_injOn (by exact hi) (by exact hj) he')
  have hs : {(p.getVert i).val.val,(p.getVert j).val.val} ⊆ componentMembers G x identifier hfree C := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hm _
    · exact Finset.mem_singleton.mp hr ▸ hm _
  have hb : (∑ r ∈ {(p.getVert i).val.val,(p.getVert j).val.val}, row r) ≤
      ∑ r ∈ componentMembers G x identifier hfree C, row r := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro r hr _
    exact sub_nonneg.mpr (hx.2 r (Finset.mem_sdiff.mp (core_residual G x identifier hfree
      (component_subset_core G x identifier hfree C hr))).1)
  rw [Finset.sum_pair hneq] at hb
  exact hb

theorem prefix_three_gap_six_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : 9 ≤ p.length)
    (hA0 : a.val.val ∉ attachments G x identifier hfree)
    (hn4 : (p.getVert 4).val.val ∉ attachments G x identifier hfree)
    (hn8 : (p.getVert 8).val.val ∉ attachments G x identifier hfree)
    (hA9 : (p.getVert 9).val.val ∈ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hstart := start_fractional_constraint G x identifier hfree C hC a b p hp hgraph hn hA0 hx
  have h2 := internal_excess_constraint G x identifier hfree C a b p hp hgraph 2 (by decide) (by omega) hx.1
  have h4 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 4 (by decide) (by omega) hn4 hx
  have h6 := internal_excess_constraint G x identifier hfree C a b p hp hgraph 6 (by decide) (by omega) hx.1
  have h8 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 8 (by decide) (by omega) hn8 hx
  norm_num only [Nat.reduceSub,Nat.reduceAdd] at h2 h4 h6 h8
  have hchain := HighGirthBadArithmetic.prefix_three_gap_six _ _ _ _ _ _ _ (hcap _) hstart h2 h4 h6 h8
  have hΩ := path_two_row_excess_le G x identifier hfree C hx a b p hp 2 6 (by omega) (by omega) (by decide)
  have hQ := free_charge_nonneg G x identifier hfree C hx.1
  have hΩ0 := free_oversupply_nonneg G x identifier hfree C hx
  have ht := attachment_terminal_bound G x identifier hfree C hC hx.1 a b p hp hgraph 9 (by decide) hlen hA9
  apply HighGirthBadArithmetic.terminal_payment (freeCharge G x identifier hfree C)
    (freeOversupply G x identifier hfree C) (x (p.getVert 9).val.val)
    (((∑ v ∈ G.neighborFinset (p.getVert 2).val.val, x v)-1)+
      ((∑ v ∈ G.neighborFinset (p.getVert 6).val.val, x v)-1)) hQ hΩ0
  · linarith
  · linarith
  · exact ht

theorem prefix_three_gap_seven_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : 10 ≤ p.length)
    (hn1 : (p.getVert 1).val.val ∉ attachments G x identifier hfree)
    (hn5 : (p.getVert 5).val.val ∉ attachments G x identifier hfree)
    (hn9 : (p.getVert 9).val.val ∉ attachments G x identifier hfree)
    (hA10 : (p.getVert 10).val.val ∈ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have h1 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 1 (by decide) (by omega) hn1 hx
  have h3 := internal_excess_constraint G x identifier hfree C a b p hp hgraph 3 (by decide) (by omega) hx.1
  have h5 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 5 (by decide) (by omega) hn5 hx
  have h7 := internal_excess_constraint G x identifier hfree C a b p hp hgraph 7 (by decide) (by omega) hx.1
  have h9 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 9 (by decide) (by omega) hn9 hx
  norm_num only [Nat.reduceSub,Nat.reduceAdd,SimpleGraph.Walk.getVert_zero] at h1 h3 h5 h7 h9
  have hchain := HighGirthBadArithmetic.prefix_three_gap_seven _ _ _ _ _ _ _ _ h1 h3 h5 h7 h9
  have hΩ := path_two_row_excess_le G x identifier hfree C hx a b p hp 3 7 (by omega) (by omega) (by decide)
  have hQ := (free_path_ends_weight G x identifier hfree C hC hx.1 a b p hp hgraph hn).1
  have hQ0 := free_charge_nonneg G x identifier hfree C hx.1
  have hΩ0 := free_oversupply_nonneg G x identifier hfree C hx
  have ht := attachment_terminal_bound G x identifier hfree C hC hx.1 a b p hp hgraph 10 (by decide) hlen hA10
  apply HighGirthBadArithmetic.terminal_payment (freeCharge G x identifier hfree C)
    (freeOversupply G x identifier hfree C) (x (p.getVert 10).val.val)
    (x a.val.val+((∑ v ∈ G.neighborFinset (p.getVert 3).val.val, x v)-1)+
      ((∑ v ∈ G.neighborFinset (p.getVert 7).val.val, x v)-1)) hQ0 hΩ0
  · linarith
  · linarith
  · exact ht

end Paper.TotalDomination.HighGirthSetup
