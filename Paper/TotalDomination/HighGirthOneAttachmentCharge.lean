import Paper.TotalDomination.HighGirthOneAttachmentGeometry

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem component_members_path_card
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) : (componentMembers G x identifier hfree C).card = p.length+1 := by
  classical
  let f : C → V := fun z => z.val.val
  have hinj : Function.Injective f := fun a b he => Subtype.ext (Subtype.ext he)
  have heq : p.support.toFinset.image f = componentMembers G x identifier hfree C := by
    ext v
    constructor
    · intro hv
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
    · intro hv
      obtain ⟨hvcore,hvcomp⟩ := (Finset.mem_filter.mp hv).2
      let z : C := ⟨⟨v,hvcore⟩,hvcomp⟩
      exact Finset.mem_image.mpr ⟨z,List.mem_toFinset.mpr (hcover z),rfl⟩
  rw [← heq,Finset.card_image_of_injective _ hinj,List.toFinset_card_of_nodup hp.support_nodup,
    SimpleGraph.Walk.length_support]

theorem path_ends_sum_weight
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (hx : ∀ v, 0 ≤ x v)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hn : ¬p.Nil) :
    x a.val.val+x b.val.val ≤ freeCharge G x identifier hfree C := by
  classical
  have hm : ∀ z : C, z.val.val ∈ componentMembers G x identifier hfree C := by
    intro z
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.val.property,z.property⟩
  have ht := nontrivial_path_ends_terms G x identifier hfree C a b p hn
  have hh := free_path_end_hits G x identifier hfree C hC a b p hp hgraph
  have ha := free_small_hit_weight G x identifier hfree C hC hx (hm a) hh.1
  have hb := free_small_hit_weight G x identifier hfree C hC hx (hm b) hh.2
  have hne : a.val.val ≠ b.val.val := by
    intro he
    have he' : a = b := Subtype.ext (Subtype.ext he)
    subst b
    have heq : p = .nil := (SimpleGraph.Walk.isPath_iff_eq_nil p).mp hp
    subst p
    exact hn (by simp)
  let weight := fun v => ((c G v : ℝ)-(hits G (I G x identifier hfree) v : ℝ))*x v
  have hs : {a.val.val,b.val.val} ⊆ freeTerms G x identifier hfree C := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ht.1
    · exact Finset.mem_singleton.mp hv ▸ ht.2
  have hsum : (∑ v ∈ {a.val.val,b.val.val}, weight v) ≤ freeCharge G x identifier hfree C := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hs
    intro v hv _
    have hhit : (hits G (I G x identifier hfree) v : ℝ) ≤ c G v := by
      exact_mod_cast other_hits_cost G x identifier hfree (Finset.mem_filter.mp hv).1
    exact mul_nonneg (sub_nonneg.mpr hhit) (hx v)
  rw [Finset.sum_pair hne] at hsum
  change _+_ ≤ _ at hsum
  dsimp only [weight] at hsum
  linarith

theorem length_one_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : p.length = 1)
    (hno : a.val.val ∉ attachments G x identifier hfree ∨ b.val.val ∉ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hends := free_path_ends_weight G x identifier hfree C hC hx.1 a b p hp hgraph hn
  have hΩ := free_oversupply_nonneg G x identifier hfree C hx
  rcases hno with hno | hno
  · have hrow := start_fractional_constraint G x identifier hfree C hC a b p hp hgraph hn hno hx
    have hsnd : p.snd = b := by change p.getVert 1 = b; rw [← hlen,SimpleGraph.Walk.getVert_length]
    rw [hsnd] at hrow
    linarith [hends.2]
  · have hrow := start_fractional_constraint G x identifier hfree C hC b a p.reverse hp.reverse
      (by simpa only [SimpleGraph.Walk.toSubgraph_reverse] using hgraph) (by simpa using hn) hno hx
    have hsnd : p.reverse.snd = a := by
      change p.reverse.getVert 1 = a
      rw [SimpleGraph.Walk.getVert_reverse,hlen]
      exact p.getVert_zero
    rw [hsnd] at hrow
    linarith [hends.1]

theorem length_two_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : p.length = 2)
    (hno : (p.getVert 1).val.val ∉ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hrow := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 1 (by decide) (by omega) hno hx
  norm_num only [Nat.reduceSub,Nat.reduceAdd,SimpleGraph.Walk.getVert_zero] at hrow
  have hlast : p.getVert 2 = b := by rw [← hlen,SimpleGraph.Walk.getVert_length]
  rw [hlast] at hrow
  have hends := path_ends_sum_weight G x identifier hfree C hC hx.1 a b p hp hgraph hn
  have hΩ := free_oversupply_nonneg G x identifier hfree C hx
  linarith

theorem center_seven_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe) (hlen : p.length = 6)
    (hn1 : (p.getVert 1).val.val ∉ attachments G x identifier hfree)
    (hn5 : (p.getVert 5).val.val ∉ attachments G x identifier hfree)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  classical
  have hn : ¬p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have h1 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 1 (by decide) (by omega) hn1 hx
  have h5 := internal_fractional_constraint G x identifier hfree C hC a b p hp hgraph 5 (by decide) (by omega) hn5 hx
  have h3 := internal_excess_constraint G x identifier hfree C a b p hp hgraph 3 (by decide) (by omega) hx.1
  norm_num only [Nat.reduceSub,Nat.reduceAdd,SimpleGraph.Walk.getVert_zero] at h1 h5 h3
  have hlast : p.getVert 6 = b := by rw [← hlen,SimpleGraph.Walk.getVert_length]
  rw [hlast] at h5
  have hends := path_ends_sum_weight G x identifier hfree C hC hx.1 a b p hp hgraph hn
  have hm : (p.getVert 3).val.val ∈ componentMembers G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(p.getVert 3).val.property,(p.getVert 3).property⟩
  have hΩ := free_row_excess_le G x identifier hfree C hx hm
  have hbound := HighGirthBadArithmetic.one_inner_seven _ _ _ _ _ _ _ h1 h5 h3 hends hΩ
  linarith

theorem one_attachment_nonexceptional_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (a b : C) (p : C.toSimpleGraph.Walk a b) (hp : p.IsPath)
    (hcover : ∀ z : C, z ∈ p.support) (hgraph : C.toSimpleGraph = p.toSubgraph.spanningCoe)
    (hone : (componentAttachmentPairs G x identifier hfree C).card = 1)
    (hnE : ¬Exceptional G x identifier hfree C)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  obtain ⟨j,hj,hAj,hnot,hj3,hL,hend⟩ := one_attachment_position_bounds G x identifier hfree C hC a b p hp hcover hgraph hone
  have hcard := component_members_path_card G x identifier hfree C a b p hp hcover
  interval_cases j
  · have hshort := hend (Or.inl rfl)
    have hcases : p.length = 0 ∨ p.length = 1 ∨ p.length = 2 := by omega
    rcases hcases with he | he | he
    · apply singleton_nonexceptional_charge G x identifier hfree C hC _ hone hnE hx hcap
      simpa only [he,zero_add] using hcard
    · have hb : b.val.val ∉ attachments G x identifier hfree := by
        have hh := hnot p.length le_rfl (by omega)
        simpa only [SimpleGraph.Walk.getVert_length] using hh
      exact length_one_charge G x identifier hfree C hC a b p hp hgraph he (Or.inr hb) hx
    · exact length_two_charge G x identifier hfree C hC a b p hp hgraph he (hnot 1 (by omega) (by decide)) hx
  · have ha : a.val.val ∉ attachments G x identifier hfree := by
      simpa only [SimpleGraph.Walk.getVert_zero] using hnot 0 (by omega) (by decide)
    by_cases he : p.length = 1
    · exact length_one_charge G x identifier hfree C hC a b p hp hgraph he (Or.inl ha) hx
    · exact False.elim (first_attachment_one_impossible G x identifier hfree C hC a b p hp hgraph
        (by omega) ha hAj hx)
  · by_cases he : p.length = 2
    · exact length_two_charge G x identifier hfree C hC a b p hp hgraph he (hnot 1 (by omega) (by decide)) hx
    · exact first_attachment_two_charge G x identifier hfree C hC a b p hp hgraph
        (by omega) (hnot 1 (by omega) (by decide)) hAj hx
  · have hcases : p.length = 4 ∨ p.length = 5 ∨ p.length = 6 := by
      have hnot3 : p.length ≠ 3 := by
        intro he
        have hh := hend (Or.inr he.symm)
        omega
      omega
    have hb : b.val.val ∉ attachments G x identifier hfree := by
      have hnot3 : p.length ≠ 3 := by
        intro he
        have hh := hend (Or.inr he.symm)
        omega
      simpa only [SimpleGraph.Walk.getVert_length] using hnot p.length le_rfl hnot3
    have hrev : C.toSimpleGraph = p.reverse.toSubgraph.spanningCoe := by
      simpa only [SimpleGraph.Walk.toSubgraph_reverse] using hgraph
    rcases hcases with he | he | he
    · have hA : (p.reverse.getVert 1).val.val ∈ attachments G x identifier hfree := by
        simpa only [SimpleGraph.Walk.getVert_reverse,he,Nat.reduceSub] using hAj
      exact False.elim (first_attachment_one_impossible G x identifier hfree C hC b a p.reverse hp.reverse hrev
        (by simp only [SimpleGraph.Walk.length_reverse]; omega) hb hA hx)
    · have hA : (p.reverse.getVert 2).val.val ∈ attachments G x identifier hfree := by
        simpa only [SimpleGraph.Walk.getVert_reverse,he,Nat.reduceSub] using hAj
      have hn1 : (p.reverse.getVert 1).val.val ∉ attachments G x identifier hfree := by
        simpa only [SimpleGraph.Walk.getVert_reverse,he,Nat.reduceSub] using hnot 4 (by omega) (by decide)
      exact first_attachment_two_charge G x identifier hfree C hC b a p.reverse hp.reverse hrev
        (by simp only [SimpleGraph.Walk.length_reverse]; omega) hn1 hA hx
    · exact center_seven_charge G x identifier hfree C hC a b p hp hgraph he
        (hnot 1 (by omega) (by decide)) (hnot 5 (by omega) (by decide)) hx

end Paper.TotalDomination.HighGirthSetup

#print axioms Paper.TotalDomination.HighGirthSetup.one_attachment_nonexceptional_charge
