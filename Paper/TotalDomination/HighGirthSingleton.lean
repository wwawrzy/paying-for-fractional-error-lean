import Paper.TotalDomination.HighGirthChargePacking

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def componentAttachmentPairs
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Finset (V × V) := by
  classical
  exact (attachmentPairs G x identifier hfree).filter (fun p => p.1 ∈ componentMembers G x identifier hfree C)

theorem charge_term_le
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hx : ∀ v, 0 ≤ x v) {v : V} (hv : v ∈ freeTerms G x identifier hfree C) :
    ((c G v : ℝ)-(hits G (I G x identifier hfree) v : ℝ))*x v ≤ freeCharge G x identifier hfree C := by
  apply Finset.single_le_sum _ hv
  intro u hu
  have hother := (Finset.mem_filter.mp hu).1
  have hh : (hits G (I G x identifier hfree) u : ℝ) ≤ c G u := by
    exact_mod_cast other_hits_cost G x identifier hfree hother
  exact mul_nonneg (sub_nonneg.mpr hh) (hx u)

theorem singleton_neighbors
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (b p : V)
    (hsingle : componentMembers G x identifier hfree C = {b})
    (hone : componentAttachmentPairs G x identifier hfree C = {(b,p)}) :
    G.neighborFinset b = {p} := by
  classical
  have hb : b ∈ componentMembers G x identifier hfree C := by simp [hsingle]
  have hbp : (b,p) ∈ componentAttachmentPairs G x identifier hfree C := by simp [hone]
  have hbp' := (Finset.mem_filter.mp hbp).1
  have ha : G.Adj b p := (Finset.mem_filter.mp hbp').2
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨(G.mem_neighborFinset b p).mpr ha,?_⟩
  intro v hv
  have hav := (G.mem_neighborFinset b v).mp hv
  have hvC : v ∉ componentMembers G x identifier hfree C := by
    rw [hsingle]
    simpa using hav.ne.symm
  have ht := free_external_connectors G x identifier hfree C hC hb hvC hav
  have hpairs : (b,v) ∈ componentAttachmentPairs G x identifier hfree C :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨component_subset_core G x identifier hfree C hb,ht⟩,hav⟩,hb⟩
  rw [hone] at hpairs
  exact congrArg Prod.snd (Finset.mem_singleton.mp hpairs)

theorem singleton_charge_or_exception
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C) (b p : V)
    (hsingle : componentMembers G x identifier hfree C = {b})
    (hone : componentAttachmentPairs G x identifier hfree C = {(b,p)})
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    x p = 1 ∧ p ∈ other G (I G x identifier hfree) ∧
    (1 ≤ freeCharge G x identifier hfree C ∨
      (G.degree p = 2 ∧ ∃ w ∈ first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree), G.Adj p w)) := by
  classical
  have hbC : b ∈ componentMembers G x identifier hfree C := by simp [hsingle]
  have hbS := component_subset_core G x identifier hfree C hbC
  have hbR := core_residual G x identifier hfree hbS
  have hbp : (b,p) ∈ componentAttachmentPairs G x identifier hfree C := by simp [hone]
  have hbp' := (Finset.mem_filter.mp hbp).1
  have hprod := (Finset.mem_filter.mp hbp').1
  have hpT := (Finset.mem_product.mp hprod).2
  have ha : G.Adj b p := (Finset.mem_filter.mp hbp').2
  have hneighbors := singleton_neighbors G x identifier hfree C hC b p hsingle hone
  have hrow := hx.2 b (Finset.mem_sdiff.mp hbR).1
  change 1 ≤ ∑ v ∈ G.neighborFinset b, x v at hrow
  rw [hneighbors,Finset.sum_singleton] at hrow
  have hxp : x p = 1 := le_antisymm (hcap p) hrow
  have hpK := HighGirthSelection.remaining_neighbors_candidates G (Finset.mem_sdiff.mp hbR).1 ha
  have hnW := (Finset.mem_filter.mp hpT).2.1
  have hnH := no_high_neighbor G x identifier hfree (Finset.mem_sdiff.mp hbS).1 ha
  have hpO : p ∈ other G (I G x identifier hfree) :=
    Finset.mem_sdiff.mpr ⟨hpK,fun h => (Finset.mem_union.mp h).elim hnW hnH⟩
  have hc := connectors_cost_two G x identifier hfree hpT
  change c G p = 2 at hc
  have hh := other_hits_cost G x identifier hfree hpO
  have hpos : 0 < hits G (I G x identifier hfree) p := Finset.card_pos.mpr
    ⟨b,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p b).mpr ha.symm,hbR⟩⟩
  refine ⟨hxp,hpO,?_⟩
  by_cases hh1 : hits G (I G x identifier hfree) p = 1
  · left
    have hterm : p ∈ freeTerms G x identifier hfree C := Finset.mem_filter.mpr
      ⟨hpO,b,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p b).mpr ha.symm,hbC⟩⟩
    have hbound := charge_term_le G x identifier hfree C hx.1 hterm
    rw [hc,hh1,hxp] at hbound
    norm_num at hbound
    exact hbound
  · right
    have hh2 : hits G (I G x identifier hfree) p = 2 := by omega
    have hnB : p ∉ B G := by
      intro hpB
      apply hnW
      apply Finset.mem_filter.mpr
      exact ⟨hpB,by change (2/3:ℝ) < x p; rw [hxp]; norm_num⟩
    have hd : G.degree p ≤ 2 := by
      have hn : ¬3 ≤ G.degree p := fun h => hnB (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      omega
    have hd2 : G.degree p = 2 := by
      have hle := hits_le_degree G x identifier hfree p
      omega
    obtain ⟨w,hw,haw⟩ := (mem_neighbors G).mp (Finset.mem_filter.mp hpT).2.2.1
    have heq : G.neighborFinset p ∩ residual G (I G x identifier hfree) = G.neighborFinset p := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      simpa only [SimpleGraph.card_neighborFinset_eq_degree,hd2] using hh2.ge
    have hwR : w ∈ residual G (I G x identifier hfree) :=
      (Finset.mem_inter.mp (heq.symm ▸ (G.mem_neighborFinset p w).mpr haw)).2
    exact ⟨hd2,w,Finset.mem_inter.mpr ⟨hw,hwR⟩,haw⟩

noncomputable def Exceptional
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent) : Prop :=
  ∃ b p, componentMembers G x identifier hfree C = {b} ∧
    componentAttachmentPairs G x identifier hfree C = {(b,p)} ∧ G.degree p = 2 ∧
    ∃ w ∈ first G (I G x identifier hfree) ∩ residual G (I G x identifier hfree), G.Adj p w

theorem singleton_attachment_witness
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (b : V) (hsingle : componentMembers G x identifier hfree C = {b})
    (hone : (componentAttachmentPairs G x identifier hfree C).card = 1) :
    ∃ p, componentAttachmentPairs G x identifier hfree C = {(b,p)} := by
  classical
  obtain ⟨⟨a,p⟩,he⟩ := Finset.card_eq_one.mp hone
  have hm : (a,p) ∈ componentAttachmentPairs G x identifier hfree C := by simp [he]
  have ha : a ∈ componentMembers G x identifier hfree C := (Finset.mem_filter.mp hm).2
  rw [hsingle] at ha
  have hab := Finset.mem_singleton.mp ha
  subst a
  exact ⟨p,he⟩

theorem singleton_nonexceptional_charge
    (C : (G.induce (↑(core G x identifier hfree) : Set V)).ConnectedComponent)
    (hC : freeComponent G x identifier hfree C)
    (hsingle : (componentMembers G x identifier hfree C).card = 1)
    (hone : (componentAttachmentPairs G x identifier hfree C).card = 1)
    (hn : ¬Exceptional G x identifier hfree C)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) :
    (1:ℝ)/3 ≤ freeCharge G x identifier hfree C + freeOversupply G x identifier hfree C := by
  classical
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hsingle
  obtain ⟨p,hp⟩ := singleton_attachment_witness G x identifier hfree C b hb hone
  obtain ⟨_,_,hQ | ⟨hdeg,w,hw,ha⟩⟩ := singleton_charge_or_exception G x identifier hfree C hC b p hb hp hx hcap
  · have hΩ : 0 ≤ freeOversupply G x identifier hfree C := by
      apply Finset.sum_nonneg
      intro r hr
      exact sub_nonneg.mpr (hx.2 r (Finset.mem_sdiff.mp (core_residual G x identifier hfree
        (component_subset_core G x identifier hfree C hr))).1)
    linarith
  · exact False.elim (hn ⟨b,p,hb,hp,hdeg,w,hw,ha⟩)

end Paper.TotalDomination.HighGirthSetup
#print axioms Paper.TotalDomination.HighGirthSetup.singleton_charge_or_exception

#print axioms Paper.TotalDomination.HighGirthSetup.singleton_nonexceptional_charge
