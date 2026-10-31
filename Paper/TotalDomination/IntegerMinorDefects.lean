import Paper.TotalDomination.IntegerCountGeometry
import Paper.Preliminaries.StarCounting

/-! A genuine star-minor charge for the integer total-domination rule.
Residual first-step vertices are retained as centers; only R minus W is used
as the disjoint residual set in the contraction model. -/
namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def starResidual : Finset V := residual G (I G d x identifier hfree) \ first G (I G d x identifier hfree)

theorem residual_no_first_edge {q w : V} (hq : q ∈ residual G (I G d x identifier hfree))
    (hw : w ∈ first G (I G d x identifier hfree)) : ¬ G.Adj q w := by
  intro ha
  exact (Finset.mem_sdiff.mp hq).2 ((mem_neighbors G).mpr ⟨w,hw,ha⟩)

theorem star_residual_disjoint : Disjoint (starResidual G d x identifier hfree)
    (covered G (first G (I G d x identifier hfree))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  obtain ⟨w,hw,hqw⟩ := Finset.mem_biUnion.mp hc
  rcases (mem_closed G q w).mp hqw with heq | ha
  · exact (Finset.mem_sdiff.mp hq).2 (heq ▸ hw)
  · exact residual_no_first_edge G d x identifier hfree (Finset.mem_sdiff.mp hq).1 hw ha.symm

theorem core_subset_star_residual : core G d x identifier hfree ⊆ starResidual G d x identifier hfree := by
  intro q hq
  refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hq).2,?_⟩
  intro hw
  exact Finset.disjoint_left.mp (high_disjoint_first G (I G d x identifier hfree))
    (Finset.mem_inter.mp hq).1 hw

theorem star_residual_degree {q : V} (hq : q ∈ core G d x identifier hfree) :
    ((starResidual G d x identifier hfree).filter (G.Adj q)).card = hits G (I G d x identifier hfree) q := by
  congr 1
  ext v
  simp only [Finset.mem_filter,starResidual,Finset.mem_sdiff,hits,Finset.mem_inter,
    SimpleGraph.mem_neighborFinset]
  constructor
  · exact fun h => ⟨h.2,h.1.1⟩
  · intro h
    exact ⟨⟨h.2,fun hw => residual_no_first_edge G d x identifier hfree (Finset.mem_inter.mp hq).2 hw h.1⟩,h.1⟩

theorem defect_extra {q : V} (hq : q ∈ core G d x identifier hfree) (hb : G.degree q ≠ d)
    (heq : ((starResidual G d x identifier hfree).filter (G.Adj q)).card = d) :
    ∃ v ∈ covered G (first G (I G d x identifier hfree)), G.Adj q v := by
  classical
  have hhit : hits G (I G d x identifier hfree) q = d := by
    rwa [star_residual_degree G d x identifier hfree hq] at heq
  have hex : ∃ v, G.Adj q v ∧ v ∉ residual G (I G d x identifier hfree) := by
    by_contra hn
    push Not at hn
    have hs : G.neighborFinset q ∩ residual G (I G d x identifier hfree) = G.neighborFinset q := by
      apply Finset.inter_eq_left.mpr
      intro v hv
      exact hn v ((G.mem_neighborFinset q v).mp hv)
    have hh : G.degree q = d := by
      change (G.neighborFinset q ∩ residual G (I G d x identifier hfree)).card = d at hhit
      rwa [hs,SimpleGraph.card_neighborFinset_eq_degree] at hhit
    exact hb hh
  obtain ⟨v,ha,hv⟩ := hex
  have hqB : q ∈ WeightedBudget.defects G d := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩
  have hvN : v ∈ covered G (WeightedBudget.defects G d) :=
    Finset.mem_biUnion.mpr ⟨q,hqB,(mem_closed G v q).mpr (Or.inr ha)⟩
  have hvD := near_defect_demands G d hvN
  have hvW : v ∈ neighbors G (first G (I G d x identifier hfree)) := by
    by_contra hn
    exact hv (Finset.mem_sdiff.mpr ⟨hvD,hn⟩)
  obtain ⟨w,hw,haw⟩ := (mem_neighbors G).mp hvW
  exact ⟨v,Finset.mem_biUnion.mpr ⟨w,hw,(mem_closed G v w).mpr (Or.inr haw.symm)⟩,ha⟩

set_option maxHeartbeats 2000000 in
/-- Full minor-density branch of fv:total:defects. The planar marked-face
branch is separate and is not asserted by this theorem. -/
theorem minor_defects (hd : 0 < d) (hden : MinorDensity.Bound G ((d:ℝ)/2)) :
    ((WeightedBudget.defects G d ∩ core G d x identifier hfree).card : ℝ) ≤
      ((d:ℝ)/2)*((servedLow G d x identifier hfree).card+(first G (I G d x identifier hfree)).card) := by
  classical
  let W := first G (I G d x identifier hfree)
  let R := starResidual G d x identifier hfree
  let Q := core G d x identifier hfree
  let L := servedLow G d x identifier hfree
  let C := W∪R
  let J := StarMinor.graph G W R
  let Q' := Q.subtype (fun v => v ∈ C)
  let X' := (L∪W).subtype (fun v => v ∈ C)
  let B' := (WeightedBudget.defects G d ∩ Q).subtype (fun v => v ∈ C)
  have hR := star_residual_disjoint G d x identifier hfree
  have hQC : Q ⊆ C := fun v hv => Finset.mem_union_right W (core_subset_star_residual G d x identifier hfree hv)
  have hLC : L ⊆ C := by
    intro v hv
    have hvR : v ∈ residual G (I G d x identifier hfree) :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1
    by_cases hw : v ∈ W
    · exact Finset.mem_union_left _ hw
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvR,hw⟩)
  have hXC : L∪W ⊆ C := Finset.union_subset hLC Finset.subset_union_left
  have hdis : Disjoint Q' X' := by
    apply Finset.disjoint_left.mpr
    intro q hq hx
    have hqQ := Finset.mem_subtype.mp hq
    rcases Finset.mem_union.mp (Finset.mem_subtype.mp hx) with hl | hw
    · exact Finset.disjoint_left.mp (block_disjoint G d x identifier hfree).2.1 hqQ hl
    · exact Finset.disjoint_left.mp (high_disjoint_first G (I G d x identifier hfree))
        (Finset.mem_inter.mp hqQ).1 hw
  have hB : B' ⊆ Q' := fun q hq => Finset.mem_subtype.mpr
    (Finset.mem_inter.mp (Finset.mem_subtype.mp hq)).2
  have hlower : ∀ q ∈ Q', d+(if q ∈ B' then 1 else 0) ≤ ((Q'∪X').filter (J.Adj q)).card := by
    intro q hq
    have hqQ := Finset.mem_subtype.mp hq
    have hqR := core_subset_star_residual G d x identifier hfree hqQ
    have hlo : d ≤ (R.filter (G.Adj q.val)).card := by
      rw [star_residual_degree G d x identifier hfree hqQ]
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hqQ).1).2
    have hh := StarCounting.degree_lower G W R (Q∪L) hR q hqR d hlo
      (fun v hv ha => high_neighbor_residual G d x identifier hfree (Finset.mem_inter.mp hqQ).1
        (Finset.mem_sdiff.mp hv).1 ha)
      (fun hb he => defect_extra G d x identifier hfree hqQ hb he)
    have hsets : ((Q∪L∪W).subtype (fun v => v ∈ C)) = Q'∪X' := by
      ext v
      simp only [Q',X',Finset.mem_subtype,Finset.mem_union]
      tauto
    have hbiff : q ∈ B' ↔ G.degree q.val ≠ d := by
      simp only [B',Finset.mem_subtype,Finset.mem_inter,WeightedBudget.defects,
        Finset.mem_filter,Finset.mem_univ,true_and,and_iff_left hqQ]
    change d+(if G.degree q.val ≠ d then 1 else 0) ≤
      (((Q∪L∪W).subtype (fun v => v ∈ C)).filter (J.Adj q)).card at hh
    rw [hsets] at hh
    simpa only [hbiff] using hh
  have hj := MinorDensity.minor_induced_bound G J hden (StarMinor.isMinor G W R hR)
  have hb := MinorDensity.charged_card_le J hj d (by ring : (d:ℝ)=2*((d:ℝ)/2)) Q' X' B' hdis hB hlower
  have hbc : B'.card = (WeightedBudget.defects G d ∩ Q).card :=
    StarCounting.subtype_card C _ (fun v hv => hQC (Finset.mem_inter.mp hv).2)
  have hxc : X'.card ≤ L.card+W.card := by
    rw [StarCounting.subtype_card C _ hXC]
    exact Finset.card_union_le _ _
  rw [hbc] at hb
  have hxcR : (X'.card : ℝ) ≤ L.card+W.card := by exact_mod_cast hxc
  exact hb.trans (mul_le_mul_of_nonneg_left hxcR (by positivity))

end Paper.TotalDomination.IntegerSetup
#print axioms Paper.TotalDomination.IntegerSetup.minor_defects
