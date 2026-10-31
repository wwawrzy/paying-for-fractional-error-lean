import Paper.TotalDomination.IntegerMinorDefects
import Paper.Preliminaries.StarMinorGirth
import Paper.Endpoints.Girth.MarkedDefectCharge

/-! The planar branch of fv:total:defects on the actual star contraction.
Only edges incident to Q are kept. W may overlap L; L minus W is used in
the disjoint face partition, and its cardinality is bounded by ell. -/
namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

set_option maxHeartbeats 2000000 in
theorem planar_defects (hd : 0 < d) (g : ℕ) (hg : 3 ≤ g)
    (hdg : (d:ℝ) = 2*((g:ℝ)/((g:ℝ)-2))) (hp : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    ((WeightedBudget.defects G d ∩ core G d x identifier hfree).card:ℝ) ≤
      (g:ℝ)*((servedLow G d x identifier hfree).card+(first G (I G d x identifier hfree)).card) := by
  let W := first G (I G d x identifier hfree)
  let R := starResidual G d x identifier hfree
  let Q := core G d x identifier hfree
  let L := servedLow G d x identifier hfree
  let L0 := L\W
  let C := W∪R
  let J := StarMinorGirth.graph G W R Q
  let A := StarMinorGirth.marked W R
  let Q' := Q.subtype (fun v => v ∈ C)
  let L' := L0.subtype (fun v => v ∈ C)
  let B' := (WeightedBudget.defects G d ∩ Q).subtype (fun v => v ∈ C)
  have hR := star_residual_disjoint G d x identifier hfree
  have hQR : Q ⊆ R := core_subset_star_residual G d x identifier hfree
  have hQC : Q ⊆ C := fun _ h => Finset.mem_union_right W (hQR h)
  have hLC : L0 ⊆ C := by
    intro v hv
    have hr : v ∈ residual G (I G d x identifier hfree) :=
      (Finset.mem_inter.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).1).1
    exact Finset.mem_union_right W (Finset.mem_sdiff.mpr ⟨hr,(Finset.mem_sdiff.mp hv).2⟩)
  have hQW : Disjoint Q W := (high_disjoint_first G (I G d x identifier hfree)).mono_left Finset.inter_subset_left
  have hQL : Disjoint Q L0 := (block_disjoint G d x identifier hfree).2.1.mono_right Finset.sdiff_subset
  have hAT : Disjoint A (Q'∪L') := by
    apply Finset.disjoint_left.mpr
    intro v hv hh
    have hw := Finset.mem_subtype.mp hv
    rcases Finset.mem_union.mp hh with hq | hl
    · exact Finset.disjoint_left.mp hQW (Finset.mem_subtype.mp hq) hw
    · exact (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hl)).2 hw
  have hQL' : Disjoint Q' L' := by
    apply Finset.disjoint_left.mpr
    intro v hq hl
    exact Finset.disjoint_left.mp hQL (Finset.mem_subtype.mp hq) (Finset.mem_subtype.mp hl)
  have hB : B' ⊆ Q' := fun v hv => Finset.mem_subtype.mpr
    (Finset.mem_inter.mp (Finset.mem_subtype.mp hv)).2
  have hsupport : ∀ q ∈ Q, ∀ v ∈ R, G.Adj q v → v ∈ Q∪L0 := by
    intro q hq v hv ha
    have hh := high_neighbor_residual G d x identifier hfree (Finset.mem_inter.mp hq).1
      (Finset.mem_sdiff.mp hv).1 ha
    rcases Finset.mem_union.mp hh with hq | hl
    · exact Finset.mem_union_left _ hq
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hl,(Finset.mem_sdiff.mp hv).2⟩)
  have hadj (q : {v // v ∈ C}) (hq : q ∈ Q') (v : {v // v ∈ C}) :
      J.Adj q v ↔ (StarMinor.graph G W R).Adj q v := by
    exact ⟨fun h => h.1,fun h => ⟨h,Or.inl (Finset.mem_subtype.mp hq)⟩⟩
  have hbase : ∀ q ∈ Q', d ≤ J.inducedDegree q (Q'∪L') := by
    intro q hq
    have hqQ := Finset.mem_subtype.mp hq
    let D := R.filter (G.Adj q.val)
    let D' := D.subtype (fun v => v ∈ C)
    have hc : D'.card = D.card := StarCounting.subtype_card C D
      (fun v hv => Finset.mem_union_right W (Finset.mem_filter.mp hv).1)
    have hsub : D' ⊆ (Q'∪L').filter (J.Adj q) := by
      intro v hv
      have hvD := Finset.mem_subtype.mp hv
      obtain ⟨hvR,ha⟩ := Finset.mem_filter.mp hvD
      refine Finset.mem_filter.mpr ⟨?_,(hadj q hq v).mpr (StarMinor.residual_edge G W R hR (hQR hqQ) hvR ha)⟩
      rcases Finset.mem_union.mp (hsupport q.val hqQ v.val hvR ha) with hh | hh
      · exact Finset.mem_union_left _ (Finset.mem_subtype.mpr hh)
      · exact Finset.mem_union_right _ (Finset.mem_subtype.mpr hh)
    have hdeg : d ≤ D.card := by
      rw [star_residual_degree G d x identifier hfree hqQ]
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hqQ).1).2
    have hcard := Finset.card_le_card hsub
    change d ≤ ((Q'∪L').filter (J.Adj q)).card
    omega
  have hlower : ∀ q ∈ Q', d+(if q ∈ B' then 1 else 0) ≤
      ((A∪(Q'∪L')).filter (J.Adj q)).card := by
    intro q hq
    have hqQ := Finset.mem_subtype.mp hq
    have hh := StarCounting.degree_lower G W R (Q∪L0) hR q (hQR hqQ) d
      (by
        rw [star_residual_degree G d x identifier hfree hqQ]
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp hqQ).1).2)
      (hsupport q.val hqQ)
      (fun hb he => defect_extra G d x identifier hfree hqQ hb he)
    have hsets : ((Q∪L0∪W).subtype (fun v => v ∈ C)) = A∪(Q'∪L') := by
      ext v
      simp only [A,StarMinorGirth.marked,Q',L',Finset.mem_subtype,Finset.mem_union]
      tauto
    have hbiff : q ∈ B' ↔ G.degree q.val ≠ d := by
      simp only [B',Finset.mem_subtype,Finset.mem_inter,WeightedBudget.defects,
        Finset.mem_filter,Finset.mem_univ,true_and,and_iff_left hqQ]
    rw [hsets] at hh
    have hfilt : (A∪(Q'∪L')).filter (J.Adj q) =
        (A∪(Q'∪L')).filter ((StarMinor.graph G W R).Adj q) := by
      ext v
      simp only [Finset.mem_filter,hadj q hq v]
    rw [hfilt]
    simpa only [hbiff] using hh
  have hb := MarkedDefectCharge.bound J (StarMinorGirth.planar G W R Q hR hp)
    A Q' L' B' hAT hQL' (StarMinorGirth.marked_independent G W R Q hQW) hB
    g d hg hdg (StarMinorGirth.girth G W R Q hR g hgirth) hbase hlower
  have hcB : B'.card = (WeightedBudget.defects G d ∩ Q).card :=
    StarCounting.subtype_card C _ (fun v hv => hQC (Finset.mem_inter.mp hv).2)
  have hcA : A.card = W.card := StarCounting.subtype_card C W Finset.subset_union_left
  have hcL : L'.card ≤ L.card := by
    rw [StarCounting.subtype_card C L0 hLC]
    exact Finset.card_le_card Finset.sdiff_subset
  rw [hcB,hcA] at hb
  have hcLR : (L'.card:ℝ) ≤ L.card := by exact_mod_cast hcL
  have hfinal := mul_le_mul_of_nonneg_left hcLR (Nat.cast_nonneg g : (0:ℝ) ≤ g)
  change ((WeightedBudget.defects G d ∩ Q).card:ℝ) ≤ (g:ℝ)*(L.card+W.card)
  nlinarith only [hb,hfinal]

end Paper.TotalDomination.IntegerSetup
#print axioms Paper.TotalDomination.IntegerSetup.planar_defects
