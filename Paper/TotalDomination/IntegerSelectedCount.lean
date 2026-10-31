import Paper.TotalDomination.IntegerOversupply
import Paper.Preliminaries.ResidualWalkDefects

namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation ResidualDefects
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def residualDefects : Finset (residual G (I G d x identifier hfree) : Set V) :=
  localDefects G (residual G (I G d x identifier hfree)) d

theorem induced_degree_hits (v : (residual G (I G d x identifier hfree) : Set V)) :
    (G.induce (residual G (I G d x identifier hfree) : Set V)).degree v =
      hits G (I G d x identifier hfree) v.val := by
  rw [InducedCounting.degree_induce_eq_inducedDegree]
  unfold SimpleGraph.inducedDegree
  change _ = (G.neighborFinset v.val ∩ residual G (I G d x identifier hfree)).card
  congr 1
  ext r
  simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
  exact and_comm

theorem core_regular {v : (residual G (I G d x identifier hfree) : Set V)}
    (hv : v.val ∈ core G d x identifier hfree) (hb : v.val ∉ WeightedBudget.defects G d) :
    v ∉ residualDefects G d x identifier hfree := by
  classical
  have hdeg : G.degree v.val = d := by
    simpa only [WeightedBudget.defects,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hb
  have hlo := (Finset.mem_filter.mp (Finset.mem_inter.mp hv).1).2
  change d ≤ hits G (I G d x identifier hfree) v.val at hlo
  have hhi : hits G (I G d x identifier hfree) v.val ≤ G.degree v.val := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (G.card_neighborFinset_eq_degree _)
  have hh : hits G (I G d x identifier hfree) v.val = d := by omega
  have hind := induced_degree_hits G d x identifier hfree v
  simp only [residualDefects,localDefects,Finset.mem_filter,Finset.mem_univ,true_and,not_or,not_not]
  exact ⟨hind.trans hh,hdeg⟩

theorem residual_defects_card :
    (residualDefects G d x identifier hfree).card ≤
      (WeightedBudget.defects G d ∩ core G d x identifier hfree).card +
      (servedLow G d x identifier hfree).card+(last G (I G d x identifier hfree)).card := by
  classical
  let T := residualDefects G d x identifier hfree
  let Q := core G d x identifier hfree
  let L := servedLow G d x identifier hfree
  let U := last G (I G d x identifier hfree)
  have hsub : T.image Subtype.val ⊆ (WeightedBudget.defects G d ∩ Q) ∪ L ∪ U := by
    intro v hv
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hv
    by_cases hq : r.val ∈ Q
    · have hb : r.val ∈ WeightedBudget.defects G d := by
        by_contra hn
        exact core_regular G d x identifier hfree hq hn hr
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hb,hq⟩))
    · by_cases hy : r.val ∈ served G (I G d x identifier hfree)
      · have hnH : r.val ∉ high G (I G d x identifier hfree) := by
          intro hh
          exact hq (Finset.mem_inter.mpr ⟨hh,r.property⟩)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy,hnH⟩))
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨r.property,hy⟩)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  have h1 := Finset.card_union_le (WeightedBudget.defects G d ∩ Q) L
  have h2 := Finset.card_union_le ((WeightedBudget.defects G d ∩ Q) ∪ L) U
  change T.card ≤ (WeightedBudget.defects G d ∩ Q).card+L.card+U.card
  omega

theorem residual_defects_cover :
    ∀ v : (residual G (I G d x identifier hfree) : Set V),
      v ∈ covered (G.induce (residual G (I G d x identifier hfree) : Set V))
        (covered (G.induce (residual G (I G d x identifier hfree) : Set V))
          (covered (G.induce (residual G (I G d x identifier hfree) : Set V))
            (residualDefects G d x identifier hfree))) := by
  apply ResidualWalkDefects.cover_three
  intro v hv
  obtain ⟨b,hb,p,hp,_⟩ := InitialSelection.remaining_walk G d hfree
    (residual_subset_remaining G d x identifier hfree hv)
  exact ⟨b,(Finset.mem_filter.mp hb).2,p,hp⟩

theorem residual_card (hden : Incidence.InducedDensityBound G ((d:ℝ)/2)) :
    (residual G (I G d x identifier hfree)).card ≤
      (1+d+d*(d-1)+d*(d-1)^2)*(residualDefects G d x identifier hfree).card := by
  classical
  let R := residual G (I G d x identifier hfree)
  let J := G.induce (R : Set V)
  let T := residualDefects G d x identifier hfree
  have hcard : Fintype.card (R:Set V) = R.card := by
    simp only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard]
  have hcap := hden R
  have hcap' : (2*J.edgeFinset.card : ℕ) ≤ d*Fintype.card (R:Set V) := by
    have hc : (J.edgeFinset.card : ℝ) ≤ (d:ℝ)/2*R.card := hcap
    rw [hcard]
    have hh : (2:ℝ)*J.edgeFinset.card ≤ d*R.card := by linarith
    exact_mod_cast hh
  have h := RadiusThree.card_le J T d
    (fun v hv => (outside_localDefects G R d hv).1)
    (residual_defects_cover G d x identifier hfree) hcap'
  rw [hcard] at h
  exact h

/-- The selected-count conclusion for the nonnegative defect coefficients used
in all actual applications. Nonnegativity is explicit: without it the printed
source statement permits counterexamples. -/
theorem selected_count (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 ≤ κ)
    (hden : Incidence.InducedDensityBound G ((d:ℝ)/2))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1)
    (hdefects : ((WeightedBudget.defects G d ∩ core G d x identifier hfree).card : ℝ) ≤
      κ*((servedLow G d x identifier hfree).card+(first G (I G d x identifier hfree)).card)) :
    let M : ℝ := (d:ℝ)^3-(d:ℝ)^2+d+1
    let Γ := M*(κ+1)
    ((output G (I G d x identifier hfree)).card : ℝ) ≤
      (1+M*κ+Γ*(d:ℝ)*((d:ℝ)+2)/2)*(first G (I G d x identifier hfree)).card +
      Γ*(d:ℝ)^2/2*surplus G (I G d x identifier hfree) +
      (2*((d:ℝ)-1)*M+Γ*((d:ℝ)-1)*((d:ℝ)^2+2))*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) +
      Γ*d*oversupply G (I G d x identifier hfree) := by
  let M : ℝ := (d:ℝ)^3-(d:ℝ)^2+d+1
  let Γ : ℝ := M*(κ+1)
  have hd0 : 0 < d := by omega
  have heq : ((1+d+d*(d-1)+d*(d-1)^2 : ℕ):ℝ) = M := by
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_mul,
      Nat.cast_pow,Nat.cast_sub (by omega : 1 ≤ d),Nat.cast_one]
    dsimp [M]
    ring
  have hM : 0 ≤ M := heq ▸ Nat.cast_nonneg _
  have hΓ : 0 ≤ Γ := mul_nonneg hM (by linarith)
  have hR : ((residual G (I G d x identifier hfree)).card : ℝ) ≤
      M*(residualDefects G d x identifier hfree).card := by
    have hh : ((residual G (I G d x identifier hfree)).card : ℝ) ≤
      ((1+d+d*(d-1)+d*(d-1)^2 : ℕ):ℝ)*(residualDefects G d x identifier hfree).card := by
      exact_mod_cast residual_card G d x identifier hfree hden
    rwa [heq] at hh
  have htNat := residual_defects_card G d x identifier hfree
  have htR : ((residualDefects G d x identifier hfree).card : ℝ) ≤
      (WeightedBudget.defects G d ∩ core G d x identifier hfree).card+
      (servedLow G d x identifier hfree).card+(last G (I G d x identifier hfree)).card := by exact_mod_cast htNat
  have hU := last_penalty_bound G d x identifier hfree hd0 hx hcap
  have hT : ((residualDefects G d x identifier hfree).card : ℝ) ≤
      κ*(first G (I G d x identifier hfree)).card+(κ+1)*(servedLow G d x identifier hfree).card+
      2*((d:ℝ)-1)*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) := by
    nlinarith only [htR,hU,hdefects]
  have hTm := mul_le_mul_of_nonneg_left hT hM
  have hj := surplus_nonneg G (I G d x identifier hfree) ((d:ℝ)/2)
    (by
      have h : (0:ℝ) < d := by exact_mod_cast hd0
      positivity) hden (by change 2*((d:ℝ)/2) ≤ (d:ℝ);linarith)
  have hD := output_card_le G (I G d x identifier hfree)
  have hL := mul_le_mul_of_nonneg_left (oversupply_bound G d x identifier hfree hd hden hx hcap) hΓ
  change ((output G (I G d x identifier hfree)).card : ℝ) ≤
      (1+M*κ+Γ*(d:ℝ)*((d:ℝ)+2)/2)*(first G (I G d x identifier hfree)).card +
      Γ*(d:ℝ)^2/2*surplus G (I G d x identifier hfree) +
      (2*((d:ℝ)-1)*M+Γ*((d:ℝ)-1)*((d:ℝ)^2+2))*penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) +
      Γ*d*oversupply G (I G d x identifier hfree)
  dsimp only [Γ] at hL ⊢
  nlinarith only [hR,hTm,hj,hD,hL]

end Paper.TotalDomination.IntegerSetup

#print axioms Paper.TotalDomination.IntegerSetup.selected_count
