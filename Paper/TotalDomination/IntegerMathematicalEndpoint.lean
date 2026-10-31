import Paper.TotalDomination.IntegerSlack

/-! The mathematical integer total-domination endpoint for an accurate vector.
No distributed solver or round/bit bound is asserted here. -/
namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

noncomputable def finalSelection : Finset V := F G d ∪ output G (I G d x identifier hfree)

theorem final_total_dominates : ∀ r, ∃ v ∈ finalSelection G d x identifier hfree, G.Adj r v := by
  intro r
  by_cases hf : r ∈ F G d
  · obtain ⟨v,hv,ha⟩ := InitialSelection.selected_neighbor G d hf
    exact ⟨v,Finset.mem_union_left _ hv,ha⟩
  by_cases hl : r ∈ linked G d
  · obtain ⟨v,hv,ha⟩ := (mem_neighbors G).mp (Finset.mem_inter.mp hl).2
    exact ⟨v,Finset.mem_union_left _ hv,ha⟩
  have hr : r ∈ (I G d x identifier hfree).demands :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hf⟩,hl⟩
  obtain ⟨v,hv,ha⟩ := output_covers G (I G d x identifier hfree) r hr
  exact ⟨v,Finset.mem_union_right _ hv,ha⟩

theorem minor_rounding (hd : 2 ≤ d)
    (hden : MinorDensity.Bound G ((d:ℝ)/2))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) (hsupport : ∀ v ∉ K G d, x v = 0)
    {optimum : ℝ}
    (hsolver : objective G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) ≤
      (1+accuracy d ((d:ℝ)/2))*optimum) :
    ((output G (I G d x identifier hfree)).card : ℝ) ≤ optimum := by
  have hd0 : 0 < d := by omega
  have hk : (0:ℝ) ≤ (d:ℝ)/2 := by positivity
  exact Paper.Slack.pays_for_error (accuracy_positive d hd hk)
    (slack G d x identifier hfree hd ((d:ℝ)/2) hk
      (MinorDensity.induced_bound G hden) hx hcap hsupport
      (minor_defects G d x identifier hfree hd0 hden)) hsolver

/-- Actual total dominating set with the exact d-fold fractional benchmark,
provided that the residual solver has attained the stated positive accuracy. -/
theorem exact_size (hd : 2 ≤ d)
    (hden : MinorDensity.Bound G ((d:ℝ)/2))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hcap : ∀ v, x v ≤ 1) (hsupport : ∀ v ∉ K G d, x v = 0)
    (hsolver : objective G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) ≤
      (1+accuracy d ((d:ℝ)/2))*InitialSelection.residualOptimum G d) :
    (∀ r, ∃ v ∈ finalSelection G d x identifier hfree, G.Adj r v) ∧
    ((finalSelection G d x identifier hfree).card : ℝ) ≤
      d*InitialSelection.totalFractionalNumber G := by
  refine ⟨final_total_dominates G d x identifier hfree,?_⟩
  have hround := minor_rounding G d x identifier hfree hd hden hx hcap hsupport hsolver
  have hbudget := InitialSelection.fractional_budget G d (by omega) hfree
  have hcard : ((finalSelection G d x identifier hfree).card : ℝ) ≤
      (F G d).card+(output G (I G d x identifier hfree)).card := by
    exact_mod_cast Finset.card_union_le (F G d) (output G (I G d x identifier hfree))
  change ((F G d).card : ℝ)+InitialSelection.residualOptimum G d ≤ _ at hbudget
  linarith

end Paper.TotalDomination.IntegerSetup
#print axioms Paper.TotalDomination.IntegerSetup.exact_size
