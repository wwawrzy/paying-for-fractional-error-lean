import Paper.TotalDomination.HighGirthCountEndpoint
import Paper.TotalDomination.HighGirthSlackArithmetic
import Paper.Endpoints.Rounding.Slack

namespace Paper.TotalDomination.HighGirthSetup
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem positive_rounding_slack (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hden : Incidence.InducedDensityBound G a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) (hsupport : ∀ v ∉ K G, x v = 0) :
    (1+HighGirthSlackArithmetic.accuracy a)*(selected G x identifier hfree).card ≤
      objective G (I G x identifier hfree) (fun v => (c G v : ℝ)) := by
  have hc := count_endpoint G x identifier hfree a ha hhi hden hx hcap
  have hcounts := HighGirthSavingArithmetic.density_counts G (I G x identifier hfree) a ha hhi hden rfl
  have hcount := HighGirthSlackArithmetic.size_bound a
    ((first G (I G x identifier hfree)).card : ℝ)
    ((high G (I G x identifier hfree)).card : ℝ)
    ((served G (I G x identifier hfree)).card : ℝ)
    (surplus G (I G x identifier hfree))
    ((attachmentEdges G x identifier hfree).card : ℝ)
    ((linkedLast G x identifier hfree).card : ℝ)
    (penalty G (I G x identifier hfree) (fun v => (c G v : ℝ))+oversupply G (I G x identifier hfree))
    ((selected G x identifier hfree).card : ℝ) ha hhi hcounts.2.1 hcounts.2.2.1 hc.1 (by exact_mod_cast hc.2)
  obtain ⟨hp,ho,hs⟩ := saving G x identifier hfree a ha hhi hden hx hsupport
  apply HighGirthSlackArithmetic.slack a _ _ _ _ _ _ ha hhi
    (Nat.cast_nonneg _) hcounts.1 (Nat.cast_nonneg _) (add_nonneg hp ho) hcount
  simpa only [HighGirthSlackArithmetic.betaSaving,add_assoc] using hs

/-- Mathematical part of fv:hg:total-two(i); solver accuracy remains explicit. -/
theorem coefficient_two (a : ℝ) (ha : 1 ≤ a) (hhi : a < 9/8)
    (hden : Incidence.InducedDensityBound G a)
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G) x)
    (hcap : ∀ v, x v ≤ 1) (hsupport : ∀ v ∉ K G, x v = 0)
    (hsolver : objective G (I G x identifier hfree) (fun v => (c G v : ℝ)) ≤
      (1+HighGirthSlackArithmetic.accuracy a)*HighGirthSelection.residualOptimum G) :
    (∀ r, ∃ v ∈ F G ∪ selected G x identifier hfree, G.Adj r v) ∧
    ((F G ∪ selected G x identifier hfree).card : ℝ) ≤
      2*HighGirthSelection.totalFractionalNumber G := by
  refine ⟨total_dominates G x identifier hfree,?_⟩
  have hround := Paper.Slack.pays_for_error (HighGirthSlackArithmetic.accuracy_positive a ha hhi)
    (positive_rounding_slack G x identifier hfree a ha hhi hden hx hcap hsupport) hsolver
  have hbudget := HighGirthSelection.fractional_budget G hfree
  have hc : ((F G ∪ selected G x identifier hfree).card : ℝ) ≤
      (F G).card+(selected G x identifier hfree).card := by
    exact_mod_cast Finset.card_union_le (F G) (selected G x identifier hfree)
  change ((F G).card : ℝ)+HighGirthSelection.residualOptimum G ≤ _ at hbudget
  linarith

end Paper.TotalDomination.HighGirthSetup
#print axioms Paper.TotalDomination.HighGirthSetup.coefficient_two
