import Paper.Endpoints.Rounding.CurrentCountBound
import Paper.Endpoints.Rounding.CurrentBudgetBridge
import Paper.Preliminaries.PlanarDensity


namespace Paper.Proposition2PlanarAudit

open SevenFoundation

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem planar_rounding (hplanar : G.IsPlanar) (x : V → ℝ)
    (hx : feasible (CurrentBudget.auxiliary G 6) x)
    (hcap : ∀ v ∈ CurrentBudget.candidates G 6, x v ≤ 1) :
    let I := CurrentCounting.input G 3 6 (by norm_num) x hx hcap
    ((CurrentRounding.first G 3 I).card + (CurrentRounding.middle G 3 I).card : ℝ) / 4 +
        CurrentRounding.slack G 3 I ≤
      CurrentRounding.objective G 3 I - (CurrentRounding.output G 3 I).card ∧
    ((CurrentRounding.output G 3 I).card : ℝ) ≤
      49 * ((CurrentRounding.first G 3 I).card + (CurrentRounding.middle G 3 I).card) +
        294 * CurrentRounding.slack G 3 I := by
  have hden := PlanarDensity.minor_density G hplanar
  have hs := CurrentRounding.selection_saving G 3
    (CurrentCounting.input G 3 6 (by norm_num) x hx hcap) (by norm_num)
    (MinorDensity.induced_bound G hden)
    (CurrentCounting.high_full_cost G 3 6 (by norm_num) x hx hcap)
  have hc := CurrentCountBound.output_card_le G 3 6 (by norm_num) x hx hcap
    (by norm_num) hden
  norm_num at hs hc
  exact ⟨hs, hc⟩

theorem planar_rounding_on_residual (hplanar : G.IsPlanar)
    (z : ↥(CurrentBudget.candidates G 6 : Set V) → ℝ)
    (hz : PartialOptimum.Feasible (G.induce (CurrentBudget.candidates G 6 : Set V))
      (CurrentBudgetBridge.residualDemands G 6) z)
    (hcap : ∀ v, z v ≤ 1) :
    ∃ x : V → ℝ, (∀ v : ↥(CurrentBudget.candidates G 6 : Set V), x v = z v) ∧
      ∃ hx : feasible (CurrentBudget.auxiliary G 6) x,
      ∃ hc : ∀ v ∈ CurrentBudget.candidates G 6, x v ≤ 1,
      let I := CurrentCounting.input G 3 6 (by norm_num) x hx hc
      ((CurrentRounding.first G 3 I).card + (CurrentRounding.middle G 3 I).card : ℝ) / 4 +
          CurrentRounding.slack G 3 I ≤
        CurrentRounding.objective G 3 I - (CurrentRounding.output G 3 I).card ∧
      ((CurrentRounding.output G 3 I).card : ℝ) ≤
        49 * ((CurrentRounding.first G 3 I).card + (CurrentRounding.middle G 3 I).card) +
          294 * CurrentRounding.slack G 3 I := by
  classical
  let x := InducedExtension.extend (CurrentBudget.candidates G 6) z
  have hx := CurrentBudgetBridge.to_auxiliary G 6 z hz
  have hc : ∀ v ∈ CurrentBudget.candidates G 6, x v ≤ 1 := by
    intro v hv
    simpa only [x, InducedExtension.extend, dif_pos hv] using hcap ⟨v, hv⟩
  refine ⟨x, ?_, hx, hc, planar_rounding G hplanar x hx hc⟩
  intro v
  have hv : v.val ∈ CurrentBudget.candidates G 6 := v.property
  exact dif_pos hv

end Paper.Proposition2PlanarAudit

#print axioms Paper.Proposition2PlanarAudit.planar_rounding
#print axioms Paper.Proposition2PlanarAudit.planar_rounding_on_residual
