import Paper.TotalDomination.IntegerSolver
import Paper.TotalDomination.IntegerPlanarDefects
import Paper.Preliminaries.PlanarDensity

/-! Separate solver density and degree threshold, then instantiate the actual
integer algorithm on planar graphs of girth 3, 4 or 6. -/
namespace Paper.TotalDomination.IntegerDefectSolver
open BroadcastModel SevenFoundation
open scoped BigOperators

theorem parameters (rho : ℝ) (hrho : 1 ≤ rho) (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters rho d (IntegerSetup.accuracy d κ),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G rho → (∀ v, (G.neighborFinset v).Nonempty) →
        Incidence.InducedDensityBound G ((d:ℝ)/2) →
        (∀ (x : V → ℝ) (labels : V → ℕ) (hfree : ∀ v, (G.neighborFinset v).Nonempty),
          ((WeightedBudget.defects G d ∩ IntegerSetup.core G d x labels hfree).card:ℝ) ≤
            κ*((IntegerSetup.servedLow G d x labels hfree).card+
              (first G (IntegerSetup.I G d x labels hfree)).card)) →
        ∀ {ids : ℕ} (codec : BitCode V ids),
        (∀ r, ∃ v ∈ IntegerSolver.output G codec p t k b n (by omega), G.Adj r v) ∧
        ((IntegerSolver.output G codec p t k b n (by omega)).card:ℝ) ≤
          d*InitialSelection.totalFractionalNumber G := by
  have hε := IntegerSetup.accuracy_positive d hd hκ
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := IntegerResidualSolver.parameters_general rho hrho d hd _ hε
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hminor hfree hden hdefects ids codec
  have hx := hp G hminor hfree codec
  let x := CoveringOptimum.cap (IntegerResidualSolver.solution G codec p t k b n (by omega : 1 ≤ d))
  let labels := NonintegerSolver.labels V
  let I := IntegerSetup.I G d x labels hfree
  have hobj : objective G I (fun v => (IntegerSetup.c G d v:ℝ)) =
      ∑ v, (IntegerSetup.c G d v:ℝ)*x v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    change (IntegerSetup.c G d v:ℝ)*x v = 0
    have hz : x v = 0 := hx.2.2.1 v hv
    rw [hz,mul_zero]
  have hslack := IntegerSetup.slack G d x labels hfree hd κ hκ hden hx.1 hx.2.1 hx.2.2.1
    (hdefects x labels hfree)
  have hround : ((output G I).card:ℝ) ≤ InitialSelection.residualOptimum G d :=
    Paper.Slack.pays_for_error hε hslack (by rw [hobj];exact hx.2.2.2)
  have hbudget := InitialSelection.fractional_budget G d (by omega) hfree
  have hcard : ((IntegerSetup.finalSelection G d x labels hfree).card:ℝ) ≤
      (IntegerSetup.F G d).card+(output G I).card := by
    exact_mod_cast Finset.card_union_le (IntegerSetup.F G d) (output G I)
  rw [IntegerSolver.output_eq G codec p t k b n (by omega) labels
    NonintegerSolver.labels_strictMono hfree]
  refine ⟨IntegerSetup.final_total_dominates G d x labels hfree,?_⟩
  change ((IntegerSetup.F G d).card:ℝ)+InitialSelection.residualOptimum G d ≤ _ at hbudget
  linarith

/-- Actual planar endpoint, including the critical integer girths. -/
theorem planar_parameters (g d : ℕ) (hg : 3 ≤ g) (hd : 2 ≤ d)
    (hdg : (d:ℝ) = 2*((g:ℝ)/((g:ℝ)-2))) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters 3 d (IntegerSetup.accuracy d (g:ℝ)),
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → (∀ v, (G.neighborFinset v).Nonempty) →
        (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
        ∀ {ids : ℕ} (codec : BitCode V ids),
        (∀ r, ∃ v ∈ IntegerSolver.output G codec p t k b n (by omega), G.Adj r v) ∧
        ((IntegerSolver.output G codec p t k b n (by omega)).card:ℝ) ≤
          d*InitialSelection.totalFractionalNumber G := by
  obtain ⟨p,t,k,b,n,ht,hk,hp⟩ := parameters 3 (by norm_num) d hd (g:ℝ) (Nat.cast_nonneg _)
  refine ⟨p,t,k,b,n,ht,hk,?_⟩
  intro V _ _ G _ hplanar hfree hgirth ids codec
  have hden : Incidence.InducedDensityBound G ((d:ℝ)/2) := by
    have he : (d:ℝ)/2 = (g:ℝ)/((g:ℝ)-2) := by linarith
    rw [he]
    exact CurrentPlanarFaceBound.induced_density hplanar g hg hgirth
  exact hp G (PlanarDensity.minor_density G hplanar) hfree hden
    (fun x labels hf => IntegerSetup.planar_defects G d x labels hf (by omega) g hg hdg hplanar hgirth) codec

end Paper.TotalDomination.IntegerDefectSolver
#print axioms Paper.TotalDomination.IntegerDefectSolver.planar_parameters
