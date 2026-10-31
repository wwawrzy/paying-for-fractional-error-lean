import Paper.TotalDomination.FractionalRepair
import Paper.Preliminaries.PathPowerTotalGeometry

/-! An actual open-neighborhood fractional cover of the lower-bound family.
The additive boundary loss is independent of path length. -/
namespace Paper.TotalDomination.PathPowerFractional
open PathPowerTreewidth

theorem number_bound (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) :
    FractionalSolver.fractionalNumber (graph n t) ≤ (n:ℝ)/(2*(t:ℝ))+2*t := by
  have hf := PathPowerTotal.isolate_free n t hn ht
  have hd : (0:ℝ) < 2*(t:ℝ) := by
    have hh : (1:ℝ) ≤ t := by exact_mod_cast ht
    positivity
  have hh := FractionalRepair.number_bound (graph n t) hf (PathPowerTotal.boundary n t)
    (2*(t:ℝ)) hd (fun v hv => by exact_mod_cast PathPowerTotal.degree_lower n t v hv)
  have hB : ((PathPowerTotal.boundary n t).card:ℝ) ≤ 2*(t:ℝ) := by
    exact_mod_cast PathPowerTotal.boundary_card n t
  change FractionalSolver.fractionalNumber (graph n t) ≤ _ at hh
  simp only [Fintype.card_fin] at hh
  linarith

end Paper.TotalDomination.PathPowerFractional
#print axioms Paper.TotalDomination.PathPowerFractional.number_bound
