import Paper.TotalDomination.IntegerSelectedCount
import Paper.TotalDomination.IntegerMinorDefects
import Paper.Endpoints.Rounding.Slack

/-! The actual integer input satisfies the saving inequality. -/
namespace Paper.TotalDomination.IntegerSetup
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
variable (x : V → ℝ) (identifier : V → ℕ)
variable (hfree : ∀ v, (G.neighborFinset v).Nonempty)

theorem integer_saving (hd : 2 ≤ d)
    (hden : Incidence.InducedDensityBound G ((d:ℝ)/2))
    (hx : CoveringOptimum.Feasible (fun r => G.neighborFinset r) (Z G d) x)
    (hsupport : ∀ v ∉ K G d, x v = 0) :
    0 ≤ penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) ∧
    0 ≤ oversupply G (I G d x identifier hfree) ∧
    (first G (I G d x identifier hfree)).card / 2 +
      surplus G (I G d x identifier hfree) / 4 +
      penalty G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) +
      oversupply G (I G d x identifier hfree) ≤
      objective G (I G d x identifier hfree) (fun v => (c G d v : ℝ)) -
      (output G (I G d x identifier hfree)).card := by
  have hdR : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨hR1,hR2,hR3⟩ := local_conditions G d x identifier hfree
  have hh := rounding_saving G (I G d x identifier hfree) ((d:ℝ)/2)
    (by positivity) hden (by change 2*((d:ℝ)/2) ≤ (d:ℝ); linarith)
    (by change 0 < 3/(2*(d:ℝ)); positivity) (fun v => (c G d v : ℝ))
    (fun v _ => hx.1 v) hsupport
    (fun r hr => hx.2 r (Finset.mem_sdiff.mp hr).1)
    (fun v hv => by
      change (c G d v : ℝ) = 2*((d:ℝ)/2)
      rw [hR1 v hv]; ring)
    (fun v hv => by
      change (hits G (I G d x identifier hfree) v : ℝ) ≤ (c G d v : ℝ)
      exact_mod_cast hR2 v hv)
    (fun v hv he => hR3 v hv (by
      have he' : (d:ℝ) < (hits G (I G d x identifier hfree) v : ℝ) := by linarith
      exact_mod_cast he'))
  refine ⟨hh.1,hh.2.1,?_⟩
  have ht1 : 2*((d:ℝ)/2)*(3/(2*(d:ℝ)))-1 = 1/2 := by field_simp [ne_of_gt hdR]; ring
  have ht2 : 1-((d:ℝ)/2)*(3/(2*(d:ℝ))) = 1/4 := by field_simp [ne_of_gt hdR]; ring
  have hs := hh.2.2
  change (2*((d:ℝ)/2)*(3/(2*(d:ℝ)))-1)*_ +
    (1-((d:ℝ)/2)*(3/(2*(d:ℝ))))*_ + _ + _ ≤ _ at hs
  rw [ht1,ht2] at hs
  linarith

end Paper.TotalDomination.IntegerSetup
#print axioms Paper.TotalDomination.IntegerSetup.integer_saving
