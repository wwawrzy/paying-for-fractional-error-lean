import Paper.Endpoints.Bounds.CurrentTheoremB

/-! The solver-independent implication in the revised STOC density proposition.
The external solver's feasibility and objective guarantee are explicit
hypotheses. No claim about its execution, degree knowledge, or round bound
is introduced as an axiom. Capping is part of the existing rounding map. -/

namespace Paper.CurrentDensityFromFractional
open SevenFoundation CurrentTheoremB
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact paper slack turns any sufficiently accurate feasible
fractional solution into the claimed dominating set. -/
theorem output_bound (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a)
    (hden : Incidence.InducedDensityBound G (a : ℝ))
    (x : V → ℝ) (hx : feasible (ordinary G) x)
    (hsolver : (∑ v, x v) ≤ (1 + (delta a : ℝ)) * fractionalNumber G) :
    dominates G (nonintegerRounded G a ha hnoninteger x hx) ∧
      ((nonintegerRounded G a ha hnoninteger x hx).card : ℝ) ≤
        (2 * (a : ℝ) + 1) * fractionalNumber G := by
  obtain ⟨m, h, hm, hratio, hmath, hprogram⟩ := noninteger_branch a ha hnoninteger
  obtain ⟨hdelta, hleast, hopt, hround⟩ := hmath G hden
  obtain ⟨hdom, hslack, hpay⟩ := hround x hx
  refine ⟨hdom, ?_⟩
  rw [← hopt]
  apply hpay
  rw [CurrentNonintegerTransformation.transformedCost_eq, hopt, ordinary_cost]
  have hb : 0 ≤ 2 * (a : ℝ) + 1 := by
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  calc
    _ ≤ (2 * (a : ℝ) + 1) * ((1 + (delta a : ℝ)) * fractionalNumber G) :=
      mul_le_mul_of_nonneg_left hsolver hb
    _ = _ := by ring

end Paper.CurrentDensityFromFractional

#print axioms Paper.CurrentDensityFromFractional.output_bound
