import Paper.Solver.Density.RationalTermination

/-! Feasibility of the rational vector returned by the literal execution.
The public initial degree bound remains explicit in this intermediate result. -/
namespace Paper.Density.RationalFeasibility
open BroadcastModel RationalRuntime RationalTermination SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem output_eq (m K : ℕ) (v : V) :
    (program m K).run G (fun _ => PUnit.unit) v =
      ((finalState G m K v).primal : ℚ) / (denominator m K * target m K) := rfl

theorem denominator_pos {m K : ℕ} (hm : 1 ≤ m) :
    0 < denominator m K * target m K := by
  apply Nat.mul_pos
  · exact pow_pos (by omega) _
  · exact Nat.mul_pos (by omega) (by omega)

def output (m K : ℕ) (v : V) : ℝ :=
  (((program (V := V) m K).run G (fun _ => PUnit.unit) v : ℚ) : ℝ)

theorem output_fraction (m K : ℕ) (v : V) :
    output G m K v = ((finalState G m K v).primal : ℝ) /
      ((denominator m K * target m K : ℕ) : ℝ) := by
  simp only [output, output_eq, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Nat.cast_mul]

theorem output_nonneg (m K : ℕ) (v : V) : 0 ≤ output G m K v := by
  rw [output_fraction]
  positivity

theorem output_covers {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    1 ≤ UnitDomination.mass G (output G m K) v := by
  have hcover := actual_coverage G hm hk hdegree v
  have hreal : ((denominator m K * target m K : ℕ) : ℝ) ≤
      ∑ u ∈ closed G v, ((finalState G m K u).primal : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using hcover)
  have hd : (0 : ℝ) < ((denominator m K * target m K : ℕ) : ℝ) := by
    exact_mod_cast denominator_pos (K := K) hm
  unfold UnitDomination.mass
  simp_rw [output_fraction]
  rw [← Finset.sum_div]
  exact (le_div_iff₀ hd).2 (by simpa only [one_mul] using hreal)

/-- This is a theorem about the actual output, without an input fractional
vector or a supplied coverage/termination contract. -/
theorem ordinary_feasible {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    feasible (ordinary G) (output G m K) :=
  (UnitDomination.ordinary_feasible G _).2
    ⟨output_nonneg G m K, output_covers G hm hk hdegree⟩

end Paper.Density.RationalFeasibility

#print axioms Paper.Density.RationalFeasibility.output_eq
#print axioms Paper.Density.RationalFeasibility.output_fraction
#print axioms Paper.Density.RationalFeasibility.output_covers
#print axioms Paper.Density.RationalFeasibility.ordinary_feasible
