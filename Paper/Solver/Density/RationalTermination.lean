import Paper.Solver.Density.RationalEpochDecay
import Paper.Solver.Density.RationalLiveExponent

/-! Termination of the genuine bounded-degree runtime. The explicit initial
degree/mass bound is a premise of this intermediate theorem; it is not an
endpoint for the algorithm without global degree information. -/
namespace Paper.Density.RationalTermination
open BroadcastModel RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay RationalLiveExponent SevenFoundation
open scoped BigOperators

theorem base_inv (m : ℕ) : base m = (scale m)⁻¹ := by
  simp only [base, scale, inv_div, Nat.cast_add, Nat.cast_one]

theorem threshold_neg_nat (m n : ℕ) : threshold m (-(n : ℤ)) = base m ^ n := by
  change scale m ^ (-(n : ℤ)) = base m ^ n
  rw [zpow_neg, zpow_natCast, ← inv_pow, ← base_inv]

theorem live_lower {m K : ℕ} (s : State m K) (hs : LiveBound s) (hstop : s.stopped = false) :
    threshold m (1 - (target m K : ℤ)) ≤ value s := by
  have hl := hs hstop
  have he : s.exponent.value.val ≤ target m K - 1 := by omega
  have hcount : -((target m K - 1 : ℕ) : ℤ) = 1 - (target m K : ℤ) := by omega
  rw [← hcount, threshold_neg_nat]
  have hv : value s = base m ^ s.exponent.value.val := by simp [value, requirement, hstop, base]
  rw [hv]
  exact pow_le_pow_of_le_one (base_bounds m).1 (base_bounds m).2 he

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def finalState (m K : ℕ) : V → State m K :=
  (outer m K (K + target m K)).run G (fun _ => initial m K)

private theorem self_term_le (f : V → ℝ) (hf : ∀ u, 0 ≤ f u) (v : V) :
    f v ≤ ∑ u ∈ closed G v, f u :=
  Finset.single_le_sum (fun u _ => hf u) (self_mem_closed G v)

theorem final_mass_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    fullMass G (finalState G m K) v ≤ (threshold m (-(target m K : ℤ)) : ℝ) := by
  let s : V → State m K := fun _ => initial m K
  have hi : fullMass G s v = ((closed G v).card : ℝ) := by
    simp [fullMass, s, value, initial, requirement, CappedCount.cap]
  have hcount : ((K + target m K : ℕ) : ℤ) - target m K = (K : ℤ) := by omega
  exact outer_bound G hm hk (K + target m K) s (fun _ => initial_consistent m K) v
    (by rw [hcount, hi]; exact hdegree v)

/-- Every row of the actual finite execution is stopped. No termination,
coverage observer, or fractional solver is supplied as an assumption. -/
theorem all_stopped {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    (finalState G m K v).stopped = true := by
  by_cases hstop : (finalState G m K v).stopped = true
  · exact hstop
  have hfalse : (finalState G m K v).stopped = false := by
    cases h : (finalState G m K v).stopped with
    | false => rfl
    | true => exact False.elim (hstop h)
  have hlower : (threshold m (1 - (target m K : ℤ)) : ℝ) ≤
      (value (finalState G m K v) : ℝ) := by
    exact_mod_cast live_lower (finalState G m K v) (actual_live G hm K v) hfalse
  have hn (u : V) : (0 : ℝ) ≤ (value (finalState G m K u) : ℝ) := by
    exact_mod_cast value_nonneg (finalState G m K u)
  have hself := self_term_le G (fun u => (value (finalState G m K u) : ℝ)) hn v
  change (value (finalState G m K v) : ℝ) ≤ fullMass G (finalState G m K) v at hself
  have hupper := final_mass_bound G hm hk hdegree v
  have hp : (0 : ℚ) < threshold m (-(target m K : ℤ)) := by
    change (0 : ℚ) < scale m ^ (-(target m K : ℤ))
    exact zpow_pos ((by norm_num : (0 : ℚ) < 1).trans (scale_bounds hm).1) _
  have hpR : (0 : ℝ) < (threshold m (-(target m K : ℤ)) : ℝ) := by exact_mod_cast hp
  have hsR : (1 : ℝ) < (scale m : ℝ) := by exact_mod_cast (scale_bounds hm).1
  have hstep := threshold_succ hm (-(target m K : ℤ))
  have he : -(target m K : ℤ) + 1 = 1 - (target m K : ℤ) := by ring
  rw [he] at hstep
  have hstepR : (threshold m (1 - (target m K : ℤ)) : ℝ) =
      (scale m : ℝ) * (threshold m (-(target m K : ℤ)) : ℝ) := by exact_mod_cast hstep
  have hlt : (threshold m (-(target m K : ℤ)) : ℝ) <
      (threshold m (1 - (target m K : ℤ)) : ℝ) := by
    rw [hstepR]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hsR hpR
  exact False.elim (not_lt_of_ge (hlower.trans (hself.trans hupper)) hlt)

theorem actual_coverage {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (v : V) :
    target m K * denominator m K ≤ ∑ u ∈ closed G v, (finalState G m K u).primal :=
  actual_stopped_coverage G m K v (all_stopped G hm hk hdegree v)

end Paper.Density.RationalTermination

#print axioms Paper.Density.RationalTermination.live_lower
#print axioms Paper.Density.RationalTermination.final_mass_bound
#print axioms Paper.Density.RationalTermination.all_stopped
#print axioms Paper.Density.RationalTermination.actual_coverage
