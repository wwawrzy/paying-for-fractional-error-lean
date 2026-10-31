import Paper.Solver.Density.RationalSaturation
import Paper.Solver.Density.RationalEpochDecay

/-! Consecutive increments of the actual descending inner scan grow by at
most the rational scale. Eligibility can only disappear between rounds. -/
namespace Paper.Density.RationalIncrementGrowth
open BroadcastModel RationalRuntime RationalAccounting RationalSaturation RationalRequirementDecay RationalEpochDecay SevenFoundation
open scoped BigOperators

theorem grid_recurrence (m K ed : ℕ) (hed : ed + 1 ≤ K) :
    m * gridIncrement m K ed = (m + 1) * gridIncrement m K (ed + 1) := by
  have he : K - ed = (K - (ed + 1)) + 1 := by omega
  unfold gridIncrement
  rw [he, pow_succ, pow_succ]
  ring

theorem grid_fraction (m K ed : ℕ) (hed : ed ≤ K) :
    (gridIncrement m K ed : ℚ) / denominator m K = ((m : ℚ) / (m + 1)) ^ ed := by
  have hp : (m : ℚ) + 1 ≠ 0 := by positivity
  have he : K - ed + ed = K := by omega
  unfold gridIncrement denominator
  push_cast
  rw [div_pow]
  apply (div_eq_div_iff (pow_ne_zero _ hp) (pow_ne_zero _ (by positivity))).2
  rw [mul_assoc, ← pow_add, he]

theorem first_grid_product {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) :
    threshold m (K : ℤ) * (gridIncrement m K (K - 1) : ℚ) =
      scale m * denominator m K := by
  have hd : (denominator m K : ℚ) ≠ 0 := by unfold denominator; positivity
  have hg : (gridIncrement m K (K - 1) : ℚ) =
      base m ^ (K - 1) * denominator m K :=
    (div_eq_iff hd).mp (grid_fraction m K (K - 1) (by omega))
  have he : K - 1 + 1 = K := by omega
  have hpow : scale m ^ K = scale m ^ (K - 1) * scale m := by
    simpa only [he] using pow_succ (scale m) (K - 1)
  change scale m ^ K * (gridIncrement m K (K - 1) : ℚ) = _
  rw [hg]
  calc
    _ = scale m * (base m * scale m) ^ (K - 1) * denominator m K := by
      rw [hpow, mul_pow]
      ring
    _ = _ := by rw [base_scale hm, one_pow, mul_one]

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def step (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) : ℕ :=
  (eval G (primalRound m K ep ed) s v).increment.value.val

theorem step_formula (m K : ℕ) (ep : ℤ) (ed : ℕ) (hed : ed ≤ K)
    (s : V → State m K) (v : V) :
    step G m K ep ed s v =
      if threshold m ep ≤ localGamma G s v then gridIncrement m K ed else 0 := by
  change (CappedCount.cap (denominator m K)
    (if threshold m ep ≤ localGamma G s v then gridIncrement m K ed else 0)).value.val = _
  split_ifs
  · exact increment_exact m K ed hed
  · rfl

theorem row_step_le_grid (m K : ℕ) (ep : ℤ) (ed : ℕ) (hed : ed ≤ K)
    (s : V → State m K) (v : V) :
    (∑ u ∈ closed G v, step G m K ep ed s u) ≤ (closed G v).card * gridIncrement m K ed := by
  calc
    _ ≤ ∑ _u ∈ closed G v, gridIncrement m K ed := by
      apply Finset.sum_le_sum
      intro u _
      rw [step_formula G m K ep ed hed]
      split_ifs <;> omega
    _ = _ := by simp

theorem first_increment_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (ep : ℤ) (s : V → State m K) (v : V)
    (hdegree : ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    m * (∑ u ∈ closed G v, step G m K ep (K - 1) s u) ≤
      (m + 1) * denominator m K := by
  have hc : ((closed G v).card : ℚ) ≤ threshold m (K : ℤ) := by exact_mod_cast hdegree
  have hr : ((∑ u ∈ closed G v, step G m K ep (K - 1) s u) : ℚ) ≤
      ((closed G v).card : ℚ) * gridIncrement m K (K - 1) := by
    exact_mod_cast row_step_le_grid G m K ep (K - 1) (by omega) s v
  have hs := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (α := ℚ) (gridIncrement m K (K - 1)))
  rw [first_grid_product hm hk] at hs
  have hall := mul_le_mul_of_nonneg_left (hr.trans hs) (Nat.cast_nonneg (α := ℚ) m)
  have he : (m : ℚ) * scale m = (m + 1 : ℕ) := by
    unfold scale
    have hp : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    field_simp
  rw [← mul_assoc, he] at hall
  exact_mod_cast hall

theorem eligibility_previous (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V)
    (h : threshold m ep ≤ localGamma G (after G m K ep ed s) v) :
    threshold m ep ≤ localGamma G s v := by
  have hm := gamma_after_le G m K ep ed s v
  rw [gamma_eq, gamma_eq] at hm
  have hq : localGamma G (after G m K ep ed s) v ≤ localGamma G s v := by
    exact_mod_cast hm
  exact h.trans hq

/-- No physical candidate can start sending at a later inner iteration after
not sending in the preceding iteration. The exact grid ratio bounds growth. -/
theorem step_growth (m K : ℕ) (ep : ℤ) (ed : ℕ) (hed : ed + 1 ≤ K)
    (s : V → State m K) (v : V) :
    m * step G m K ep ed (after G m K ep (ed + 1) s) v ≤
      (m + 1) * step G m K ep (ed + 1) s v := by
  rw [step_formula G m K ep ed (by omega), step_formula G m K ep (ed + 1) hed]
  by_cases h : threshold m ep ≤ localGamma G (after G m K ep (ed + 1) s) v
  · rw [if_pos h, if_pos (eligibility_previous G m K ep (ed + 1) s v h)]
    exact (grid_recurrence m K ed hed).le
  · rw [if_neg h, Nat.mul_zero]
    exact Nat.zero_le _

theorem weight_step (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    (after G m K ep ed s v).weight = (s v).weight +
      ∑ u ∈ closed G v, step G m K ep ed s u := by
  change (s v).weight + (step G m K ep ed s v +
    ∑ u : G.neighborFinset v, step G m K ep ed s u) = _
  rw [UnitDomination.closed_eq_insert, Finset.sum_insert (by simp), Finset.sum_coe_sort]

theorem row_step_growth (m K : ℕ) (ep : ℤ) (ed : ℕ) (hed : ed + 1 ≤ K)
    (s : V → State m K) (v : V) :
    m * (∑ u ∈ closed G v, step G m K ep ed (after G m K ep (ed + 1) s) u) ≤
      (m + 1) * (∑ u ∈ closed G v, step G m K ep (ed + 1) s u) := by
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun u _ => step_growth G m K ep ed hed s u)

/-- If a row remains active after one inner iteration, the next increment
cannot overshoot a full unit by more than the rational grid scale. -/
theorem active_next_increment (m K : ℕ) (ep : ℤ) (ed : ℕ) (hed : ed + 1 ≤ K)
    (s : V → State m K) (v : V)
    (ha : (after G m K ep (ed + 1) s v).active = true) :
    m * (∑ u ∈ closed G v, step G m K ep ed (after G m K ep (ed + 1) s) u) <
      (m + 1) * denominator m K := by
  have hw : (after G m K ep (ed + 1) s v).weight < denominator m K := by
    rw [after_active] at ha
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp ha).2
  have hprev : (∑ u ∈ closed G v, step G m K ep (ed + 1) s u) < denominator m K := by
    rw [weight_step] at hw
    omega
  exact (row_step_growth G m K ep ed hed s v).trans_lt
    (Nat.mul_lt_mul_of_pos_left hprev (by omega))

end Paper.Density.RationalIncrementGrowth

#print axioms Paper.Density.RationalIncrementGrowth.grid_fraction
#print axioms Paper.Density.RationalIncrementGrowth.eligibility_previous
#print axioms Paper.Density.RationalIncrementGrowth.step_growth
#print axioms Paper.Density.RationalIncrementGrowth.weight_step
#print axioms Paper.Density.RationalIncrementGrowth.active_next_increment
#print axioms Paper.Density.RationalIncrementGrowth.first_increment_bound
