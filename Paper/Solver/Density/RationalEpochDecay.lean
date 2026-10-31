import Paper.Solver.Density.RationalRequirementDecay

/-! Geometric contraction across the actual padded phases and outer loop.
The only graph-dependent premise is the explicit initial mass bound; this
module does not claim removal of the public degree parameter. -/
namespace Paper.Density.RationalEpochDecay
open BroadcastModel RationalRuntime RationalCounters RationalRequirementDecay
open scoped BigOperators

def scale (m : ℕ) : ℚ := ((m + 1 : ℕ) : ℚ) / m

theorem scale_bounds {m : ℕ} (hm : 1 ≤ m) : 1 < scale m ∧ scale m ≤ 2 := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have h1 : (1 : ℚ) ≤ m := by exact_mod_cast hm
  unfold scale
  push_cast
  constructor
  · apply (lt_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

theorem base_scale {m : ℕ} (hm : 1 ≤ m) : base m * scale m = 1 := by
  have hp : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold base scale
  push_cast
  field_simp

theorem block_power {m : ℕ} (hm : 1 ≤ m) :
    base m ^ (2 * m) * (scale m + 1) ≤ 1 := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have he : 1 + 1 / (m : ℚ) = scale m := by unfold scale; push_cast; field_simp
  have hb := one_add_mul_le_pow (by
    have hr : (0 : ℚ) ≤ 1 / (m : ℚ) := by positivity
    linarith : (-2 : ℚ) ≤ 1 / (m : ℚ)) m
  rw [he] at hb
  have hleft : 1 + (m : ℚ) * (1 / (m : ℚ)) = 2 := by field_simp <;> norm_num
  have htwo : (2 : ℚ) ≤ scale m ^ m := by linarith
  have hlarge : scale m + 1 ≤ scale m ^ (2 * m) := by
    calc
      _ ≤ 4 := by linarith [(scale_bounds hm).2]
      _ ≤ (scale m ^ m) ^ 2 := by nlinarith only [htwo]
      _ = _ := by rw [← pow_mul, Nat.mul_comm m 2]
  have hi : base m ^ (2 * m) * scale m ^ (2 * m) = 1 := by
    rw [← mul_pow, base_scale hm, one_pow]
  exact (mul_le_mul_of_nonneg_left hlarge (pow_nonneg (base_bounds m).1 _)).trans_eq hi

theorem threshold_succ {m : ℕ} (hm : 1 ≤ m) (ep : ℤ) :
    threshold m (ep + 1) = scale m * threshold m ep := by
  have hp : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) / m := by positivity
  unfold threshold scale
  rw [zpow_add₀ (ne_of_gt hp), zpow_one]
  ring

theorem threshold_two {m : ℕ} (hm : 1 ≤ m) (ep : ℤ) :
    threshold m (ep + 2) = scale m ^ 2 * threshold m ep := by
  have he : ep + 2 = (ep + 1) + 1 := by ring
  rw [he, threshold_succ hm, threshold_succ hm]
  ring

private theorem scalar_block (q u θ γ : ℝ) (H : ℕ) (hq : 0 ≤ q) (hu : 1 ≤ u)
    (hθ : 0 ≤ θ) (hγ : γ ≤ u ^ 2 * θ) (hpow : q ^ H * (u + 1) ≤ 1) :
    q ^ H * γ + (1 - q ^ H) * θ ≤ u * θ := by
  have ha := mul_le_mul_of_nonneg_left hγ (pow_nonneg hq H)
  have hb := mul_le_mul_of_nonneg_right hpow (mul_nonneg (sub_nonneg.mpr hu) hθ)
  nlinarith only [ha, hb]

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem iterate_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ) (j : ℕ)
    (s : V → State m K) (hs : ∀ v, Consistent (s v)) (v : V) :
    fullMass G (((phase m K ep).iterate j).run G s) v ≤
      (base m : ℝ) ^ j * fullMass G s v +
        (1 - (base m : ℝ) ^ j) * (threshold m ep : ℝ) := by
  induction j with
  | zero => simp only [Program.iterate, Program.run, pow_zero, one_mul, sub_self, zero_mul, add_zero, le_refl]
  | succ j ih =>
    let a := ((phase m K ep).iterate j).run G s
    have ha : ∀ u, Consistent (a u) :=
      iterate_consistent G _ (phase_consistent G m K ep) j s hs
    have hp : (0 : ℝ) ≤ (base m : ℝ) := by exact_mod_cast (base_bounds m).1
    calc
      _ ≤ (base m : ℝ) * fullMass G a v + (1 - (base m : ℝ)) * (threshold m ep : ℝ) :=
        phase_contraction G hm hk ep a ha v
      _ ≤ (base m : ℝ) * ((base m : ℝ) ^ j * fullMass G s v +
          (1 - (base m : ℝ) ^ j) * (threshold m ep : ℝ)) +
          (1 - (base m : ℝ)) * (threshold m ep : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left ih hp) le_rfl
      _ = _ := by rw [pow_succ]; ring

theorem epoch_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ)
    (s : V → State m K) (hs : ∀ v, Consistent (s v)) (v : V)
    (hγ : fullMass G s v ≤ (threshold m (ep + 2) : ℝ)) :
    fullMass G (((phase m K ep).iterate (2 * m)).run G s) v ≤
      (threshold m (ep + 1) : ℝ) := by
  have hpow : (base m : ℝ) ^ (2 * m) * ((scale m : ℝ) + 1) ≤ 1 := by
    exact_mod_cast block_power hm
  have hinput : fullMass G s v ≤ (scale m : ℝ) ^ 2 * (threshold m ep : ℝ) := by
    simpa only [threshold_two hm, Rat.cast_mul, Rat.cast_pow] using hγ
  have hθ : (0 : ℝ) ≤ (threshold m ep : ℝ) := by
    have hrat : (0 : ℚ) < threshold m ep := by
      unfold threshold
      apply zpow_pos
      positivity
    exact_mod_cast le_of_lt hrat
  have hq : (0 : ℝ) ≤ (base m : ℝ) := by exact_mod_cast (base_bounds m).1
  have hu : (1 : ℝ) ≤ (scale m : ℝ) := by exact_mod_cast le_of_lt (scale_bounds hm).1
  have hB := (iterate_bound G hm hk ep (2 * m) s hs v).trans
    (scalar_block (base m) (scale m) (threshold m ep) (fullMass G s v) (2 * m)
      hq hu hθ hinput hpow)
  simpa only [threshold_succ hm, Rat.cast_mul] using hB

/-- The literal entire outer loop reaches its final requirement-mass bound. -/
theorem outer_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (j : ℕ)
    (s : V → State m K) (hs : ∀ v, Consistent (s v)) (v : V)
    (hγ : fullMass G s v ≤ (threshold m ((j : ℤ) - target m K) : ℝ)) :
    fullMass G ((outer m K j).run G s) v ≤ (threshold m (-(target m K : ℤ)) : ℝ) := by
  induction j generalizing s with
  | zero => simpa only [outer, Program.run, Int.natCast_zero, zero_sub] using hγ
  | succ j ih =>
    let ep : ℤ := (j : ℤ) - target m K - 1
    let a := ((phase m K ep).iterate (2 * m)).run G s
    have ha : ∀ u, Consistent (a u) :=
      iterate_consistent G _ (phase_consistent G m K ep) (2 * m) s hs
    have hin : ep + 2 = ((j + 1 : ℕ) : ℤ) - target m K := by dsimp only [ep]; push_cast; ring
    have hout : ep + 1 = (j : ℤ) - target m K := by dsimp only [ep]; ring
    have hb := epoch_bound G hm hk ep s hs v (by simpa only [hin] using hγ)
    rw [hout] at hb
    exact ih a ha hb

end Paper.Density.RationalEpochDecay

#print axioms Paper.Density.RationalEpochDecay.block_power
#print axioms Paper.Density.RationalEpochDecay.threshold_two
#print axioms Paper.Density.RationalEpochDecay.iterate_bound
#print axioms Paper.Density.RationalEpochDecay.epoch_bound
#print axioms Paper.Density.RationalEpochDecay.outer_bound
