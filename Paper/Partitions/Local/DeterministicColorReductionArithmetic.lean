import Paper.Partitions.Local.DeterministicColorReductionCodec

/-! Pure arithmetic for the actual binary color-reduction width.
Two reductions are at most one shifted ceiling logarithm above a public
degree-dependent threshold. Small widths have a separate constant bound.
This file does not define an iteration or claim a log-star round bound. -/
namespace Paper.DeterministicColorReductionArithmetic

def logStep (b : ℕ) : ℕ := Nat.clog 2 (b + 1)

def factor (Δ : ℕ) : ℕ := 4 * Δ + 1

def logThreshold (Δ : ℕ) : ℕ := 2 ^ (4 * factor Δ)

def threshold (Δ : ℕ) : ℕ := 2 ^ logThreshold Δ

theorem factor_pos (Δ : ℕ) : 1 ≤ factor Δ := by
  unfold factor
  omega

theorem logStep_mono : Monotone logStep := by
  intro b c h
  exact Nat.clog_mono_right 2 (Nat.add_le_add_right h 1)

theorem self_le_two_pow (a : ℕ) : a ≤ 2 ^ a :=
  (Nat.lt_pow_self (by decide : 1 < 2)).le

/-- The elementary exponential domination needed after taking the floor log. -/
theorem square_le_two_pow (m : ℕ) (hm : 4 ≤ m) : m * m ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    calc
      (m + 1) * (m + 1) ≤ 2 * (m * m) := by
        have hh := Nat.mul_le_mul_right m hm
        nlinarith
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]; ring

theorem product_le_square (a m : ℕ) (ha : 1 ≤ a) (hm : 4 * a ≤ m) :
    a * (a + m + 1) ≤ m * m := by
  calc
    a * (a + m + 1) ≤ a * (2 * m) := Nat.mul_le_mul_left a (by omega)
    _ = (2 * a) * m := by ring
    _ ≤ m * m := Nat.mul_le_mul_right m (by omega)

/-- The +1 in logStep is accounted for before bounding the product by a power. -/
theorem logStep_mul (a x : ℕ) (ha : 1 ≤ a) :
    logStep (a * x) ≤ a + Nat.log 2 x + 1 := by
  unfold logStep
  apply Nat.clog_le_of_le_pow
  have hx := Nat.lt_pow_succ_log_self (by decide : 1 < 2) x
  calc
    a * x + 1 ≤ a * (x + 1) := by nlinarith
    _ ≤ a * 2 ^ (Nat.log 2 x + 1) := Nat.mul_le_mul_left a (by omega)
    _ ≤ 2 ^ a * 2 ^ (Nat.log 2 x + 1) :=
      Nat.mul_le_mul_right _ (self_le_two_pow a)
    _ = 2 ^ (a + Nat.log 2 x + 1) := by
      simp only [Nat.pow_add, Nat.mul_assoc]

/-- A scaled logarithm is at most its input above the explicit exponential cutoff. -/
theorem scaled_logStep_le (a x : ℕ) (ha : 1 ≤ a) (hx : 2 ^ (4 * a) ≤ x) :
    a * logStep (a * x) ≤ x := by
  have hm : 4 * a ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by decide : 1 < 2) hx
  have hm4 : 4 ≤ Nat.log 2 x := by omega
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : 0 < 2 ^ (4 * a)) hx
  calc
    a * logStep (a * x) ≤ a * (a + Nat.log 2 x + 1) :=
      Nat.mul_le_mul_left a (logStep_mul a x ha)
    _ ≤ Nat.log 2 x * Nat.log 2 x := product_le_square a _ ha hm
    _ ≤ 2 ^ Nat.log 2 x := square_le_two_pow _ hm4
    _ ≤ x := Nat.pow_log_le_self 2 (Nat.ne_of_gt hxpos)

/-- This bound is derived from the received, actual binary codec width. -/
theorem width_le_scaled (b Δ : ℕ) :
    DeterministicColorReductionCodec.width b Δ ≤ factor Δ * logStep b := by
  calc
    DeterministicColorReductionCodec.width b Δ ≤ 4 * Δ * Nat.clog 2 (b + 1) :=
      DeterministicColorReductionCodec.width_logarithmic b Δ
    _ ≤ factor Δ * logStep b :=
      Nat.mul_le_mul_right _ (Nat.le_succ (4 * Δ))

/-- Two actual reductions are dominated by one shifted ceiling logarithm. -/
theorem two_steps (b Δ : ℕ) (hb : logThreshold Δ ≤ logStep b) :
    DeterministicColorReductionCodec.width
      (DeterministicColorReductionCodec.width b Δ) Δ ≤ logStep b := by
  calc
    DeterministicColorReductionCodec.width
        (DeterministicColorReductionCodec.width b Δ) Δ ≤
        factor Δ * logStep (DeterministicColorReductionCodec.width b Δ) :=
      width_le_scaled _ Δ
    _ ≤ factor Δ * logStep (factor Δ * logStep b) :=
      Nat.mul_le_mul_left _ (logStep_mono (width_le_scaled b Δ))
    _ ≤ logStep b := scaled_logStep_le (factor Δ) (logStep b) (factor_pos Δ) hb

/-- The threshold is chosen from Delta before any graph or identifier width. -/
theorem two_steps_above_threshold (b Δ : ℕ) (hb : threshold Δ ≤ b) :
    DeterministicColorReductionCodec.width
      (DeterministicColorReductionCodec.width b Δ) Δ ≤ logStep b := by
  apply two_steps b Δ
  calc
    logThreshold Δ = Nat.clog 2 (threshold Δ) := by
      unfold threshold
      exact (Nat.clog_pow 2 _ (by decide : 1 < 2)).symm
    _ ≤ logStep b := Nat.clog_mono_right 2 (hb.trans (Nat.le_succ b))

theorem logStep_below_threshold (b Δ : ℕ) (hb : b < threshold Δ) :
    logStep b ≤ logThreshold Δ := by
  apply Nat.clog_le_of_le_pow
  change b + 1 ≤ threshold Δ
  omega

/-- A small incoming width gives a degree-dependent constant outgoing width. -/
theorem width_below_threshold (b Δ : ℕ) (hb : b < threshold Δ) :
    DeterministicColorReductionCodec.width b Δ ≤ factor Δ * logThreshold Δ :=
  (width_le_scaled b Δ).trans (Nat.mul_le_mul_left _ (logStep_below_threshold b Δ hb))

@[simp] theorem two_steps_zero_degree (b : ℕ) :
    DeterministicColorReductionCodec.width
      (DeterministicColorReductionCodec.width b 0) 0 = 0 := by
  simp only [DeterministicColorReductionCodec.width_zero_degree]

@[simp] theorem two_steps_zero_bits (Δ : ℕ) :
    DeterministicColorReductionCodec.width
      (DeterministicColorReductionCodec.width 0 Δ) Δ = 0 := by
  simp only [DeterministicColorReductionCodec.width_zero_bits]

/-- Below the cutoff one may stop; no small-input contraction is assumed. -/
theorem two_steps_or_below_threshold (b Δ : ℕ) :
    b < threshold Δ ∨ DeterministicColorReductionCodec.width
      (DeterministicColorReductionCodec.width b Δ) Δ ≤ logStep b := by
  rcases lt_or_ge b (threshold Δ) with hb | hb
  · exact Or.inl hb
  · exact Or.inr (two_steps_above_threshold b Δ hb)

end Paper.DeterministicColorReductionArithmetic

#print axioms Paper.DeterministicColorReductionArithmetic.square_le_two_pow
#print axioms Paper.DeterministicColorReductionArithmetic.scaled_logStep_le
#print axioms Paper.DeterministicColorReductionArithmetic.two_steps
#print axioms Paper.DeterministicColorReductionArithmetic.two_steps_above_threshold
#print axioms Paper.DeterministicColorReductionArithmetic.width_below_threshold
#print axioms Paper.DeterministicColorReductionArithmetic.two_steps_zero_degree
#print axioms Paper.DeterministicColorReductionArithmetic.two_steps_or_below_threshold
