import Paper.Partitions.Local.DeterministicColorReductionArithmetic

/-! Binary ceiling log-star and a public scalar color-width schedule.
The genuine logarithm is clog2(n), with base case n <= 1. The shifted
logarithm from the codec estimate is used only in the four-step bridge.
The schedule applies the actual Codec.width, stopping below a threshold
depending only on Delta. No varying-width distributed program or bound
in terms of the graph order is claimed here. -/
namespace Paper.DeterministicColorReductionLogStar
open DeterministicColorReductionArithmetic

theorem clog_lt_self (n : ℕ) (hn : 1 < n) : Nat.clog 2 n < n := by
  have hp : n - 1 < 2 ^ (n - 1) := Nat.lt_pow_self (by decide : 1 < 2)
  have hc : Nat.clog 2 n ≤ n - 1 := Nat.clog_le_of_le_pow (by omega)
  omega

/-- The standard binary ceiling iterated logarithm, terminating at 0 or 1. -/
def logStar (n : ℕ) : ℕ :=
  if hn : n ≤ 1 then 0 else logStar (Nat.clog 2 n) + 1
termination_by n
decreasing_by exact clog_lt_self n (by omega)

theorem logStar_small (n : ℕ) (hn : n ≤ 1) : logStar n = 0 := by
  rw [logStar]
  simp only [dif_pos hn, if_pos hn]

theorem logStar_step (n : ℕ) (hn : 1 < n) :
    logStar n = logStar (Nat.clog 2 n) + 1 := by
  rw [logStar]
  simp only [dif_neg (by omega : ¬ n ≤ 1), if_neg (by omega : ¬ n ≤ 1)]

def ceilingRun : ℕ → ℕ → ℕ
  | 0, n => n
  | t + 1, n => ceilingRun t (Nat.clog 2 n)

theorem ceilingRun_logStar (n : ℕ) : ceilingRun (logStar n) n ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 1
    · rw [logStar_small n hn]
      exact hn
    · rw [logStar_step n (by omega)]
      exact ih (Nat.clog 2 n) (clog_lt_self n (by omega))

/-- logStar is the least number of genuine ceiling logarithms reaching <=1. -/
theorem logStar_minimal (t n : ℕ) (h : ceilingRun t n ≤ 1) : logStar n ≤ t := by
  induction t generalizing n with
  | zero => exact (logStar_small n h).le
  | succ t ih =>
    by_cases hn : n ≤ 1
    · rw [logStar_small n hn]
      exact Nat.zero_le _
    · rw [logStar_step n (by omega)]
      exact Nat.add_le_add_right (ih (Nat.clog 2 n) h) 1

theorem logStar_mono : Monotone logStar := by
  intro a b hab
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb : b ≤ 1
    · rw [logStar_small a (hab.trans hb), logStar_small b hb]
    · by_cases ha : a ≤ 1
      · rw [logStar_small a ha]
        exact Nat.zero_le _
      · rw [logStar_step a (by omega), logStar_step b (by omega)]
        exact Nat.add_le_add_right
          (ih (Nat.clog 2 b) (clog_lt_self b (by omega)) (a := Nat.clog 2 a)
            (Nat.clog_mono_right 2 hab)) 1

theorem add_two_le_two_pow (k : ℕ) (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Nat.pow_succ]
    have hp : 0 < 2 ^ k := by positivity
    omega

theorem logStep_le_clog_succ (b : ℕ) : logStep b ≤ Nat.clog 2 b + 1 := by
  unfold logStep
  apply Nat.clog_le_of_le_pow
  have hp := Nat.le_pow_clog (by decide : 1 < 2) b
  have hpos : 0 < 2 ^ Nat.clog 2 b := by positivity
  rw [Nat.pow_succ]
  omega

/-- Two shifted logs are at most one genuine log, away from the small base case. -/
theorem logStep_twice_le_clog (b : ℕ) (hb : 3 ≤ b) :
    logStep (logStep b) ≤ Nat.clog 2 b := by
  have hk : 2 ≤ Nat.clog 2 b := by
    have h : 1 < Nat.clog 2 b :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
    omega
  calc
    logStep (logStep b) ≤ logStep (Nat.clog 2 b + 1) :=
      logStep_mono (logStep_le_clog_succ b)
    _ ≤ Nat.clog 2 b := Nat.clog_le_of_le_pow (add_two_le_two_pow _ hk)

theorem threshold_gt_two (Δ : ℕ) : 2 < threshold Δ := by
  have ha := factor_pos Δ
  have hp := self_le_two_pow (4 * factor Δ)
  change 4 * factor Δ ≤ logThreshold Δ at hp
  have ht : logThreshold Δ < threshold Δ := Nat.lt_pow_self (by decide : 1 < 2)
  omega

/-- A stopped step retains the current width; an active step uses the real codec. -/
def step (Δ b : ℕ) : ℕ :=
  if b < threshold Δ then b else DeterministicColorReductionCodec.width b Δ

theorem step_small (Δ b : ℕ) (hb : b < threshold Δ) : step Δ b = b := by
  simp only [step, if_pos hb]

theorem step_large (Δ b : ℕ) (hb : threshold Δ ≤ b) :
    step Δ b = DeterministicColorReductionCodec.width b Δ := by
  simp only [step, if_neg (by omega : ¬ b < threshold Δ)]

def run (Δ : ℕ) : ℕ → ℕ → ℕ
  | 0, b => b
  | t + 1, b => run Δ t (step Δ b)

theorem run_small (Δ t b : ℕ) (hb : b < threshold Δ) : run Δ t b = b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change run Δ t (step Δ b) = b
    rw [step_small Δ b hb]
    exact ih

theorem run_add (Δ s t b : ℕ) : run Δ (s + t) b = run Δ t (run Δ s b) := by
  induction s generalizing b with
  | zero => simp only [Nat.zero_add, run]
  | succ s ih =>
    simp only [Nat.succ_add, run]
    exact ih (step Δ b)

theorem two_steps_or_stopped (b Δ : ℕ) :
    step Δ (step Δ b) < threshold Δ ∨ step Δ (step Δ b) ≤ logStep b := by
  by_cases h0 : b < threshold Δ
  · exact Or.inl (by simpa only [step_small Δ b h0] using h0)
  · by_cases h1 : step Δ b < threshold Δ
    · exact Or.inl (by simpa only [step_small Δ (step Δ b) h1] using h1)
    · apply Or.inr
      rw [step_large Δ (step Δ b) (by omega), step_large Δ b (by omega)]
      exact two_steps_above_threshold b Δ (by omega)

/-- Four actual reductions dominate a genuine log unless the schedule stopped. -/
theorem four_steps_or_stopped (b Δ : ℕ) :
    run Δ 4 b < threshold Δ ∨ run Δ 4 b ≤ Nat.clog 2 b := by
  change step Δ (step Δ (step Δ (step Δ b))) < threshold Δ ∨
    step Δ (step Δ (step Δ (step Δ b))) ≤ Nat.clog 2 b
  by_cases hb : b ≤ 2
  · have hs : b < threshold Δ := lt_of_le_of_lt hb (threshold_gt_two Δ)
    exact Or.inl (by simpa only [step_small Δ b hs] using hs)
  · rcases two_steps_or_stopped b Δ with hs | hp
    · exact Or.inl (by simpa only [step_small Δ (step Δ (step Δ b)) hs] using hs)
    · rcases two_steps_or_stopped (step Δ (step Δ b)) Δ with hs | hp'
      · exact Or.inl hs
      · exact Or.inr (hp'.trans ((logStep_mono hp).trans (logStep_twice_le_clog b (by omega))))

/-- A public budget for any incoming width bounded by b, with no graph input. -/
theorem schedule_small_of_le (b Δ : ℕ) :
    ∀ a, a ≤ b → run Δ (4 * logStar b) a < threshold Δ := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a hab
    by_cases ha : a < threshold Δ
    · simpa only [run_small Δ (4 * logStar b) a ha] using ha
    · have hb : 1 < b := by
        have ht := threshold_gt_two Δ
        omega
      have hbudget : 4 * logStar b = 4 + 4 * logStar (Nat.clog 2 b) := by
        rw [logStar_step b hb]
        omega
      rw [hbudget, run_add]
      rcases four_steps_or_stopped a Δ with hs | hp
      · simpa only [run_small Δ (4 * logStar (Nat.clog 2 b)) (run Δ 4 a) hs] using hs
      · exact ih (Nat.clog 2 b) (clog_lt_self b hb) (run Δ 4 a)
          (hp.trans (Nat.clog_mono_right 2 hab))

theorem schedule_small (b Δ : ℕ) : run Δ (4 * logStar b) b < threshold Δ :=
  schedule_small_of_le b Δ b le_rfl

/-- Number of executed reductions; stopped slots do not contribute a round. -/
def usedRounds (Δ : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, b => if b < threshold Δ then 0
      else usedRounds Δ t (DeterministicColorReductionCodec.width b Δ) + 1

theorem usedRounds_le (Δ t b : ℕ) : usedRounds Δ t b ≤ t := by
  induction t generalizing b with
  | zero => exact le_rfl
  | succ t ih =>
    simp only [usedRounds]
    split_ifs with hb
    · exact Nat.zero_le _
    · exact Nat.add_le_add_right (ih _) 1

theorem run_usedRounds (Δ t b : ℕ) :
    run Δ (usedRounds Δ t b) b = run Δ t b := by
  induction t generalizing b with
  | zero => rfl
  | succ t ih =>
    by_cases hb : b < threshold Δ
    · have hu : usedRounds Δ (t + 1) b = 0 := by simp only [usedRounds, if_pos hb]
      rw [hu]
      exact (run_small Δ (t + 1) b hb).symm
    · have hu : usedRounds Δ (t + 1) b =
          usedRounds Δ t (DeterministicColorReductionCodec.width b Δ) + 1 := by
        simp only [usedRounds, if_neg hb]
      rw [hu]
      change run Δ (usedRounds Δ t (DeterministicColorReductionCodec.width b Δ)) (step Δ b) =
        run Δ t (step Δ b)
      rw [step_large Δ b (by omega)]
      exact ih (DeterministicColorReductionCodec.width b Δ)

/-- The actual stopped prefix has at most 4*logStar(b) reductions and bounded width. -/
theorem public_schedule (b Δ : ℕ) :
    usedRounds Δ (4 * logStar b) b ≤ 4 * logStar b ∧
    run Δ (usedRounds Δ (4 * logStar b) b) b < threshold Δ := by
  constructor
  · exact usedRounds_le Δ _ b
  · rw [run_usedRounds]
    exact schedule_small b Δ

end Paper.DeterministicColorReductionLogStar

#print axioms Paper.DeterministicColorReductionLogStar.ceilingRun_logStar
#print axioms Paper.DeterministicColorReductionLogStar.logStar_minimal
#print axioms Paper.DeterministicColorReductionLogStar.logStar_mono
#print axioms Paper.DeterministicColorReductionLogStar.logStep_twice_le_clog
#print axioms Paper.DeterministicColorReductionLogStar.four_steps_or_stopped
#print axioms Paper.DeterministicColorReductionLogStar.schedule_small
#print axioms Paper.DeterministicColorReductionLogStar.public_schedule
