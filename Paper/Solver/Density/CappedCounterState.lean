import Paper.Solver.Density.CappedRationalRounds

/-! A compact exact state for the rational capped update. A message needs
only the fixed local denominator, the growth exponent, and a cap bit; its
receiver reconstructs the rational value. Encoding and bit-length bounds are
separate obligations. No degree bound occurs in the state or transition. -/

namespace Paper.Density.CappedCounterState

structure State where
  denominator : ℕ
  exponent : ℕ
  capped : Bool
  deriving DecidableEq

def scale (m : ℕ) : ℚ := ((m : ℚ) + 1) / m

def decode (cap : ℚ) (m : ℕ) (s : State) : ℚ :=
  if s.capped then cap else scale m ^ s.exponent / (s.denominator : ℚ)

def initial (cap : ℚ) (L : ℕ) : State :=
  ⟨L, 0, decide (cap ≤ 1 / (L : ℚ))⟩

def step (cap : ℚ) (m : ℕ) (blocked : Bool) (s : State) : State :=
  if blocked || s.capped then s
  else if cap ≤ scale m * decode cap m s then { s with capped := true }
  else { s with exponent := s.exponent + 1 }

def Valid (cap : ℚ) (m : ℕ) (s : State) : Prop := decode cap m s ≤ cap

theorem scale_ge_one {m : ℕ} (hm : 0 < m) : 1 ≤ scale m := by
  have hp : (0 : ℚ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ hp).mpr
  linarith

theorem initial_decode (cap : ℚ) (m L : ℕ) :
    decode cap m (initial cap L) = min cap (1 / (L : ℚ)) := by
  simp [initial, decode, min_def]

theorem initial_valid (cap : ℚ) (m L : ℕ) : Valid cap m (initial cap L) := by
  rw [Valid, initial_decode]
  exact min_le_left _ _

/-- Capping is absorbing. An uncapped multiplication is represented by
incrementing the exponent, with no rational numerator stored. -/
theorem step_decode (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (blocked : Bool) (s : State) :
    decode cap m (step cap m blocked s) =
      if blocked then decode cap m s else min cap (scale m * decode cap m s) := by
  cases blocked with
  | true => simp [step]
  | false =>
    cases hc : s.capped with
    | true =>
      have hg : cap ≤ scale m * cap := by
        simpa using mul_le_mul_of_nonneg_right (scale_ge_one hm) hcap
      simp [step, hc, decode, min_eq_left hg]
    | false =>
      have hg : decode cap m { s with exponent := s.exponent + 1 } =
          scale m * decode cap m s := by
        simp only [decode, hc, Bool.false_eq_true, ite_false, pow_succ]
        ring
      by_cases hn : cap ≤ scale m * decode cap m s
      · simp only [step, hc, Bool.false_or, Bool.false_eq_true, ite_false,
          if_pos hn, min_eq_left hn]
        rfl
      · have hlt := le_of_lt (lt_of_not_ge hn)
        simpa only [step, hc, Bool.false_or, Bool.false_eq_true, ite_false,
          if_neg hn, min_eq_right hlt] using hg

theorem step_valid (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (blocked : Bool) (s : State) (hs : Valid cap m s) :
    Valid cap m (step cap m blocked s) := by
  unfold Valid
  rw [step_decode cap hm hcap]
  cases blocked
  · exact min_le_left _ _
  · exact hs

theorem step_denominator (cap : ℚ) (m : ℕ) (blocked : Bool) (s : State) :
    (step cap m blocked s).denominator = s.denominator := by
  unfold step
  split_ifs <;> rfl

theorem step_exponent_le (cap : ℚ) (m : ℕ) (blocked : Bool) (s : State) :
    (step cap m blocked s).exponent ≤ s.exponent + 1 := by
  unfold step
  split_ifs <;> simp

/-- Iteration is indexed only for analysis; each update uses its local bit. -/
def run (cap : ℚ) (m L : ℕ) (blocked : ℕ → Bool) : ℕ → State
  | 0 => initial cap L
  | n + 1 => step cap m (blocked n) (run cap m L blocked n)

theorem run_denominator (cap : ℚ) (m L : ℕ) (blocked : ℕ → Bool) (n : ℕ) :
    (run cap m L blocked n).denominator = L := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run, step_denominator, ih]

theorem run_exponent_le (cap : ℚ) (m L : ℕ) (blocked : ℕ → Bool) (n : ℕ) :
    (run cap m L blocked n).exponent ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact (step_exponent_le cap m (blocked n) (run cap m L blocked n)).trans
      (Nat.add_le_add_right ih 1)

theorem run_valid (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (L : ℕ) (blocked : ℕ → Bool) (n : ℕ) : Valid cap m (run cap m L blocked n) := by
  induction n with
  | zero => exact initial_valid cap m L
  | succ n ih => exact step_valid cap hm hcap (blocked n) _ ih

end Paper.Density.CappedCounterState

#print axioms Paper.Density.CappedCounterState.initial_decode
#print axioms Paper.Density.CappedCounterState.step_decode
#print axioms Paper.Density.CappedCounterState.run_denominator
#print axioms Paper.Density.CappedCounterState.run_exponent_le
#print axioms Paper.Density.CappedCounterState.run_valid
