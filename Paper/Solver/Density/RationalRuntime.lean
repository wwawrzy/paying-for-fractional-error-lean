import Paper.Preliminaries.BinaryCounter

/-! The primal/requirement execution of ETH report 426, Algorithm 1, for
unit-cost domination. A fixed rational base replaces irrational roots.
Only requirement exponents/control bits and fixed-grid primal increments
are broadcast. Dual accounting variables are absent from the executable.
The loop threshold follows Lemmas 4.1 and 4.3 (the displayed line 7 of
Algorithm 1 has the reciprocal typo). -/
namespace Paper.Density.RationalRuntime
open BroadcastModel
open scoped BigOperators

def target (m K : ℕ) : ℕ := m * (K + 1)
def denominator (m K : ℕ) : ℕ := (m + 1) ^ K
def bits (M : ℕ) : ℕ := 2 * Nat.clog 2 (M + 2)

def countCode (M : ℕ) : BitCode (CappedCount.Count M) (bits M) :=
  BinaryCounter.bounded (Nat.clog 2 (M + 2)) M (by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (M + 2)
    omega)

structure State (m K : ℕ) where
  primal : ℕ
  weight : ℕ
  fulfilled : ℕ
  exponent : CappedCount.Count (target m K)
  stopped : Bool
  active : Bool
  increment : CappedCount.Count (denominator m K)

def initial (m K : ℕ) : State m K :=
  ⟨0, 0, 0, CappedCount.cap _ 0, false, true, CappedCount.cap _ 0⟩

abbrev Requirement (m K : ℕ) := CappedCount.Count (target m K) × Bool

def request {m K : ℕ} (s : State m K) : Requirement m K :=
  (s.exponent, s.active && !s.stopped)

def requirement (m : ℕ) {K : ℕ} (r : Requirement m K) : ℚ :=
  if r.2 then ((m : ℚ) / (m + 1)) ^ r.1.value.val else 0

def threshold (m : ℕ) (ep : ℤ) : ℚ := (((m + 1 : ℕ) : ℚ) / m) ^ ep

def gridIncrement (m K ed : ℕ) : ℕ := m ^ ed * (m + 1) ^ (K - ed)

variable {V : Type} [DecidableEq V]

def primalRound (m K : ℕ) (ep : ℤ) (ed : ℕ) :
    Round V (State m K) (State m K) (Requirement m K) where
  send _ _ s := request s
  update _ N s messages :=
    let gamma := requirement m (request s) + ∑ u : N, requirement m (messages u)
    let dx := if threshold m ep ≤ gamma then gridIncrement m K ed else 0
    let inc := CappedCount.cap (denominator m K) dx
    { s with primal := s.primal + inc.value.val, increment := inc }

def dualRound (m K : ℕ) : Round V (State m K) (State m K)
    (CappedCount.Count (denominator m K)) where
  send _ _ s := s.increment
  update _ N s messages :=
    let dw := s.increment.value.val + ∑ u : N, (messages u).value.val
    let w := s.weight + dw
    { s with weight := w, fulfilled := s.fulfilled + dw, active := s.active && decide (w < denominator m K) }

def clean {m K : ℕ} (s : State m K) : State m K :=
  if denominator m K ≤ s.weight then
    if target m K * denominator m K ≤ s.fulfilled then
      { s with stopped := true, active := false, weight := 0 }
    else
      { s with weight := s.weight % denominator m K, exponent := CappedCount.cap (target m K) (s.exponent.value.val + s.weight / denominator m K) }
  else s

def inner (m K : ℕ) (ep : ℤ) (ed : ℕ) : Program V (State m K) (State m K) :=
  .seq (.broadcast (bits (target m K) + 1) ((countCode (target m K)).pairBool)
    (primalRound m K ep ed))
    (.broadcast (bits (denominator m K)) (countCode (denominator m K)) (dualRound m K))

def scan (m K : ℕ) (ep : ℤ) : ℕ → Program V (State m K) (State m K)
  | 0 => .local fun _ _ s => s
  | j + 1 => .seq (inner m K ep j) (scan m K ep j)

def phase (m K : ℕ) (ep : ℤ) : Program V (State m K) (State m K) :=
  .seq (.local fun _ _ s => { s with active := !s.stopped })
    (.seq (scan m K ep K) (.local fun _ _ s => clean s))

def outer (m K : ℕ) : ℕ → Program V (State m K) (State m K)
  | 0 => .local fun _ _ s => s
  | j + 1 => .seq ((phase m K ((j : ℤ) - target m K - 1)).iterate (2 * m))
      (outer m K j)

def program (m K : ℕ) : Program V PUnit ℚ :=
  .seq (.local fun _ _ _ => initial m K)
    (.seq (outer m K (K + target m K))
      (.local fun _ _ s => (s.primal : ℚ) / (denominator m K * target m K)))

theorem gridIncrement_le (m K ed : ℕ) (hed : ed ≤ K) :
    gridIncrement m K ed ≤ denominator m K := by
  unfold gridIncrement denominator
  calc
    _ ≤ (m + 1) ^ ed * (m + 1) ^ (K - ed) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : m ≤ m + 1) ed)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le hed]

theorem increment_exact (m K ed : ℕ) (hed : ed ≤ K) :
    (CappedCount.cap (denominator m K) (gridIncrement m K ed)).value.val =
      gridIncrement m K ed := min_eq_left (gridIncrement_le m K ed hed)

omit [DecidableEq V] in
theorem inner_rounds (m K : ℕ) (ep : ℤ) (ed : ℕ) :
    (inner (V := V) m K ep ed).rounds = 2 := rfl

omit [DecidableEq V] in
theorem scan_rounds (m K : ℕ) (ep : ℤ) (j : ℕ) :
    (scan (V := V) m K ep j).rounds = 2 * j := by
  induction j with
  | zero => simp only [scan, Program.rounds, Nat.mul_zero]
  | succ j ih => simp only [scan, Program.rounds, inner_rounds, ih]; omega

theorem phase_rounds (m K : ℕ) (ep : ℤ) :
    (phase (V := V) m K ep).rounds = 2 * K := by
  simp only [phase, Program.rounds, scan_rounds, Nat.zero_add, Nat.add_zero]

theorem outer_rounds (m K j : ℕ) :
    (outer (V := V) m K j).rounds = j * (2 * m) * (2 * K) := by
  induction j with
  | zero => simp only [outer, Program.rounds, Nat.zero_mul]
  | succ j ih =>
    simp only [outer, Program.rounds, Program.iterate_rounds, phase_rounds, ih]
    ring

theorem rounds (m K : ℕ) :
    (program (V := V) m K).rounds = (K + target m K) * (2 * m) * (2 * K) := by
  simp only [program, Program.rounds, outer_rounds, Nat.zero_add, Nat.add_zero]

def messageBound (m K : ℕ) : ℕ := max (bits (target m K) + 1) (bits (denominator m K))

omit [DecidableEq V] in
theorem scan_bits (m K : ℕ) (ep : ℤ) (j : ℕ) :
    (scan (V := V) m K ep j).maxBits ≤ messageBound m K := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    exact max_le (le_refl (messageBound m K)) ih

theorem phase_bits (m K : ℕ) (ep : ℤ) :
    (phase (V := V) m K ep).maxBits ≤ messageBound m K := by
  simpa only [phase, Program.maxBits, Nat.zero_max, Nat.max_zero] using scan_bits (V := V) m K ep K

theorem outer_bits (m K j : ℕ) :
    (outer (V := V) m K j).maxBits ≤ messageBound m K := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    exact max_le ((Program.iterate_maxBits _ _).trans (phase_bits m K _)) ih

theorem maxBits (m K : ℕ) :
    (program (V := V) m K).maxBits ≤ messageBound m K := by
  simpa only [program, Program.maxBits, Nat.zero_max, Nat.max_zero] using
    outer_bits (V := V) m K (K + target m K)

end Paper.Density.RationalRuntime

#print axioms Paper.Density.RationalRuntime.gridIncrement_le
#print axioms Paper.Density.RationalRuntime.increment_exact
#print axioms Paper.Density.RationalRuntime.rounds
#print axioms Paper.Density.RationalRuntime.maxBits
