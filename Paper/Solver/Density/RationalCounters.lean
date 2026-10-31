import Paper.Solver.Density.RationalBalance

/-! Exact requirement-counter bookkeeping of the executable. Saturation of
the finite requirement exponent is inactive whenever the row remains live;
every stopped row has already received the prescribed covering mass. -/
namespace Paper.Density.RationalCounters
open BroadcastModel RationalRuntime
open scoped BigOperators

def Consistent {m K : ℕ} (s : State m K) : Prop :=
  (s.stopped = true → target m K * denominator m K ≤ s.fulfilled) ∧
  (s.stopped = false → s.fulfilled = s.exponent.value.val * denominator m K + s.weight)

theorem initial_consistent (m K : ℕ) : Consistent (initial m K) := by
  constructor
  · simp [initial]
  · simp [initial, CappedCount.cap]

theorem add_consistent {m K : ℕ} (s : State m K) (n : ℕ) (active : Bool)
    (hs : Consistent s) :
    Consistent { s with weight := s.weight + n, fulfilled := s.fulfilled + n, active := active } := by
  constructor
  · intro hstop
    exact (hs.1 hstop).trans (Nat.le_add_right _ _)
  · intro hstop
    have hacc := hs.2 hstop
    dsimp only
    omega

theorem exponent_uncapped {m K : ℕ} (s : State m K)
    (hacc : s.fulfilled = s.exponent.value.val * denominator m K + s.weight)
    (hlive : s.fulfilled < target m K * denominator m K) :
    s.exponent.value.val + s.weight / denominator m K ≤ target m K := by
  have hD : 0 < denominator m K := by unfold denominator; positivity
  have hmul : (s.exponent.value.val + s.weight / denominator m K) * denominator m K ≤
      s.fulfilled := by
    rw [Nat.add_mul, hacc]
    exact Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
  by_contra hn
  have hbig : target m K * denominator m K <
      (s.exponent.value.val + s.weight / denominator m K) * denominator m K :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hn) hD
  omega

theorem clean_consistent {m K : ℕ} (s : State m K) (hs : Consistent s) :
    Consistent (clean s) := by
  unfold clean
  split_ifs with hw hf
  · constructor
    · intro _
      exact hf
    · intro h
      contradiction
  · constructor
    · intro h
      exact hs.1 h
    · intro h
      have hacc := hs.2 h
      have hcap := exponent_uncapped s hacc (Nat.lt_of_not_ge hf)
      change s.fulfilled = min (s.exponent.value.val + s.weight / denominator m K)
        (target m K) * denominator m K + s.weight % denominator m K
      rw [min_eq_left hcap, Nat.add_mul]
      have hdiv := Nat.mod_add_div s.weight (denominator m K)
      nlinarith only [hacc, hdiv]
  · exact hs

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inner_consistent (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K)
    (hs : ∀ v, Consistent (s v)) : ∀ v, Consistent ((inner m K ep ed).run G s v) := by
  let t := eval G (primalRound m K ep ed) s
  have ht (v : V) : Consistent (t v) := hs v
  intro v
  exact add_consistent (t v) _ _ (ht v)

theorem scan_consistent (m K : ℕ) (ep : ℤ) (j : ℕ) (s : V → State m K)
    (hs : ∀ v, Consistent (s v)) : ∀ v, Consistent ((scan m K ep j).run G s v) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih => exact ih _ (inner_consistent G m K ep j s hs)

theorem phase_consistent (m K : ℕ) (ep : ℤ) (s : V → State m K)
    (hs : ∀ v, Consistent (s v)) : ∀ v, Consistent ((phase m K ep).run G s v) := by
  have hstart : ∀ v, Consistent ({(s v) with active := !(s v).stopped}) := hs
  intro v
  exact clean_consistent _ (scan_consistent G m K ep K _ hstart v)

theorem iterate_consistent {m K : ℕ} (P : Program V (State m K) (State m K))
    (hP : ∀ s, (∀ v, Consistent (s v)) → ∀ v, Consistent (P.run G s v))
    (j : ℕ) (s : V → State m K) (hs : ∀ v, Consistent (s v)) :
    ∀ v, Consistent ((P.iterate j).run G s v) := by
  induction j with
  | zero => exact hs
  | succ j ih => exact hP _ ih

theorem outer_consistent (m K j : ℕ) (s : V → State m K)
    (hs : ∀ v, Consistent (s v)) : ∀ v, Consistent ((outer m K j).run G s v) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih =>
    apply ih
    exact iterate_consistent G _ (phase_consistent G m K _) _ s hs

theorem actual_consistent (m K : ℕ) (v : V) :
    Consistent ((outer (V := V) m K (K + target m K)).run G (fun _ => initial m K) v) :=
  outer_consistent G m K (K + target m K) _ (fun _ => initial_consistent m K) v

/-- Each row which the literal protocol has marked finished already has its
full target coverage. Termination of every row is a separate obligation. -/
theorem actual_stopped_coverage (m K : ℕ) (v : V) :
    let s := (outer (V := V) m K (K + target m K)).run G (fun _ => initial m K)
    (s v).stopped = true → target m K * denominator m K ≤
      ∑ u ∈ SevenFoundation.closed G v, (s u).primal := by
  dsimp only
  intro hstop
  exact ((actual_consistent G m K v).1 hstop).trans_eq
    (RationalBalance.actual_fulfilled G m K v)

end Paper.Density.RationalCounters

#print axioms Paper.Density.RationalCounters.exponent_uncapped
#print axioms Paper.Density.RationalCounters.clean_consistent
#print axioms Paper.Density.RationalCounters.actual_consistent
#print axioms Paper.Density.RationalCounters.actual_stopped_coverage
