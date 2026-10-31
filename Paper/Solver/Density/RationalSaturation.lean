import Paper.Solver.Density.RationalAccounting

/-! The final inner iteration of the actual runtime removes every active
requirement from any candidate whose active mass reaches its threshold.
This is the executable saturation step used in the termination argument. -/
namespace Paper.Density.RationalSaturation
open BroadcastModel RationalRuntime RationalAccounting SevenFoundation
open scoped BigOperators

theorem request_mono {m K : ℕ} (s t : State m K)
    (he : t.exponent = s.exponent) (hstop : t.stopped = s.stopped)
    (ha : t.active = true → s.active = true) :
    requirement m (request t) ≤ requirement m (request s) := by
  by_cases ht : (request t).2 = true
  · have hflags := Bool.and_eq_true_iff.mp ht
    have hs : (request s).2 = true := by
      apply Bool.and_eq_true_iff.mpr
      refine ⟨ha hflags.1, ?_⟩
      simpa only [hstop] using hflags.2
    change (if (request t).2 = true then ((m : ℚ) / (m + 1)) ^ t.exponent.value.val else 0) ≤
      (if (request s).2 = true then ((m : ℚ) / (m + 1)) ^ s.exponent.value.val else 0)
    rw [if_pos ht, if_pos hs, he]
  · have htf : (request t).2 = false := by
      cases h : (request t).2 with
      | false => rfl
      | true => exact False.elim (ht h)
    simp only [requirement, htf, Bool.false_eq_true, if_false]
    split_ifs <;> positivity

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def after (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) : V → State m K :=
  (inner m K ep ed).run G s

theorem after_exponent (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    (after G m K ep ed s v).exponent = (s v).exponent := rfl

theorem after_stopped (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    (after G m K ep ed s v).stopped = (s v).stopped := rfl

theorem after_active (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    (after G m K ep ed s v).active = ((s v).active &&
      decide ((after G m K ep ed s v).weight < denominator m K)) := rfl

theorem source_after_le (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    source (after G m K ep ed s) v ≤ source s v := by
  have hh := request_mono (s v) (after G m K ep ed s v) rfl rfl (by
    intro h
    rw [after_active] at h
    exact (Bool.and_eq_true_iff.mp h).1)
  change (requirement m (request (after G m K ep ed s v)) : ℝ) ≤
    (requirement m (request (s v)) : ℝ)
  exact_mod_cast hh

theorem gamma_after_le (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    gamma G (after G m K ep ed s) v ≤ gamma G s v :=
  Finset.sum_le_sum (fun u _ => source_after_le G m K ep ed s u)

theorem increment_at_threshold (m K : ℕ) (ep : ℤ) (s : V → State m K) (v : V)
    (h : (threshold m ep : ℝ) ≤ gamma G s v) :
    (eval G (primalRound m K ep 0) s v).increment.value.val = denominator m K := by
  have hq : threshold m ep ≤ localGamma G s v := by
    rw [gamma_eq] at h
    exact_mod_cast h
  change (CappedCount.cap (denominator m K)
    (if threshold m ep ≤ localGamma G s v then gridIncrement m K 0 else 0)).value.val = _
  have he : gridIncrement m K 0 = denominator m K := by simp [gridIncrement, denominator]
  simp only [if_pos hq, he, CappedCount.cap, min_self]

private theorem neighbor_term_le (f : V → ℕ) (v r : V) (hv : v ∈ G.neighborFinset r) :
    f v ≤ ∑ u : G.neighborFinset r, f u := by
  rw [Finset.sum_coe_sort]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv

theorem closed_weight_ge (m K : ℕ) (ep : ℤ) (s : V → State m K) (v r : V)
    (hinc : (eval G (primalRound m K ep 0) s v).increment.value.val = denominator m K)
    (hr : r ∈ closed G v) : denominator m K ≤ (after G m K ep 0 s r).weight := by
  let p := eval G (primalRound m K ep 0) s
  change denominator m K ≤ (s r).weight + ((p r).increment.value.val +
    ∑ u : G.neighborFinset r, (p u).increment.value.val)
  rcases (mem_closed G r v).mp hr with hrv | hadj
  · subst r
    change (p v).increment.value.val = denominator m K at hinc
    omega
  · have hv : v ∈ G.neighborFinset r := (G.mem_neighborFinset r v).mpr hadj.symm
    have hs := neighbor_term_le G (fun u => (p u).increment.value.val) v r hv
    dsimp only at hs
    change (p v).increment.value.val = denominator m K at hinc
    omega

theorem source_after_zero (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (r : V)
    (hw : denominator m K ≤ (after G m K ep ed s r).weight) :
    source (after G m K ep ed s) r = 0 := by
  have ha : (after G m K ep ed s r).active = false := by
    rw [after_active]
    simp only [not_lt_of_ge hw, decide_false, Bool.and_false]
  simp only [source, request, ha, Bool.false_and, requirement, Bool.false_eq_true,
    if_false, Rat.cast_zero]

theorem gamma_after_zero (m K : ℕ) (ep : ℤ) (s : V → State m K) (v : V)
    (h : (threshold m ep : ℝ) ≤ gamma G s v) : gamma G (after G m K ep 0 s) v = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact source_after_zero G m K ep 0 s r (closed_weight_ge G m K ep s v r
    (increment_at_threshold G m K ep s v h) hr)

theorem gamma_after_lt {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (s : V → State m K) (v : V) :
    gamma G (after G m K ep 0 s) v < (threshold m ep : ℝ) := by
  have hp : (0 : ℚ) < threshold m ep := by
    unfold threshold
    exact zpow_pos (div_pos (by positivity) (by exact_mod_cast (by omega : 0 < m))) ep
  by_cases h : (threshold m ep : ℝ) ≤ gamma G s v
  · rw [gamma_after_zero G m K ep s v h]
    exact_mod_cast hp
  · exact (gamma_after_le G m K ep 0 s v).trans_lt (lt_of_not_ge h)

/-- Every nonempty actual inner scan ends with active mass below threshold. -/
theorem scan_gamma_lt {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ)
    (s : V → State m K) (v : V) :
    gamma G ((scan m K ep (j + 1)).run G s) v < (threshold m ep : ℝ) := by
  induction j generalizing s with
  | zero => exact gamma_after_lt G hm ep s v
  | succ j ih => exact ih ((inner m K ep (j + 1)).run G s)

end Paper.Density.RationalSaturation

#print axioms Paper.Density.RationalSaturation.source_after_le
#print axioms Paper.Density.RationalSaturation.increment_at_threshold
#print axioms Paper.Density.RationalSaturation.closed_weight_ge
#print axioms Paper.Density.RationalSaturation.gamma_after_zero
#print axioms Paper.Density.RationalSaturation.scan_gamma_lt
