import Paper.Solver.Density.RationalEpochCharge

/-! A forward index for the genuine descending outer execution. The trace
is proved equal to the actual ledger, not supplied as an execution contract. -/
namespace Paper.Density.RationalEpochTrace
open RationalRuntime RationalCounters RationalRequirementDecay RationalEpochDecay
open RationalDualLedger RationalPendingBound RationalPendingExecution RationalEpochCharge SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def epoch (m K j : ℕ) : ℤ := (K : ℤ) - 2 - j

noncomputable def trace (m K : ℕ) : ℕ → Ledger (V := V) m K
  | 0 => initialLedger m K
  | j + 1 => accountBlock G (epoch m K j) (2 * m) (trace m K j)

theorem trace_consistent (m K j : ℕ) : ∀ v, Consistent ((trace G m K j).state v) := by
  induction j with
  | zero => exact fun _ => initial_consistent m K
  | succ j ih => exact block_consistent G (epoch m K j) (2 * m) (trace G m K j) ih

theorem trace_small (m K j : ℕ) : ∀ v, ((trace G m K j).state v).weight < denominator m K := by
  induction j with
  | zero =>
    intro _
    change 0 < denominator m K
    unfold denominator
    positivity
  | succ j ih => exact block_small G (epoch m K j) (2 * m) (trace G m K j) ih

theorem trace_pending {m K : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    PendingBound (epoch m K j) (trace G m K j) := by
  induction j with
  | zero => simp [PendingBound, trace, initialLedger, initial]
  | succ j ih =>
    have hb := block_pending_bound G hm (epoch m K j) (2 * m) (trace G m K j)
      (trace_consistent G m K j) ih
    change PendingBound (epoch m K j) (trace G m K (j + 1)) at hb
    have he : epoch m K j = epoch m K (j + 1) + 1 := by unfold epoch; push_cast; ring
    exact pending_lower_threshold hm (epoch m K (j + 1)) _ (by simpa only [he] using hb)

theorem trace_mass_bound {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) (j : ℕ) (v : V) :
    fullMass G (trace G m K j).state v ≤ (threshold m ((K : ℤ) - j) : ℝ) := by
  induction j with
  | zero =>
    simpa [fullMass, trace, initialLedger, initial, value, requirement, CappedCount.cap] using hdegree v
  | succ j ih =>
    have hi : epoch m K j + 2 = (K : ℤ) - j := by unfold epoch; ring
    have ho : epoch m K j + 1 = (K : ℤ) - (j + 1 : ℕ) := by unfold epoch; push_cast; ring
    have hb := epoch_bound G hm hk (epoch m K j) (trace G m K j).state
      (trace_consistent G m K j) v (by simpa only [hi] using ih)
    change fullMass G (accountBlock G (epoch m K j) (2 * m) (trace G m K j)).state v ≤ _
    rw [block_state]
    simpa only [ho] using hb

theorem trace_mass_nonneg (m K j : ℕ) (v : V) : 0 ≤ fullMass G (trace G m K j).state v := by
  have hn (u : V) : (0 : ℝ) ≤ (value ((trace G m K j).state u) : ℚ) := by
    exact_mod_cast value_nonneg ((trace G m K j).state u)
  exact Finset.sum_nonneg (fun u _ => hn u)

theorem tail_eq (m K : ℕ) (j n : ℕ) (hcount : j + n = K + target m K) :
    accountOuter G n (trace G m K j) = trace G m K (K + target m K) := by
  induction n generalizing j with
  | zero =>
    have hj : j = K + target m K := by omega
    subst j
    rfl
  | succ n ih =>
    change accountOuter G n (accountBlock G ((n : ℤ) - target m K - 1) (2 * m)
      (trace G m K j)) = _
    have he : (n : ℤ) - target m K - 1 = epoch m K j := by unfold epoch; omega
    rw [he]
    change accountOuter G n (trace G m K (j + 1)) = _
    exact ih (j + 1) (by omega)

theorem trace_actual (m K : ℕ) : trace G m K (K + target m K) = actualLedger G m K :=
  (tail_eq G m K 0 (K + target m K) (by omega)).symm

end Paper.Density.RationalEpochTrace

#print axioms Paper.Density.RationalEpochTrace.trace_pending
#print axioms Paper.Density.RationalEpochTrace.trace_mass_bound
#print axioms Paper.Density.RationalEpochTrace.trace_actual
