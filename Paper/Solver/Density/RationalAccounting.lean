import Paper.Solver.Density.RationalRuntime
import Paper.Solver.Density.UnitDomination

/-! Exact proof-side dual allocation for the literal primal broadcast.
These real accounting quantities are never communicated by the runtime. -/
namespace Paper.Density.RationalAccounting
open BroadcastModel RationalRuntime SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def source {m K : ℕ} (s : V → State m K) (v : V) : ℝ :=
  (requirement m (request (s v)) : ℚ)

def localGamma {m K : ℕ} (s : V → State m K) (v : V) : ℚ :=
  requirement m (request (s v)) + ∑ u : G.neighborFinset v, requirement m (request (s u))

def gamma {m K : ℕ} (s : V → State m K) (v : V) : ℝ :=
  UnitDomination.mass G (source s) v

def increment (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) : ℝ :=
  ((eval G (primalRound m K ep ed) s v).increment.value.val : ℝ)

noncomputable def allocation (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (r : V) : ℝ :=
  source s r * UnitDomination.mass G (fun v => increment G m K ep ed s v / gamma G s v) r

omit [Fintype V] [DecidableEq V] in
theorem source_nonneg {m K : ℕ} (s : V → State m K) (v : V) : 0 ≤ source s v := by
  unfold source requirement
  split_ifs <;> positivity

theorem gamma_eq {m K : ℕ} (s : V → State m K) (v : V) :
    gamma G s v = (localGamma G s v : ℝ) := by
  unfold gamma UnitDomination.mass
  rw [UnitDomination.closed_eq_insert, Finset.sum_insert (by simp)]
  rw [← Finset.sum_coe_sort]
  simp only [localGamma, source, Rat.cast_add, Rat.cast_sum]

theorem gamma_nonneg {m K : ℕ} (s : V → State m K) (v : V) : 0 ≤ gamma G s v :=
  Finset.sum_nonneg (fun u _ => source_nonneg s u)

theorem increment_nonneg (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    0 ≤ increment G m K ep ed s v := Nat.cast_nonneg _

theorem zero_increment {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (s : V → State m K) (v : V) (hz : gamma G s v = 0) :
    increment G m K ep ed s v = 0 := by
  have hmp : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp : (0 : ℚ) < threshold m ep := by
    unfold threshold
    exact zpow_pos (div_pos (by positivity) hmp) ep
  have hq : localGamma G s v = 0 := by
    have hcast : (localGamma G s v : ℝ) = 0 := (gamma_eq G s v).symm.trans hz
    exact_mod_cast hcast
  have hn : ¬ threshold m ep ≤ localGamma G s v := by rw [hq]; exact not_le_of_gt hp
  change ((CappedCount.cap (denominator m K)
    (if threshold m ep ≤ localGamma G s v then gridIncrement m K ed else 0)).value.val : ℝ) = 0
  simp only [if_neg hn, CappedCount.cap, Nat.zero_min, Nat.cast_zero]

theorem allocation_nonneg (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (r : V) :
    0 ≤ allocation G m K ep ed s r := by
  apply mul_nonneg (source_nonneg s r)
  exact Finset.sum_nonneg (fun v _ => div_nonneg
    (increment_nonneg G m K ep ed s v) (gamma_nonneg G s v))

/-- Every literal primal increment is distributed exactly once among the
dual accounting variables, without sending those variables. -/
theorem total_allocation {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (ed : ℕ)
    (s : V → State m K) :
    (∑ r, allocation G m K ep ed s r) = ∑ v, increment G m K ep ed s v := by
  unfold allocation
  rw [UnitDomination.transpose_sum]
  apply Finset.sum_congr rfl
  intro v _
  change increment G m K ep ed s v / gamma G s v * gamma G s v = _
  by_cases hz : gamma G s v = 0
  · rw [zero_increment G hm ep ed s v hz]
    simp
  · exact div_mul_cancel₀ _ hz

end Paper.Density.RationalAccounting

#print axioms Paper.Density.RationalAccounting.gamma_eq
#print axioms Paper.Density.RationalAccounting.zero_increment
#print axioms Paper.Density.RationalAccounting.allocation_nonneg
#print axioms Paper.Density.RationalAccounting.total_allocation
