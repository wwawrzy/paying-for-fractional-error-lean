import Paper.Solver.Density.RationalCounters
import Paper.Solver.Density.RationalSaturation

/-! Requirement decay of a literal cleanup and a literal complete phase.
The active requirement after the inner scan controls the part which has
not yet received a full unit of coverage. -/
namespace Paper.Density.RationalRequirementDecay
open BroadcastModel RationalRuntime RationalAccounting RationalCounters RationalSaturation SevenFoundation
open scoped BigOperators

def base (m : ℕ) : ℚ := (m : ℚ) / (m + 1)
def value {m K : ℕ} (s : State m K) : ℚ := requirement m (s.exponent, !s.stopped)

theorem base_bounds (m : ℕ) : 0 ≤ base m ∧ base m ≤ 1 := by
  unfold base
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0 : ℚ) < m + 1)).mpr
    norm_num

theorem value_nonneg {m K : ℕ} (s : State m K) : 0 ≤ value s := by
  unfold value requirement
  split_ifs <;> positivity

theorem clean_drop {m K : ℕ} (s : State m K) (hs : Consistent s)
    (hw : denominator m K ≤ s.weight) : value (clean s) ≤ base m * value s := by
  by_cases hf : target m K * denominator m K ≤ s.fulfilled
  · simp only [clean, if_pos hw, if_pos hf, value, requirement]
    exact mul_nonneg (base_bounds m).1 (value_nonneg s)
  · by_cases hstop : s.stopped = true
    · simp [clean, hw, hf, value, requirement, hstop]
    · have hfalse : s.stopped = false := by
        cases h : s.stopped with
        | false => rfl
        | true => exact False.elim (hstop h)
      have hcap := exponent_uncapped s (hs.2 hfalse) (Nat.lt_of_not_ge hf)
      have hD : 0 < denominator m K := by unfold denominator; positivity
      have hq : s.weight / denominator m K ≠ 0 := by
        intro hz
        have hmod := Nat.mod_lt s.weight hD
        have he := Nat.mod_add_div s.weight (denominator m K)
        rw [hz, Nat.mul_zero, Nat.add_zero] at he
        omega
      change value (clean s) ≤ base m * value s
      simp only [clean, if_pos hw, if_neg hf, value, requirement, hfalse,
        Bool.not_false, if_pos rfl, CappedCount.cap, min_eq_left hcap]
      change base m ^ (s.exponent.value.val + s.weight / denominator m K) ≤
        base m * base m ^ s.exponent.value.val
      rw [pow_add]
      calc
        _ ≤ base m ^ s.exponent.value.val * base m :=
          mul_le_mul_of_nonneg_left (pow_le_of_le_one (base_bounds m).1 (base_bounds m).2 hq)
            (pow_nonneg (base_bounds m).1 _)
        _ = _ := mul_comm _ _

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Accurate {m K : ℕ} (s : V → State m K) : Prop :=
  ∀ v, (s v).active = (!(s v).stopped && decide ((s v).weight < denominator m K))

theorem weight_after_ge (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K) (v : V) :
    (s v).weight ≤ (after G m K ep ed s v).weight := Nat.le_add_right _ _

theorem inner_accurate (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K)
    (hs : Accurate s) : Accurate (after G m K ep ed s) := by
  intro v
  rw [after_active, hs v, after_stopped]
  by_cases hw : (after G m K ep ed s v).weight < denominator m K
  · have hold := (weight_after_ge G m K ep ed s v).trans_lt hw
    simp only [hw, hold, decide_true, Bool.and_true]
  · simp only [hw, decide_false, Bool.and_false]

theorem inner_start_accurate (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K)
    (hs : ∀ v, (s v).active = !(s v).stopped) : Accurate (after G m K ep ed s) := by
  intro v
  rw [after_active, hs v, after_stopped]

theorem scan_accurate (m K : ℕ) (ep : ℤ) (j : ℕ) (s : V → State m K)
    (hs : Accurate s) : Accurate ((scan m K ep j).run G s) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih => exact ih _ (inner_accurate G m K ep j s hs)

theorem scan_start_accurate (m K : ℕ) (ep : ℤ) (j : ℕ) (s : V → State m K)
    (hs : ∀ v, (s v).active = !(s v).stopped) : Accurate ((scan m K ep (j + 1)).run G s) :=
  scan_accurate G m K ep j _ (inner_start_accurate G m K ep j s hs)

theorem scan_value (m K : ℕ) (ep : ℤ) (j : ℕ) (s : V → State m K) (v : V) :
    value ((scan m K ep j).run G s v) = value (s v) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih => exact (ih ((inner m K ep j).run G s)).trans rfl

theorem clean_convex {m K : ℕ} (s : State m K) (hs : Consistent s)
    (ha : s.active = (!s.stopped && decide (s.weight < denominator m K))) :
    value (clean s) ≤ base m * value s + (1 - base m) * requirement m (request s) := by
  by_cases hw : denominator m K ≤ s.weight
  · have hactive : s.active = false := by
      rw [ha]
      simp only [not_lt_of_ge hw, decide_false, Bool.and_false]
    have hz : requirement m (request s) = 0 := by simp [request, hactive, requirement]
    rw [hz, mul_zero, add_zero]
    exact clean_drop s hs hw
  · have hclean : clean s = s := by simp only [clean, if_neg hw]
    have he : requirement m (request s) = value s := by
      simp only [request, ha, Nat.lt_of_not_ge hw, decide_true, Bool.and_true, Bool.and_self, value]
    rw [hclean, he]
    exact le_of_eq (by ring)

def fullMass {m K : ℕ} (s : V → State m K) (v : V) : ℝ :=
  ∑ r ∈ closed G v, (value (s r) : ℝ)

/-- One actual phase contracts the full requirement mass toward its threshold. -/
theorem phase_contraction {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K) (ep : ℤ)
    (s : V → State m K) (hs : ∀ v, Consistent (s v)) (v : V) :
    fullMass G ((phase m K ep).run G s) v ≤
      (base m : ℝ) * fullMass G s v + (1 - (base m : ℝ)) * (threshold m ep : ℝ) := by
  let a : V → State m K := fun u => {(s u) with active := !(s u).stopped}
  let z := (scan m K ep K).run G a
  have ha : ∀ u, (a u).active = !(a u).stopped := fun _ => rfl
  have hac : ∀ u, Consistent (a u) := hs
  have hzc : ∀ u, Consistent (z u) := scan_consistent G m K ep K a hac
  obtain ⟨j, hK⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  have hcount : j + 1 = K := by omega
  have hza : Accurate z := by
    dsimp only [z]
    simpa only [hcount] using scan_start_accurate G m K ep j a ha
  have hgamma : gamma G z v ≤ (threshold m ep : ℝ) := by
    dsimp only [z]
    simpa only [hcount] using le_of_lt (scan_gamma_lt G hm ep j a v)
  have hfull : fullMass G z v = fullMass G s v := by
    apply Finset.sum_congr rfl
    intro u _
    exact congrArg (fun q : ℚ => (q : ℝ)) (scan_value G m K ep K a u)
  have hp : (0 : ℝ) ≤ 1 - (base m : ℝ) := by exact_mod_cast sub_nonneg.mpr (base_bounds m).2
  have hsum : fullMass G ((phase m K ep).run G s) v ≤
      (base m : ℝ) * fullMass G z v + (1 - (base m : ℝ)) * gamma G z v := by
    change (∑ r ∈ closed G v, (value (clean (z r)) : ℝ)) ≤ _
    have hh (r : V) : (value (clean (z r)) : ℝ) ≤
        (base m : ℝ) * (value (z r) : ℝ) +
          (1 - (base m : ℝ)) * source z r := by
      change (value (clean (z r)) : ℝ) ≤ (base m : ℝ) * (value (z r) : ℝ) +
        (1 - (base m : ℝ)) * (requirement m (request (z r)) : ℝ)
      exact_mod_cast clean_convex (z r) (hzc r) (hza r)
    calc
      _ ≤ ∑ r ∈ closed G v, ((base m : ℝ) * (value (z r) : ℝ) +
          (1 - (base m : ℝ)) * source z r) := Finset.sum_le_sum (fun r _ => hh r)
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, fullMass, gamma, UnitDomination.mass]
  rw [hfull] at hsum
  exact hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hgamma hp))

end Paper.Density.RationalRequirementDecay

#print axioms Paper.Density.RationalRequirementDecay.clean_drop
#print axioms Paper.Density.RationalRequirementDecay.scan_start_accurate
#print axioms Paper.Density.RationalRequirementDecay.phase_contraction
