import Mathlib

/-! Fresh independent finite choices at every stage. Exact sums over the
explicit finite product give the geometric bound for an actual iteration. -/
namespace Paper.FiniteIteration
open scoped BigOperators
universe u v

def Seeds (Ω : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => Ω × Seeds Ω n

instance seedsFintype (Ω : Type u) [Fintype Ω] : (n : ℕ) → Fintype (Seeds Ω n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => @instFintypeProd Ω (Seeds Ω n) inferInstance (seedsFintype Ω n)

def run {State : Type v} {Ω : Type u} (step : State → Ω → State) (s : State) :
    (n : ℕ) → Seeds Ω n → State
  | 0, _ => s
  | n + 1, ω => run step (step s ω.1) n ω.2

theorem card_seeds (Ω : Type u) [Fintype Ω] (n : ℕ) : Fintype.card (Seeds Ω n) = Fintype.card Ω ^ n := by
  induction n with
  | zero => change Fintype.card PUnit = _; simp
  | succ n ih =>
    change Fintype.card (Ω × Seeds Ω n) = _
    rw [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

theorem geometric {State : Type v} {Ω : Type u} [Fintype Ω]
    (step : State → Ω → State) (size : State → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hstep : ∀ s, (∑ ω : Ω, size (step s ω)) ≤ ρ * Fintype.card Ω * size s)
    (n : ℕ) (s : State) :
    (∑ ω : Seeds Ω n, size (run step s n ω)) ≤ ρ ^ n * (Fintype.card Ω : ℝ) ^ n * size s := by
  induction n generalizing s with
  | zero => change (∑ _ : PUnit, size s) ≤ _; simp
  | succ n ih =>
    change (∑ ω : Ω × Seeds Ω n, size (run step (step s ω.1) n ω.2)) ≤ _
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ ω : Ω, ρ ^ n * (Fintype.card Ω : ℝ) ^ n * size (step s ω) :=
        Finset.sum_le_sum (fun ω _ => ih (step s ω))
      _ = (ρ ^ n * (Fintype.card Ω : ℝ) ^ n) * ∑ ω : Ω, size (step s ω) := by rw [Finset.mul_sum]
      _ ≤ (ρ ^ n * (Fintype.card Ω : ℝ) ^ n) * (ρ * Fintype.card Ω * size s) :=
        mul_le_mul_of_nonneg_left (hstep s) (by positivity)
      _ = _ := by rw [pow_succ, pow_succ]; ring
end Paper.FiniteIteration
