import Paper.Averaging.Tasks.FiniteAverage

namespace Paper.FiniteMeanLinear
open scoped BigOperators
variable {Ω V : Type} [Fintype Ω] [Nonempty Ω] [Fintype V] [DecidableEq V]

theorem add (x y : Ω → V → ℝ) (v : V) :
    FiniteAverage.vector (fun ω u => x ω u + y ω u) v =
      FiniteAverage.vector x v + FiniteAverage.vector y v := by
  unfold FiniteAverage.vector
  rw [Finset.sum_add_distrib, add_div]

theorem constant (f : V → ℝ) (v : V) : FiniteAverage.vector (fun _ω : Ω => f) v = f v := by
  unfold FiniteAverage.vector
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (ne_of_gt (FiniteAverage.card_pos (Ω := Ω)))

theorem indicator (S : Finset V) (v : V) :
    ((decide (v ∈ S)).toNat : ℝ) = SevenFoundation.indicator S v := by
  by_cases hv : v ∈ S <;> simp [SevenFoundation.indicator, hv]

end Paper.FiniteMeanLinear
