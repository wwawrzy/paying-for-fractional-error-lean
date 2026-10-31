import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The abstract error-cancellation principle, independent of graph structure.
Corresponds to Proposition `sc:principle` and the first assertion of Theorem B.
-/
namespace Paper.Slack
open scoped BigOperators

/-- Output-proportional slack pays for the same relative solver error. -/
theorem pays_for_error {cost output optimum δ : ℝ} (hδ : 0 < δ)
    (hslack : (1 + δ) * output ≤ cost)
    (hsolver : cost ≤ (1 + δ) * optimum) : output ≤ optimum := by
  have hpos : 0 < 1 + δ := by linarith
  exact (mul_le_mul_iff_right₀ hpos).mp (hslack.trans hsolver)

/-- A saving bound written in the form used in the rounding analysis. -/
theorem saving_pays_for_error {cost output optimum δ : ℝ} (hδ : 0 < δ)
    (hsaving : δ * output ≤ cost - output)
    (hsolver : cost ≤ (1 + δ) * optimum) : output ≤ optimum := by
  apply pays_for_error hδ (hsolver := hsolver)
  nlinarith

/-- The quantitative paying lemma: the same two nonnegative quantities bound
both the output size and the saving. In the paper `s = 1 / (a + 1)` and
`u = w + ℓ`, `v = P`. -/
theorem bounded_components_pay {cost output optimum s M M' u v : ℝ}
    (hs : 0 < s) (hM : 0 < M) (hM' : 0 < M')
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hcount : output ≤ M * u + M' * v)
    (hsaving : s * u + v ≤ cost - output)
    (hsolver : cost ≤ (1 + min (s / M) (1 / M')) * optimum) :
    output ≤ optimum := by
  let δ := min (s / M) (1 / M')
  have hδ : 0 < δ := lt_min (div_pos hs hM) (div_pos (by norm_num) hM')
  have hfirst : δ * M ≤ s := (le_div_iff₀ hM).mp (min_le_left _ _)
  have hsecond : δ * M' ≤ 1 := (le_div_iff₀ hM').mp (min_le_right _ _)
  have hsave : δ * output ≤ cost - output := by
    calc
      δ * output ≤ δ * (M * u + M' * v) :=
        mul_le_mul_of_nonneg_left hcount hδ.le
      _ = (δ * M) * u + (δ * M') * v := by simp only [mul_add, mul_assoc]
      _ ≤ s * u + 1 * v := add_le_add
        (mul_le_mul_of_nonneg_right hfirst hu)
        (mul_le_mul_of_nonneg_right hsecond hv)
      _ ≤ cost - output := by simpa using hsaving
  exact saving_pays_for_error hδ hsave hsolver

/-- The finite-family certificate in Proposition `sc:principle`. A nonempty
family makes the minimum ratio well defined and strictly positive. -/
theorem finite_certificate {ι : Type*} (I : Finset ι) (hI : I.Nonempty)
    (α β S : ι → ℝ) (hα : ∀ i ∈ I, 0 < α i) (hβ : ∀ i ∈ I, 0 < β i)
    (hS : ∀ i ∈ I, 0 ≤ S i) {cost output : ℝ}
    (hcount : output ≤ ∑ i ∈ I, β i * S i)
    (hsaving : (∑ i ∈ I, α i * S i) ≤ cost - output) :
    let δ := I.inf' hI (fun i => α i / β i)
    0 < δ ∧ (1 + δ) * output ≤ cost := by
  dsimp only
  let δ := I.inf' hI (fun i => α i / β i)
  have hδ : 0 < δ := (Finset.lt_inf'_iff hI).mpr (fun i hi => div_pos (hα i hi) (hβ i hi))
  have hcoeff : ∀ i ∈ I, δ * β i ≤ α i := by
    intro i hi
    exact (le_div_iff₀ (hβ i hi)).mp (Finset.inf'_le _ hi)
  have hs : δ * output ≤ cost - output := by
    calc
      δ * output ≤ δ * (∑ i ∈ I, β i * S i) := mul_le_mul_of_nonneg_left hcount hδ.le
      _ = ∑ i ∈ I, (δ * β i) * S i := by simp only [Finset.mul_sum, mul_assoc]
      _ ≤ ∑ i ∈ I, α i * S i := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_right (hcoeff i hi) (hS i hi))
      _ ≤ cost - output := hsaving
  exact ⟨hδ, by nlinarith⟩

end Paper.Slack
