import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! The square-root potential pays for recursive half-balanced separators.
The resulting deletion cost is at most 4 C n / sqrt(k). -/
namespace Paper.SeparatorPotential
open scoped BigOperators

theorem child_root {n t : ℝ} (hn : 0 < n) (ht : 0 ≤ t) (hhalf : t ≤ n / 2) :
    4 * t / Real.sqrt n ≤ 3 * Real.sqrt t := by
  have hq := Real.sqrt_pos.mpr hn
  have hsq := Real.sq_sqrt hn.le
  have hst := Real.sq_sqrt ht
  have hsmall : (4 / 3 : ℝ) * Real.sqrt t ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  apply (div_le_iff₀ hq).mpr
  have hm := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg t)
  nlinarith

theorem coefficient {C k n : ℝ} (hC : 0 ≤ C) (hk : 0 < k) (hkn : k ≤ n) :
    0 ≤ 4 * C / Real.sqrt k - 4 * C / Real.sqrt n := by
  have hq := Real.sqrt_pos.mpr hk
  have hle := Real.sqrt_le_sqrt hkn
  have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 4 * C) hq hle
  linarith

theorem combine {ι : Type*} (F : Finset ι) (size : ι → ℝ) {C k n : ℝ}
    (hC : 0 ≤ C) (hk : 0 < k) (hkn : k ≤ n)
    (hnonneg : ∀ i ∈ F, 0 ≤ size i) (hhalf : ∀ i ∈ F, size i ≤ n / 2)
    (hsum : ∑ i ∈ F, size i ≤ n) :
    C * Real.sqrt n + ∑ i ∈ F, (4 * C / Real.sqrt k * size i - 3 * C * Real.sqrt (size i)) ≤
      4 * C / Real.sqrt k * n - 3 * C * Real.sqrt n := by
  have hn : 0 < n := hk.trans_le hkn
  have hq := Real.sqrt_pos.mpr hn
  have hsq := Real.mul_self_sqrt hn.le
  have hcoeff := coefficient hC hk hkn
  have hterm : ∀ i ∈ F,
      4 * C / Real.sqrt k * size i - 3 * C * Real.sqrt (size i) ≤
        (4 * C / Real.sqrt k - 4 * C / Real.sqrt n) * size i := by
    intro i hi
    have hb := mul_le_mul_of_nonneg_left (child_root hn (hnonneg i hi) (hhalf i hi)) hC
    ring_nf at hb ⊢
    linarith
  have htotal : (∑ i ∈ F, (4 * C / Real.sqrt k * size i - 3 * C * Real.sqrt (size i))) ≤
      (4 * C / Real.sqrt k - 4 * C / Real.sqrt n) * n := by
    calc
      _ ≤ ∑ i ∈ F, (4 * C / Real.sqrt k - 4 * C / Real.sqrt n) * size i := Finset.sum_le_sum hterm
      _ = (4 * C / Real.sqrt k - 4 * C / Real.sqrt n) * ∑ i ∈ F, size i := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hcoeff
  have heq : 4 * C / Real.sqrt n * n = 4 * C * Real.sqrt n := by
    calc
      _ = 4 * C / Real.sqrt n * (Real.sqrt n * Real.sqrt n) := by rw [hsq]
      _ = _ := by field_simp
  nlinarith
end Paper.SeparatorPotential
