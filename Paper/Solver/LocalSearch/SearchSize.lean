import Paper.Solver.LocalSearch.ExactSearch

/-! Bounds independent of graph order for the finite exact-search output. -/
namespace Paper.SearchSize
attribute [local instance] Classical.propDecidable
open SevenFoundation FiniteSearch
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def terminalBound (t : ℝ) (m : ℕ) : ℕ :=
  (m + 1) ^ (2 ^ ⌈2 * (t + 1) * m⌉₊)

noncomputable def bound (t : ℝ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => ⌈2 * t * (m + 1 : ℕ)⌉₊ * bound t m + terminalBound t (m + 1)

theorem terminal_card_le (b : V → ℕ) (m : ℕ) (c : V → ℝ) :
    (terminal G b m c).card ≤ (m + 1) ^ (2 ^ (active b).card) := by
  have h := (Finset.card_filter_le
    (assignments (MaskCompression.representatives G (active b) c) m) (valid G m b)).trans
    (assignments_card_le (MaskCompression.representatives G (active b) c) m)
  exact h.trans (Nat.pow_le_pow_right (by omega) (MaskCompression.representatives_card_le G _ c))

theorem terminal_card_le_bound (b : V → ℕ) (m : ℕ) (c : V → ℝ) (t : ℝ)
    (hsmall : ((active b).card : ℝ) ≤ 2 * (t + 1) * m) :
    (terminal G b m c).card ≤ terminalBound t m := by
  have hc : (active b).card ≤ ⌈2 * (t + 1) * m⌉₊ := by
    exact_mod_cast hsmall.trans (Nat.le_ceil _)
  exact (terminal_card_le G b m c).trans (Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by decide) hc))

theorem search_card_le {t : ℝ} (ht : 1 ≤ t) (hden : Incidence.InducedDensityBound G t)
    (c : V → ℝ) (m : ℕ) (b : V → ℕ) :
    (ExactSearch.search G t c m b).card ≤ bound t m := by
  induction m generalizing b with
  | zero =>
    have h := terminal_card_le G b 0 c
    simpa only [ExactSearch.search, bound, zero_add, one_pow] using h
  | succ m ih =>
    rw [ExactSearch.search, bound]
    split_ifs with hlarge
    · have hC : (LocalSearchBounds.heavy G (active b) (m + 1)).card ≤
          ⌈2 * t * (m + 1 : ℕ)⌉₊ := by
        exact_mod_cast (LocalSearchBounds.heavy_card_le G (active b) (m + 1)
          (by omega) ht hden hlarge).trans (Nat.le_ceil _)
      calc
        _ ≤ ∑ v ∈ LocalSearchBounds.heavy G (active b) (m + 1),
            ((ExactSearch.search G t c m (ExactSearch.reduce G b v)).image (ExactSearch.addOne v)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ LocalSearchBounds.heavy G (active b) (m + 1), bound t m :=
          Finset.sum_le_sum (fun v _ => Finset.card_image_le.trans (ih (ExactSearch.reduce G b v)))
        _ = (LocalSearchBounds.heavy G (active b) (m + 1)).card * bound t m := by simp [mul_comm]
        _ ≤ ⌈2 * t * (m + 1 : ℕ)⌉₊ * bound t m := Nat.mul_le_mul_right _ hC
        _ ≤ _ := Nat.le_add_right _ _
    · exact (terminal_card_le_bound G b (m + 1) c t (le_of_lt (lt_of_not_ge hlarge))).trans
        (Nat.le_add_left _ _)
end Paper.SearchSize
