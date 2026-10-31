import Paper.Solver.LocalSearch.SearchControl

namespace Paper.SearchControlBudget
open BroadcastModel SearchControl
variable {V : Type} [Fintype V] [LinearOrder V]

theorem maxBits {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (program C D a B q m).maxBits ≤
      max (3 * b + 3) (max (b + 2 * a * m * (B + 1) + 1) (D + 2)) := by
  let U := max (3 * b + 3) (max (b + 2 * a * m * (B + 1) + 1) (D + 2))
  have hc : (countStage C D B q).maxBits = (SearchCount.program C D B q).maxBits := by
    simp [countStage, prepareCount, finishCount, Program.maxBits, ProgramMemory.maxBits]
  have hcount : (countStage C D B q).maxBits ≤ U := by
    rw [hc]
    apply (SearchCount.maxBits C D B q).trans
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))
  have hheavy : (HeavyListing.program C D a m).maxBits ≤ U := by
    apply (HeavyListing.maxBits C D a m).trans
    exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))
  have hcost : (DemandValues.program C D B (2 * a * m)).maxBits ≤ U :=
    (DemandValues.maxBits C D B (2 * a * m)).trans (le_max_right _ _)
  change (program C D a B q m).maxBits ≤ U
  simp only [program, prepareHeavy, prepareCosts, finish, Program.maxBits,
    ProgramMemory.maxBits, Nat.max_zero, Nat.zero_max]
  exact max_le hcount (max_le hheavy hcost)

theorem task_rounds {b : ℕ} (C : BitCode V b) (k a B q m : ℕ) :
    (program C (4 * k) a B q m).rounds = (2 * a * m + 3) * (16 * k + 1) + 1 := by
  rw [SearchControl.rounds]
  have he : 4 * (4 * k) + 1 = 16 * k + 1 := by omega
  rw [he]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (k a B q m n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C (4 * k) a B q m).maxBits ≤
      (4 * c + 2 * a * m * (B + 1) + 4 * k + 6) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have h₁ : 3 * b + 3 ≤ (3 * c + 3) * Nat.clog 2 (n + 2) := by nlinarith
  have h₂ : b + 2 * a * m * (B + 1) + 1 ≤
      (c + 2 * a * m * (B + 1) + 1) * Nat.clog 2 (n + 2) := by
    have hc := Nat.mul_le_mul_left (2 * a * m * (B + 1) + 1) hl
    nlinarith
  have h₃ : 4 * k + 2 ≤ (4 * k + 2) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * k + 2) hl
  apply (maxBits C (4 * k) a B q m).trans
  apply max_le
  · exact h₁.trans (Nat.mul_le_mul_right _ (by omega))
  · apply max_le
    · exact h₂.trans (Nat.mul_le_mul_right _ (by omega))
    · exact h₃.trans (Nat.mul_le_mul_right _ (by omega))
end Paper.SearchControlBudget
