import Paper.Preliminaries.TerminalProtocol

/-! Explicit constant-round/logarithmic-message bounds for the complete
small-demand terminal protocol on the actual physical task. -/
namespace Paper.TerminalProtocolBudget
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

theorem task_rounds {b : ℕ} (C : BitCode V b) (k B q T m : ℕ) :
    (TerminalProtocol.program C (4 * k) B q T m).rounds =
      (T + 2 ^ T + 1) * (16 * k + 1) := by
  rw [TerminalProtocol.rounds]
  congr 1
  omega

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (k B q T m n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (TerminalProtocol.program C (4 * k) B q T m).maxBits ≤
      (3 * c + B + T * (q + 1) + 4 * k + 6) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have h₁ : b + T * (q + 1) + 1 ≤
      (c + T * (q + 1) + 1) * Nat.clog 2 (n + 2) := by
    have hc := Nat.mul_le_mul_left (T * (q + 1) + 1) hl
    nlinarith
  have h₂ : 2 * b + B + 3 ≤ (2 * c + B + 3) * Nat.clog 2 (n + 2) := by
    have hc := Nat.mul_le_mul_left (B + 3) hl
    nlinarith
  have h₃ : 4 * k + 2 ≤ (4 * k + 2) * Nat.clog 2 (n + 2) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4 * k + 2) hl
  apply (TerminalProtocol.maxBits C (4 * k) B q T m).trans
  apply max_le
  · exact h₁.trans (Nat.mul_le_mul_right _ (by omega))
  · apply max_le
    · exact h₂.trans (Nat.mul_le_mul_right _ (by omega))
    · exact h₃.trans (Nat.mul_le_mul_right _ (by omega))
end Paper.TerminalProtocolBudget
