import Paper.Solver.LocalSearch.GeneralCoveringSearch

namespace Paper.GeneralCoveringSearchBudget
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

theorem control_rounds {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (GeneralCoveringSearch.control C D a B q m).rounds =
      (2 * a * m + 3) * (4 * D + 1) + 1 := by
  simpa only [GeneralCoveringSearch.control, GeneralCoveringSearch.baseInput,
    Program.rounds, Nat.zero_add] using SearchControl.rounds C D a B q m

theorem projection_maxBits {B q : ℕ} {Out : Type}
    (P : Program V (TerminalProtocol.Input V B q) Out) :
    (Program.seq (GeneralCoveringSearch.baseInput B q) P).maxBits = P.maxBits := by
  simp only [GeneralCoveringSearch.baseInput, Program.maxBits, Nat.zero_max]

theorem control_maxBits {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (GeneralCoveringSearch.control C D a B q m).maxBits =
      (SearchControl.program C D a B q m).maxBits := by
  unfold GeneralCoveringSearch.control
  exact projection_maxBits _

theorem rounds {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (GeneralCoveringSearch.program C D a B q m).rounds = RecursiveSearch.roundBound D a m := by
  induction m with
  | zero => simpa only [GeneralCoveringSearch.program, GeneralCoveringSearch.zero, GeneralCoveringSearch.baseInput,
      Program.rounds, Nat.zero_add] using SearchZero.rounds C D B q
  | succ m ih =>
    rw [GeneralCoveringSearch.program, GeneralCoveringParent.rounds, GeneralCoveringTerminal.rounds C, control_rounds, ih]
    rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (GeneralCoveringSearch.program C D a B q m).maxBits ≤ 3 * b + RecursiveSearch.extraBits D a B q m := by
  induction m with
  | zero =>
    change (GeneralCoveringSearch.zero C D B q).maxBits ≤ _
    simp only [GeneralCoveringSearch.zero, GeneralCoveringSearch.baseInput, Program.maxBits, Nat.zero_max]
    apply (SearchZero.maxBits C D B q).trans
    change max (3 * b + 3) (D + 2) ≤ 3 * b + (D + 5)
    apply max_le <;> omega
  | succ m ih =>
    let T := RecursiveSearch.threshold a (m + 1)
    let K := RecursiveSearch.branches a (m + 1)
    have hl : T * (q + 1) + B + D + 6 ≤ RecursiveSearch.extraBits D a B q (m + 1) := le_max_left _ _
    have hc : K * (B + 1) + D + 6 ≤ RecursiveSearch.extraBits D a B q (m + 1) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hi : RecursiveSearch.extraBits D a B q m ≤ RecursiveSearch.extraBits D a B q (m + 1) :=
      (le_max_right _ _).trans (le_max_right _ _)
    apply (GeneralCoveringParent.maxBits
      (GeneralCoveringTerminal.program C D B q T (m + 1)) (GeneralCoveringSearch.control C D a B q (m + 1))
      (GeneralCoveringSearch.program C D a B q m) K).trans
    apply max_le
    · apply (GeneralCoveringTerminal.maxBits C D B q T (m + 1)).trans
      apply max_le
      · omega
      · apply max_le <;> omega
    · apply max_le
      · rw [control_maxBits]
        apply (SearchControlBudget.maxBits C D a B q (m + 1)).trans
        change max (3 * b + 3) (max (b + K * (B + 1) + 1) (D + 2)) ≤ _
        apply max_le
        · omega
        · apply max_le <;> omega
      · exact ih.trans (Nat.add_le_add_left hi (3 * b))

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (D a B q m n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (GeneralCoveringSearch.program C D a B q m).maxBits ≤
      (3 * c + RecursiveSearch.extraBits D a B q m) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hc := Nat.mul_le_mul_left (RecursiveSearch.extraBits D a B q m) hl
  apply (maxBits C D a B q m).trans
  nlinarith
end Paper.GeneralCoveringSearchBudget

#print axioms Paper.GeneralCoveringSearchBudget.rounds
#print axioms Paper.GeneralCoveringSearchBudget.logarithmic_bits
