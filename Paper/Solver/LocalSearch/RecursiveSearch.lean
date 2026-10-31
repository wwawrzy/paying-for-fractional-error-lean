import Paper.Preliminaries.BranchParent

/-! Actual fully unrolled bounded-budget search program. Its constructors
depend only on fixed numeric parameters and public ID code, never on G.
Correctness of recursive calls is proved separately from this construction. -/
namespace Paper.RecursiveSearch
open BroadcastModel
variable {V : Type} [LinearOrder V]

def threshold (a m : ℕ) := 2 * (a + 1) * m

def branches (a m : ℕ) := 2 * a * m

def program {b : ℕ} (C : BitCode V b) (D a B q : ℕ) :
    ℕ → Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B))
  | 0 => SearchCount.zero C D B q
  | m + 1 => BranchParent.program
      (TerminalWord.program C D B q (threshold a (m + 1)) (m + 1))
      (SearchControl.program C D a B q (m + 1)) (program C D a B q m) (branches a (m + 1))

def roundBound (D a : ℕ) : ℕ → ℕ
  | 0 => 4 * D + 1
  | m + 1 =>
      (threshold a (m + 1) + 2 ^ threshold a (m + 1) + 1) * (4 * D + 1) +
      ((branches a (m + 1) + 3) * (4 * D + 1) + 1) +
      branches a (m + 1) * roundBound D a m

def extraBits (D a B q : ℕ) : ℕ → ℕ
  | 0 => D + 5
  | m + 1 => max (threshold a (m + 1) * (q + 1) + B + D + 6)
      (max (branches a (m + 1) * (B + 1) + D + 6) (extraBits D a B q m))

variable [Fintype V]

theorem rounds {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (program C D a B q m).rounds = roundBound D a m := by
  induction m with
  | zero => exact SearchZero.rounds C D B q
  | succ m ih =>
    rw [program, BranchParent.rounds, TerminalWord.rounds C, SearchControl.rounds, ih]
    rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (D a B q m : ℕ) :
    (program C D a B q m).maxBits ≤ 3 * b + extraBits D a B q m := by
  induction m with
  | zero =>
    apply (SearchZero.maxBits C D B q).trans
    change max (3 * b + 3) (D + 2) ≤ 3 * b + (D + 5)
    apply max_le <;> omega
  | succ m ih =>
    let T := threshold a (m + 1)
    let K := branches a (m + 1)
    have hl : T * (q + 1) + B + D + 6 ≤ extraBits D a B q (m + 1) := le_max_left _ _
    have hc : K * (B + 1) + D + 6 ≤ extraBits D a B q (m + 1) :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hi : extraBits D a B q m ≤ extraBits D a B q (m + 1) :=
      (le_max_right _ _).trans (le_max_right _ _)
    apply (BranchParent.maxBits
      (TerminalWord.program C D B q T (m + 1)) (SearchControl.program C D a B q (m + 1))
      (program C D a B q m) K).trans
    apply max_le
    · apply (TerminalWord.maxBits C D B q T (m + 1)).trans
      apply max_le
      · omega
      · apply max_le <;> omega
    · apply max_le
      · apply (SearchControlBudget.maxBits C D a B q (m + 1)).trans
        change max (3 * b + 3) (max (b + K * (B + 1) + 1) (D + 2)) ≤ _
        apply max_le
        · omega
        · apply max_le <;> omega
      · exact ih.trans (Nat.add_le_add_left hi (3 * b))

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (k a B q m n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C (4 * k) a B q m).maxBits ≤
      (3 * c + extraBits (4 * k) a B q m) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hc := Nat.mul_le_mul_left (extraBits (4 * k) a B q m) hl
  apply (maxBits C (4 * k) a B q m).trans
  nlinarith
end Paper.RecursiveSearch
