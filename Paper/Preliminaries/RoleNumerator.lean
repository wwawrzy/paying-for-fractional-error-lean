import Paper.Preliminaries.TaggedDictionary
import Paper.Preliminaries.SparseParallelCorrect

/-! A finite natural own numerator, with no rounding of real numbers.
Sum once per public role key, so repeated received entries cannot add cost. -/
namespace Paper.RoleNumerator
open scoped BigOperators
variable {Role : Type} [LinearOrder Role]

def raw (M : ℕ) (xs : List (Role × Fin (M + 1))) : ℕ :=
  ∑ r ∈ TaggedDictionary.keys xs, ((TaggedDictionary.lookup xs r).getD 0).val

def output (K M : ℕ) (xs : List (Role × Fin (M + 1))) : Fin (K * M + 1) :=
  ⟨min (raw M xs) (K * M), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem raw_le (K M : ℕ) (xs : List (Role × Fin (M + 1)))
    (hK : (TaggedDictionary.keys xs).card ≤ K) : raw M xs ≤ K * M := by
  calc
    _ ≤ ∑ _r ∈ TaggedDictionary.keys xs, M :=
      Finset.sum_le_sum (fun r _ => Nat.le_of_lt_succ ((TaggedDictionary.lookup xs r).getD 0).isLt)
    _ = (TaggedDictionary.keys xs).card * M := by simp only [Finset.sum_const_nat]
    _ ≤ K * M := Nat.mul_le_mul_right M hK

theorem output_eq (K M : ℕ) (xs : List (Role × Fin (M + 1)))
    (hK : (TaggedDictionary.keys xs).card ≤ K) : (output K M xs).val = raw M xs :=
  Nat.min_eq_left (raw_le K M xs hK)

end Paper.RoleNumerator
