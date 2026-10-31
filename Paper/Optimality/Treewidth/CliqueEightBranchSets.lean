import Paper.Optimality.Treewidth.CliqueEightLabels
import Paper.Optimality.Treewidth.CliqueTwoContractions

namespace Paper.CliqueEightBranchSets
open CliqueFourMatchings CliqueEightLabels CliqueTwoContractions
variable {V : Type} [Fintype V] [DecidableEq V]
  (S : Finset V) (eS : Fin 4 ≃ (S : Set V))
  (eR : Fin 4 ≃ ((Sᶜ : Finset V) : Set V))

def pairIndex (side : Bool) : Fin 6 := if side then 1 else 0
def rowIndex (a : Fin 4) : Fin 6 := ⟨a.val + 2, by omega⟩

theorem row_block (k : Fin 3) (a : Fin 4) :
    blocks (labeling S eS eR k) (rowIndex a) = {(eS a).val} := by
  fin_cases a <;> fin_cases k <;> rfl

theorem pair_member (k : Fin 3) (side : Bool) (j : Fin 4)
    (hj : j ∈ part k side) :
    (eR j).val ∈ blocks (labeling S eS eR k) (pairIndex side) := by
  cases side with
  | false =>
    simp only [part, Bool.false_eq_true, if_false, Finset.mem_insert,
      Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · simp [pairIndex, blocks, zero]
    · simp [pairIndex, blocks, six]
  | true =>
    simp only [part, if_true, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · simp [pairIndex, blocks, CliqueEightLabels.one]
    · simp [pairIndex, blocks, seven]

end Paper.CliqueEightBranchSets
#print axioms Paper.CliqueEightBranchSets.row_block
#print axioms Paper.CliqueEightBranchSets.pair_member
