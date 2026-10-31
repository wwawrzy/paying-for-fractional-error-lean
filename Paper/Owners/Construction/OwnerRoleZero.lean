import Paper.Owners.Construction.OwnerRoleSolver
import Paper.Solver.LocalSearch.SparseFractionalZero

namespace Paper.OwnerRoleZero
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem invalid {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v : V)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (hvalid : (OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ role).valid = false) :
    ((TaggedDictionary.lookup (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) role).getD 0).val = 0 := by
  apply SparseFractionalZero.inactive G C (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s))
    (OwnerRoleInputs.capacity L Δ k Q T s) (4 * k) a B q M _
    (fun u => OwnerRoleInputs.key_bound G C D R hcover L Δ r k t Q T s B hQ (by omega) c u)
    (OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c)
    (fun u => OwnerRoleInputsCorrect.consistent G C D R hcover L Δ r k t Q T s B hQ hks c u) v role
  exact OwnerRoleTaskData.invalid_inactive _ _ _ hvalid

end Paper.OwnerRoleZero
