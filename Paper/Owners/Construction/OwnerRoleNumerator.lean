import Paper.Owners.Construction.OwnerRoleSolverBudget
import Paper.Preliminaries.RoleNumerator

/-! Actual bounded own numerator after role construction and sparse task
solving. The fixed denominator is public and independent of graph size. -/
namespace Paper.OwnerRoleNumerator
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def denominator (Δ k Q T s q : ℕ) : ℕ :=
  q * Q ^ OwnerRoleMetadata.slots ((Δ + 1) ^ k) T ((Δ + 1) ^ s)

def program {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    Program V ((Bool × Bool) × Fin (B + 1))
      (Fin (OwnerRoleInputs.capacity L Δ k Q T s * M + 1)) :=
  .seq (OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ)
    (.local fun _ _ st => RoleNumerator.output (OwnerRoleInputs.capacity L Δ k Q T s) M st.1)

theorem denominator_pos (Δ k Q T s q : ℕ) (hQ : 0 < Q) (hq : 0 < q) :
    0 < denominator Δ k Q T s q := Nat.mul_pos hq (pow_pos hQ _)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem keys {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (c : V → Fin (B + 1)) (v : V) :
    TaggedDictionary.keys (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) =
      TaskRoleId.space (RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D R L Δ r v))
        (OwnerRoleInputs.metadataCount Δ k Q T s) := by
  change TaggedDictionary.keys (((SparseParallel.execute
    (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s)) (OwnerRoleInputs.capacity L Δ k Q T s)
    (FractionalSearch.program C (4 * k) a B q M)).run G
    ((OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u))) v).1) = _
  rw [SparseParallelCorrect.execute_keys G]
  exact OwnerRoleInputs.keys G C D R L Δ r k t Q T s B hQ c v

theorem exact_sum {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hk : k ≤ r)
    (c : V → Fin (B + 1)) (v : V) :
    ((program C L Δ r k t Q T s a B q M hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).val =
      ∑ role ∈ TaskRoleId.space
        (RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D R L Δ r v))
        (OwnerRoleInputs.metadataCount Δ k Q T s),
        ((TaggedDictionary.lookup (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
          (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) role).getD 0).val := by
  change (RoleNumerator.output (OwnerRoleInputs.capacity L Δ k Q T s) M _).val = _
  rw [RoleNumerator.output_eq _ _ _ (by
    rw [keys G C D R L Δ r k t Q T s a B q M hQ c v, TaskRoleId.card_space]
    exact Nat.mul_le_mul_right _ (OwnerRootFrameCorrect.anchors_card G C D R hcover L Δ r k hk v))]
  rw [RoleNumerator.raw, keys G C D R L Δ r k t Q T s a B q M hQ c v]

theorem rounds {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s a B q M hQ).rounds =
      14 + 4 * r + RecursiveSearch.roundBound (4 * k) a M := by
  simp only [program, Program.rounds, OwnerRoleSolver.rounds, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) :
    (program C L Δ r k t Q T s a B q M hQ).maxBits =
      (OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).maxBits := by
  simp only [program, Program.maxBits, Nat.max_zero]

end Paper.OwnerRoleNumerator
