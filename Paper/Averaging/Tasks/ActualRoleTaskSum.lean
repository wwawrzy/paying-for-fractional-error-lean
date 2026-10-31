import Paper.Averaging.Tasks.ActualRoleTaskExtension

namespace Paper.ActualRoleTaskSum
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B : ℕ) (ξ : ℝ) (c : V → Fin (B + 1))
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (v : V) :
    OutcomeVector.tasks G D R L (OwnerVirtualFacts.high G D R L Δ)
      (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts
      (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ) v =
        ∑ U : ↥((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts : Set (Finset V)),
          ActualRoleOutcome.partVector G C D R L Δ r k t Q T s a B hQ ξ c ζ U.val
            (U.val.min' ((OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).nonempty U.val U.property)) v := by
  let Qlow := OwnerVirtualFacts.high G D R L Δ
  let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
  let x := fun I => InducedExtension.extend (PhysicalTasks.vertices G D R L Qlow I)
    (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ I) v
  have hinj : ∀ U ∈ P.parts, ∀ W ∈ P.parts,
      OwnerPublicTasks.pull D Qlow U = OwnerPublicTasks.pull D Qlow W → U = W := by
    intro U hU W hW he
    exact (OwnerPublicTasks.centers D Qlow U (P.subset U hU)).symm.trans
      ((congrArg (PhysicalTasks.centers D Qlow) he).trans (OwnerPublicTasks.centers D Qlow W (P.subset W hW)))
  dsimp only [OutcomeVector.tasks, CoverVectorSum.vector]
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  have hp : (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts =
      P.parts.image (OwnerPublicTasks.pull D Qlow) := by
    rfl
  rw [hp]
  change (∑ I ∈ P.parts.image (OwnerPublicTasks.pull D Qlow), x I) = _
  calc
    _ = ∑ U ∈ P.parts, x (OwnerPublicTasks.pull D Qlow U) := Finset.sum_image hinj
    _ = ∑ U : ↥(P.parts : Set (Finset V)), x (OwnerPublicTasks.pull D Qlow U.val) :=
      (Finset.sum_coe_sort P.parts (fun U => x (OwnerPublicTasks.pull D Qlow U))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro U _
      exact ActualRoleTaskExtension.part G C D R hcover L Δ r k hk t ht Q T s hQ hks hs a B ξ c ζ U.val U.property v

end Paper.ActualRoleTaskSum
