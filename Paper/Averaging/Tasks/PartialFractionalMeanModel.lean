import Paper.Averaging.Tasks.ActualRoleMeanOutcome
import Paper.Owners.Construction.OwnerBoundaryMeanAll

namespace Paper.PartialFractionalMeanModel
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem decompose {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k : ℕ) (hk : 0 < k) (t Q T s a B : ℕ) (hQ : 0 < Q)
    (ξ : ℝ) (c : V → Fin (B + 1)) (v : V) :
    ActualRoleMeanOutcome.vector G C D R L Δ r k hk t Q T s a B hQ ξ c v =
      indicator (HeavyRepair.heavy G D R L) v +
      indicator (TaskDecomposition.highCenters D (OwnerVirtualFacts.high G D R L Δ)) v +
      FiniteAverage.vector (fun ζ : V → PriorityPartitionBroadcast.Table Δ k Q T =>
        indicator (BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
          (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts)) v +
      FiniteAverage.vector (fun ζ : V → PriorityPartitionBroadcast.Table Δ k Q T =>
        OutcomeVector.tasks G D R L (OwnerVirtualFacts.high G D R L Δ)
          (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts
          (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ)) v := by
  letI : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hy : (fun ζ : V → PriorityPartitionBroadcast.Table Δ k Q T =>
      OutcomeVector.vector G D R L (OwnerVirtualFacts.high G D R L Δ)
        (BoundaryOwners.vertices (OwnerTasks.graph G D R L (OwnerVirtualFacts.high G D R L Δ)) Finset.univ
          (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts)
        (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts
        (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ)) =
      (fun ζ u => indicator (HeavyRepair.heavy G D R L) u +
        indicator (TaskDecomposition.highCenters D (OwnerVirtualFacts.high G D R L Δ)) u +
        indicator (BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
          (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts) u +
        OutcomeVector.tasks G D R L (OwnerVirtualFacts.high G D R L Δ)
          (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts
          (ActualRoleOutcome.family G C D R L Δ r k hk t Q T s a B hQ ξ c ζ) u) := by
    funext ζ u
    unfold OutcomeVector.vector
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst, OwnerBoundaryMeanAll.centers G D R L Δ k hk t Q T hQ ζ]
  dsimp only [ActualRoleMeanOutcome.vector, NaturalOutcomeMean.vector]
  rw [hy, FiniteMeanLinear.add, FiniteMeanLinear.add, FiniteMeanLinear.add,
    FiniteMeanLinear.constant, FiniteMeanLinear.constant]

end Paper.PartialFractionalMeanModel
