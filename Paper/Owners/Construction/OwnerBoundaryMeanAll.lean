import Paper.Owners.Construction.OwnerBoundaryMean
import Paper.Preliminaries.ActualRoleOutcome
import Paper.Averaging.Tasks.FiniteMeanLinear

namespace Paper.OwnerBoundaryMeanAll
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem centers (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t Q T : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :
    PhysicalTasks.centers D (OwnerVirtualFacts.high G D R L Δ)
      (BoundaryOwners.vertices (OwnerTasks.graph G D R L (OwnerVirtualFacts.high G D R L Δ)) Finset.univ
        (ActualRoleOutcome.partition G D R L Δ k hk t Q T hQ ζ).parts) =
      BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
        (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
        (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts := by
  unfold ActualRoleOutcome.partition
  rw [OwnerPublicPartition.boundary G D R L (OwnerVirtualFacts.high G D R L Δ) k
    (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ)]
  exact OwnerPublicTasks.centers D _ _ (BoundaryOwners.subset _ _ _)

theorem correct {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T : ℕ) (hQ : 0 < Q) (v : V) :
    (((OwnerBoundaryMean.program C L Δ k t Q T hQ).run G
      (fun u => (decide (u ∈ D), decide (u ∈ R))) v).val : ℝ) / OwnerBoundaryMean.denominator Δ k Q T =
      FiniteAverage.vector (fun ζ : V → PriorityPartitionBroadcast.Table Δ k Q T =>
        indicator (BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
          (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts)) v := by
  by_cases hv : v ∈ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ)
  · rw [OwnerBoundaryMean.root_correct G C D R hcover L Δ k hk t ht Q T hQ v hv]
    unfold FiniteAverage.vector
    congr 1
    apply Finset.sum_congr rfl
    intro ζ _
    exact FiniteMeanLinear.indicator _ v
  · rw [OwnerBoundaryMean.outside G C D R hcover L Δ k t Q T hQ v hv, Nat.cast_zero, zero_div]
    unfold FiniteAverage.vector
    have hz : (∑ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
        indicator (BoundaryOwners.vertices (PublicOwners.graph G D R L (OwnerVirtualFacts.high G D R L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
          (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts) v) = 0 := by
      apply Finset.sum_eq_zero
      intro ζ _
      exact if_neg (fun h => hv (BoundaryOwners.subset _ _ _ h))
    rw [hz, zero_div]

end Paper.OwnerBoundaryMeanAll
