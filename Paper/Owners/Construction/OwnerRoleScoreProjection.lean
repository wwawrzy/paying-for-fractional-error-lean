import Paper.Owners.Construction.OwnerRoleScoreLocality
import Paper.Communication.RoleTableEncoding
import Paper.Preliminaries.CanonicalRoleFrame

namespace Paper.OwnerRoleScoreProjection
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem project_eq {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v anchor : V)
    (i : Fin (OwnerRoleInputs.metadataCount Δ k Q T s))
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (hζ : ∀ j : Fin (OwnerRoleTaskData.addresses (OwnerRoleInputsCorrect.canonical G D R L Δ s anchor)).length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i
        (LocalSeedRecords.slot _ (CanonicalRoleFrame.addresses_length G D R L Δ s anchor) j) =
      ζ ((OwnerRoleTaskData.addresses (OwnerRoleInputsCorrect.canonical G D R L Δ s anchor)).get j)) :
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) =
      OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
        (TaskRoleId.make anchor (OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ
          (OwnerRoleTaskData.addresses (OwnerRoleInputsCorrect.canonical G D R L Δ s anchor)) ζ
          (OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i))) := by
  refine OwnerRoleScoreLocality.same_task G C D R hcover L Δ r k t Q T s a B q M hQ hks c v _ _ ?_ ?_
  · rfl
  · exact RoleTaskConfigurationLocality.project_eq C Δ k t Q T ((Δ + 1) ^ s) hQ anchor i _
      (CanonicalRoleFrame.addresses_length G D R L Δ s anchor) ζ hζ

end Paper.OwnerRoleScoreProjection
