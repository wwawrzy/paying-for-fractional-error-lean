import Paper.Owners.Construction.OwnerRoleViewCorrect
import Paper.Owners.Construction.OwnerRoleConfigProjection

/-! Task interpretation depends only on the canonical subset mask and
the actual finite priority records. Unused padded coordinates are irrelevant. -/
namespace Paper.RoleTaskConfigurationLocality
open BroadcastModel
variable {V : Type} [LinearOrder V]

theorem compute_eq {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i j : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (hm : OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T F i = OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T F j)
    (hs : OwnerRoleTaskData.seeds Δ k Q T F i xs = OwnerRoleTaskData.seeds Δ k Q T F j xs) :
    OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs =
      OwnerRoleTaskData.compute C Δ k t Q T F hQ a j xs := by
  have hv : OwnerRoleTaskData.view C Δ k t Q T F hQ i xs =
      OwnerRoleTaskData.view C Δ k t Q T F hQ j xs := by
    funext u
    unfold OwnerRoleTaskData.view
    rw [hs]
  unfold OwnerRoleTaskData.compute
  rw [hm, hv]

theorem project_eq {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (hF : (OwnerRoleTaskData.addresses xs).length ≤ F)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (hζ : ∀ j : Fin (OwnerRoleTaskData.addresses xs).length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T F i
        (LocalSeedRecords.slot (OwnerRoleTaskData.addresses xs) hF j) =
      ζ ((OwnerRoleTaskData.addresses xs).get j)) :
    OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs =
      OwnerRoleTaskData.compute C Δ k t Q T F hQ a
        (OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T F hQ
          (OwnerRoleTaskData.addresses xs) ζ (OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T F i)) xs := by
  apply compute_eq C Δ k t Q T F hQ a i _ xs
  · exact (OwnerRoleConfigProjection.mask_project _ Q T F hQ _ ζ _).symm
  · rw [OwnerRoleViewCorrect.seeds_eq Δ k Q T F i xs hF ζ hζ,
      OwnerRoleViewCorrect.seeds_eq Δ k Q T F _ xs hF ζ
        (OwnerRoleConfigProjection.table_project _ Q T F hQ _ hF ζ _)]

end Paper.RoleTaskConfigurationLocality
