import Paper.Owners.Construction.OwnerRoleTaskData

namespace Paper.RoleTaskChecks
open BroadcastModel
variable {V : Type} [LinearOrder V]

theorem valid_label {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (h : (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).valid = true) :
    (OwnerRoleTaskData.view C Δ k t Q T F hQ i xs a).2 =
      (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).owners :=
  (of_decide_eq_true h).2.2.2.2.2

theorem valid_size {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (h : (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).valid = true) :
    (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).owners.card ≤ k :=
  (of_decide_eq_true h).2.2.1

theorem valid_anchor {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (h : (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).valid = true) :
    a ∈ (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).owners :=
  (of_decide_eq_true h).2.2.2.1

theorem owners_subset {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ)) :
    (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).owners ⊆
      NeighborBalls.ball (FrameInterpreter.neighbors xs) a k := by
  simpa only [Finset.sort_toFinset] using
    FiniteSubsetCode.decode_subset ((NeighborBalls.ball (FrameInterpreter.neighbors xs) a k).sort (· ≤ ·))
      ((Δ + 1) ^ k) (OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T F i)

end Paper.RoleTaskChecks
