import Paper.Owners.Construction.OwnerRoleTaskData

namespace Paper.RoleTaskCanonical
open BroadcastModel
variable {V : Type} [LinearOrder V]

theorem mask {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (h : (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).valid = true) :
    OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T F i =
      FiniteSubsetCode.encode ((NeighborBalls.ball (FrameInterpreter.neighbors xs) a k).sort (· ≤ ·))
        ((Δ + 1) ^ k) (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).owners :=
  (of_decide_eq_true h).2.1

theorem leader {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (h : (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).valid = true) :
    FinitePriorityIndex.leader (OwnerRoleTaskData.compute C Δ k t Q T F hQ a i xs).owners a = a :=
  (of_decide_eq_true h).2.2.2.2.1

end Paper.RoleTaskCanonical
