import Paper.Owners.Construction.OwnerRoleScoreLocality
import Paper.Owners.Construction.OwnerRoleCoverage
import Paper.Preliminaries.CanonicalRoleFrame

namespace Paper.OwnerRoleScoreZero
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inactive {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r)
    (c : V → Fin (B + 1)) (v : V) (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (h : (OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c v role).active = false) :
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v role = 0 := by
  exact SparseFractionalZero.inactive G C (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s))
    (OwnerRoleInputs.capacity L Δ k Q T s) (4 * k) a B q M _
    (fun u => OwnerRoleInputs.key_bound G C D R hcover L Δ r k t Q T s B hQ (by omega) c u)
    (OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c)
    (fun u => OwnerRoleInputsCorrect.consistent G C D R hcover L Δ r k t Q T s B hQ hks c u) v role h

theorem outside_low {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (hk : k ≤ r)
    (c : V → Fin (B + 1)) (v anchor : V)
    (ha : anchor ∉ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
    (i : Fin (OwnerRoleInputs.metadataCount Δ k Q T s)) :
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make anchor i) = 0 := by
  unfold OwnerRoleScoreLocality.score
  rw [SparseFractionalZero.lookup_none _ (TaskRoleId.make anchor i) (by
    rw [OwnerRoleNumerator.keys G C D R L Δ r k t Q T s a B q M hQ c v, TaskRoleId.mem_space]
    intro h
    exact ha (CanonicalRoleFrame.anchors_low G C D R hcover L Δ r k hk v anchor h))]
  rfl

end Paper.OwnerRoleScoreZero
