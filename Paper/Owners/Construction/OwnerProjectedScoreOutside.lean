import Paper.Owners.Construction.OwnerProjectedRole
import Paper.Owners.Construction.OwnerRoleScoreZero
import Paper.Preliminaries.RoleInputSemantics

namespace Paper.OwnerProjectedScoreOutside
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem zero {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a B q M : ℕ) (c : V → Fin (B + 1))
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (U : Finset V)
    (hU : U ∈ (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).parts)
    (anchor : V) (ha : anchor ∈ U) (hl : FinitePriorityIndex.leader U anchor = anchor) (v : V)
    (hv : v ∉ PhysicalTasks.vertices G D R L (OwnerVirtualFacts.high G D R L Δ)
      (OwnerPublicTasks.pull D (OwnerVirtualFacts.high G D R L Δ) U)) :
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v
      (OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ U anchor) = 0 := by
  let role := OwnerProjectedRole.role G D R L Δ k Q T s hQ ζ U anchor
  let d := OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ role
  obtain ⟨hd, hvalid, _⟩ := OwnerProjectedRole.spec G C D R L Δ k hk t ht Q T s hQ hs ζ U hU anchor ha hl
  change d.owners = U at hd
  have hsub : d.owners ⊆ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ) := by
    rw [hd]
    exact (OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ).subset U hU
  have hactive := RoleInputSemantics.active G D R L (OwnerVirtualFacts.high G D R L Δ) d hvalid hsub c v
  rw [hd] at hactive
  simp only [decide_eq_false hv] at hactive
  exact OwnerRoleScoreZero.inactive G C D R hcover L Δ r k t Q T s a B q M hQ hks c v role hactive

end Paper.OwnerProjectedScoreOutside
