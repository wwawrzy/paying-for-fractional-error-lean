import Paper.Owners.Construction.OwnerRoleScoreLocality

namespace Paper.OwnerRoleScoreAbsent
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem anchor {b : ℕ} (C : BitCode V b) (D R : Finset V)
    (L Δ r k t Q T s a B q M : ℕ) (hQ : 0 < Q) (c : V → Fin (B + 1)) (v u : V)
    (hu : u ∉ RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D R L Δ r v))
    (i : Fin (OwnerRoleInputs.metadataCount Δ k Q T s)) :
    OwnerRoleScoreLocality.score G C D R L Δ r k t Q T s a B q M hQ c v (TaskRoleId.make u i) = 0 := by
  unfold OwnerRoleScoreLocality.score
  rw [SparseFractionalZero.lookup_none _ (TaskRoleId.make u i) (by
    rw [OwnerRoleNumerator.keys G C D R L Δ r k t Q T s a B q M hQ c v, TaskRoleId.mem_space]
    exact hu)]
  rfl

end Paper.OwnerRoleScoreAbsent
