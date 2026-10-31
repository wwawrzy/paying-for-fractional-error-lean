import Paper.Owners.Construction.OwnerRoleInputsCorrect
import Paper.Preliminaries.CanonicalRoleFrame

namespace Paper.OwnerRoleCoverage
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem anchor_low {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) (hk : k ≤ r) (c : V → Fin (B + 1)) (v : V)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (hr : role ∈ TaggedDictionary.keys ((OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
      (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v)) :
    (ofLex role).1 ∈ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ) := by
  rw [OwnerRoleInputs.keys, TaskRoleId.mem_space] at hr
  exact CanonicalRoleFrame.anchors_low G C D R hcover L Δ r k hk v (ofLex role).1 hr

theorem task_covered {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) (hk : k ≤ r) (c : V → Fin (B + 1))
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (I : Finset (OwnerTasks.Low D (OwnerVirtualFacts.high G D R L Δ)))
    (hI : ((OwnerTasks.graph G D R L (OwnerVirtualFacts.high G D R L Δ)).induce (I : Set _)).Connected)
    (hsize : I.card ≤ k) (ha : (ofLex role).1 ∈ PhysicalTasks.centers D (OwnerVirtualFacts.high G D R L Δ) I) :
    ∀ v ∈ PhysicalTasks.vertices G D R L (OwnerVirtualFacts.high G D R L Δ) I,
      role ∈ TaggedDictionary.keys ((OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
        (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v) := by
  intro v hv
  rw [OwnerRoleInputs.keys, TaskRoleId.mem_space]
  exact OwnerRootFrameCorrect.task_anchor G C D R hcover L Δ r k hk I hI hsize v (ofLex role).1 hv ha

end Paper.OwnerRoleCoverage
