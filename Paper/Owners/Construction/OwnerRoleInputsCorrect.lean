import Paper.Owners.Construction.OwnerRoleInputs

/-! Every actual role input uses one common canonical anchor-frame
interpretation and its vertex's actual private owner metadata and cost. -/
namespace Paper.OwnerRoleInputsCorrect
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def canonical (D S : Finset V) (L Δ s : ℕ) (a : V) : List (TopologyGather.Record V Δ) :=
  (NeighborBalls.ball (fun u =>
    (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) a s).sort.map
      (TopologyGather.localData (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) Δ)

noncomputable def task {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ k t Q T s : ℕ) (hQ : 0 < Q)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s)) : OwnerRoleTaskData.Task V :=
  OwnerRoleTaskData.compute C Δ k t Q T ((Δ + 1) ^ s) hQ (ofLex role).1 (ofLex role).2
    (canonical G D S L Δ s (ofLex role).1)

noncomputable def expected {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ k t Q T s B : ℕ) (hQ : 0 < Q)
    (c : V → Fin (B + 1)) (v : V)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s)) : FractionalSearch.Input V B :=
  OwnerRoleTaskData.input (task G C D S L Δ k t Q T s hQ role) (OwnerMetadataCorrect.expected G D S L v) (c v)

theorem consistent {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k t Q T s B : ℕ) (hQ : 0 < Q) (hks : k + s ≤ r) (c : V → Fin (B + 1)) (v : V) :
    TaggedDictionary.Consistent (expected G C D S L Δ k t Q T s B hQ c v)
      ((OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
        (fun u => ((decide (u ∈ D), decide (u ∈ S)), c u)) v) := by
  rw [OwnerRoleInputs.run_program]
  intro p hp
  obtain ⟨role, hrole, rfl⟩ := List.mem_map.mp hp
  have hr : role ∈ TaskRoleId.space
      (RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D S L Δ r v))
      (OwnerRoleInputs.metadataCount Δ k Q T s) := (Finset.mem_sort (· ≤ ·)).mp hrole
  have ha := (TaskRoleId.mem_space _ _ role).mp hr
  have hframe := OwnerRootFrameCorrect.canonical_eq G C D S hcover L Δ r k s hks v (ofLex role).1 ha
  have hmeta : (((OwnerRoleFrames.program C L Δ r k).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2.2).metadata =
      OwnerMetadataCorrect.expected G D S L v := by
    change (((OwnerRootFrames.program C L Δ r).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2).metadata = _
    rw [OwnerRootFrames.run_program G C D S hcover L Δ r v]
    exact OwnerVirtualCorrect.metadata_correct G C D S L Δ v
  change OwnerRoleInputs.value C Δ r k t Q T s B hQ
    (OwnerRootFrameCorrect.received G C D S L Δ r v)
    (((OwnerRoleFrames.program C L Δ r k).run G
      (fun u => (decide (u ∈ D), decide (u ∈ S))) v).2.2) (c v) role = _
  dsimp only [OwnerRoleInputs.value]
  rw [hframe, hmeta]
  rfl

end Paper.OwnerRoleInputsCorrect
