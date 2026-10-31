import Paper.Owners.Construction.OwnerRoleInputsCorrect
import Paper.Partitions.Local.ClosedNeighborBalls

namespace Paper.CanonicalRoleFrame
open BroadcastModel SevenFoundation NeighborBalls
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem keys (D S : Finset V) (L Δ s : ℕ) (a : V) :
    TaggedDictionary.keys (OwnerRoleInputsCorrect.canonical G D S L Δ s a) =
      ball (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) a s := by
  simp [OwnerRoleInputsCorrect.canonical, TaggedDictionary.keys, List.map_map,
    Function.comp_def, TopologyGather.localData, Finset.sort_toFinset]

theorem record_true (D S : Finset V) (L Δ s : ℕ) (a : V) :
    ∀ p ∈ OwnerRoleInputsCorrect.canonical G D S L Δ s a, p.2.val.toFinset =
      (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset p.1 := by
  intro p hp
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
  have ht := TopologyGather.true_neighbors
    (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) Δ
      (PublicOwners.degree_bound G D S L Δ) u
  exact (congrArg List.toFinset ht).trans (Finset.sort_toFinset _ _)

theorem addresses_length (D S : Finset V) (L Δ s : ℕ) (a : V) :
    (OwnerRoleTaskData.addresses (OwnerRoleInputsCorrect.canonical G D S L Δ s a)).length ≤ (Δ + 1) ^ s := by
  rw [OwnerRoleTaskData.addresses, Finset.length_sort, keys G D S L Δ s a]
  exact NeighborBallGraph.graph_card_bound _ Δ (PublicOwners.degree_bound G D S L Δ) a s

theorem neighbors (D S : Finset V) (L Δ s : ℕ) (a u : V)
    (hu : u ∈ ball (fun w => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset w) a s) :
    FrameInterpreter.neighbors (OwnerRoleInputsCorrect.canonical G D S L Δ s a) u =
      (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u := by
  apply FrameInterpreter.neighbors_correct _ _ (record_true G D S L Δ s a) u
  rwa [keys G D S L Δ s a]

theorem ball_eq (D S : Finset V) (L Δ s k : ℕ) (hk : k ≤ s) (a : V) :
    ball (FrameInterpreter.neighbors (OwnerRoleInputsCorrect.canonical G D S L Δ s a)) a k =
      ball (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) a k := by
  apply (FiniteBallAgreement.balls_eq _ _ a k _).symm
  intro u hu
  exact (neighbors G D S L Δ s a u (monotone _ a hk hu)).symm

theorem anchors_low {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k : ℕ) (hk : k ≤ r) (v a : V)
    (ha : a ∈ RootFrameUnion.anchors k (OwnerRootFrameCorrect.received G C D S L Δ r v)) :
    a ∈ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ) := by
  rw [OwnerRootFrameCorrect.anchors_eq G C D S hcover L Δ r k hk v] at ha
  obtain ⟨u, hu, ha⟩ := Finset.mem_biUnion.mp ha
  exact ClosedNeighborBalls.owner_subset G D S L _ u (Finset.mem_inter.mp hu).2 k ha

end Paper.CanonicalRoleFrame
