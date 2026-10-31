import Paper.Owners.Construction.OwnerRoleTaskComplete

/-! Explicit projected metadata for a given global source and public part.
The entire projected-role correctness statement uses this exact number. -/
namespace Paper.OwnerProjectedRole
open BroadcastModel SevenFoundation NeighborBalls
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def index (D R : Finset V) (L Δ k Q T s : ℕ) (hQ : 0 < Q)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (I : Finset V) (a : V) :
    Fin (OwnerRoleInputs.metadataCount Δ k Q T s) :=
  let xs := OwnerRoleInputsCorrect.canonical G D R L Δ s a
  OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ
    (OwnerRoleTaskData.addresses xs) ζ
    (FiniteSubsetCode.encode ((ball (FrameInterpreter.neighbors xs) a k).sort (· ≤ ·)) ((Δ + 1) ^ k) I)

noncomputable def role (D R : Finset V) (L Δ k Q T s : ℕ) (hQ : 0 < Q)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (I : Finset V) (a : V) :
    TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s) :=
  TaskRoleId.make a (index G D R L Δ k Q T s hQ ζ I a)

theorem spec {b : ℕ} (C : BitCode V b) (D S : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (I : Finset V)
    (hI : I ∈ (OwnerRoleTaskSound.partition G D S L Δ k hk t Q T hQ ζ).parts)
    (a : V) (ha : a ∈ I) (hleader : FinitePriorityIndex.leader I a = a) :
    let i := index G D S L Δ k Q T s hQ ζ I a
      let d := OwnerRoleTaskData.compute C Δ k t Q T ((Δ + 1) ^ s) hQ a i
        (OwnerRoleInputsCorrect.canonical G D S L Δ s a)
      d.owners = I ∧ d.valid = true ∧
        ∀ u ∈ I, d.boundary u = decide (u ∈ BoundaryOwners.vertices
          (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ))
          (OwnerRoleTaskSound.partition G D S L Δ k hk t Q T hQ ζ).parts) := by
  let J := PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)
  let low := PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)
  let P := OwnerRoleTaskSound.partition G D S L Δ k hk t Q T hQ ζ
  let xs := OwnerRoleInputsCorrect.canonical G D S L Δ s a
  let N := FrameInterpreter.neighbors xs
  let l := (ball N a k).sort (· ≤ ·)
  let mask := FiniteSubsetCode.encode l ((Δ + 1) ^ k) I
  let i := OwnerRoleConfigProjection.project ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) hQ
    (OwnerRoleTaskData.addresses xs) ζ mask
  let d := OwnerRoleTaskData.compute C Δ k t Q T ((Δ + 1) ^ s) hQ a i xs
  have hF := CanonicalRoleFrame.addresses_length G D S L Δ s a
  have hb : ball N a k = ball (fun u => J.neighborFinset u) a k :=
    CanonicalRoleFrame.ball_eq G D S L Δ s k (by omega) a
  have hIball : I ⊆ ball (fun u => J.neighborFinset u) a k := by
    have hh := CandidateGeometry.connected_subset_ball J I (P.connected I hI) k (P.size I hI)
      a ha a 0 (self_mem _ a 0)
    simpa only [Nat.zero_add] using hh
  have hlen : l.length ≤ (Δ + 1) ^ k := by
    dsimp only [l]
    rw [Finset.length_sort, hb]
    exact NeighborBallGraph.graph_card_bound J Δ (PublicOwners.degree_bound G D S L Δ) a k
  have hdecoded : d.owners = I := by
    change FiniteSubsetCode.decode l ((Δ + 1) ^ k)
      (OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i) = I
    rw [OwnerRoleConfigProjection.mask_project]
    apply FiniteSubsetCode.decode_encode l _ hlen I
    dsimp only [l]
    rw [Finset.sort_toFinset, hb]
    exact hIball
  have hζ : ∀ j : Fin (OwnerRoleTaskData.addresses xs).length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i
        (LocalSeedRecords.slot (OwnerRoleTaskData.addresses xs) hF j) =
      ζ ((OwnerRoleTaskData.addresses xs).get j) :=
    OwnerRoleConfigProjection.table_project _ Q T _ hQ _ hF ζ mask
  have haLow : a ∈ low := P.subset I hI ha
  have hview : ∀ u ∈ ball (fun w => J.neighborFinset w) a k,
      OwnerRoleTaskData.view C Δ k t Q T ((Δ + 1) ^ s) hQ i xs u =
        (decide (u ∈ BoundaryOwners.vertices J low P.parts), DisjointPartLabels.label P.parts u) := by
    intro u hu
    have hcoverage : ball (fun w => J.neighborFinset w) u (T * (3 * k + 1) + 1) ⊆
        TaggedDictionary.keys xs := by
      rw [CanonicalRoleFrame.keys G D S L Δ s a]
      exact (subball _ k _ a u hu).trans (monotone _ a hs)
    rw [OwnerRoleViewCorrect.view_correct J C Δ k t Q T ((Δ + 1) ^ s) hQ i xs hF ζ hζ
      (CanonicalRoleFrame.record_true G D S L Δ s a) u hcoverage]
    rw [OwnerRoleViewCorrect.all_true_eq J C Δ k t Q T hQ low (fun v hv w hw =>
      ClosedNeighborBalls.owner_subset G D S L _ v hv 1 (neighbor_mem _ v w hw)) ζ u
        (ClosedNeighborBalls.owner_subset G D S L _ a haLow k hu)]
    exact PriorityTaskView.correct J C Δ k hk t ht Q T hQ low ζ (PublicOwners.degree_bound G D S L Δ) u
  have hvalid : d.valid = true := by
    apply decide_eq_true
    refine ⟨hF, ?_, ?_, ?_, ?_, ?_⟩
    · change OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s) i =
        FiniteSubsetCode.encode l ((Δ + 1) ^ k) d.owners
      rw [hdecoded]
      exact OwnerRoleConfigProjection.mask_project _ Q T _ hQ _ ζ mask
    · change d.owners.card ≤ k
      rw [hdecoded]
      exact P.size I hI
    · change a ∈ d.owners
      rwa [hdecoded]
    · change FinitePriorityIndex.leader d.owners a = a
      rwa [hdecoded]
    · change (OwnerRoleTaskData.view C Δ k t Q T ((Δ + 1) ^ s) hQ i xs a).2 = d.owners
      rw [hview a (self_mem _ a k), hdecoded]
      exact DisjointPartLabels.eq_of_mem P.parts P.disjoint I hI a ha
  refine ⟨hdecoded, hvalid, ?_⟩
  intro u hu
  exact congrArg Prod.fst (hview u (hIball hu))

end Paper.OwnerProjectedRole
