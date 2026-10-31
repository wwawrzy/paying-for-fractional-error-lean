import Paper.Preliminaries.CanonicalRoleFrame
import Paper.Owners.Construction.OwnerRoleViewCorrect
import Paper.Averaging.Tasks.RoleTaskChecks

/-! Every valid decoded role is a genuine part of an actual priority
partition under a global extension of its finite local configuration.
Boundary flags throughout the part are the genuine partition boundary. -/
namespace Paper.OwnerRoleTaskSound
open BroadcastModel SevenFoundation NeighborBalls
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def partition (D S : Finset V) (L Δ k : ℕ) (hk : 0 < k)
    (t Q T : ℕ) (hQ : 0 < Q) (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) :=
  PriorityPartition.partition (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
    k hk (1 / (t : ℝ)) (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) T
      (PriorityNormalization.localSeed (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
        Δ k Q hQ T (fun p => ζ p.2.1 (p.1, p.2.2)))

theorem sound {b : ℕ} (C : BitCode V b) (D S : Finset V)
    (L Δ k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hs : k + (T * (3 * k + 1) + 1) ≤ s) (a : V)
    (ha : a ∈ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ))
    (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T ((Δ + 1) ^ s))) :
    ∃ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      let P := partition G D S L Δ k hk t Q T hQ ζ
      let d := OwnerRoleTaskData.compute C Δ k t Q T ((Δ + 1) ^ s) hQ a i
        (OwnerRoleInputsCorrect.canonical G D S L Δ s a)
      d.valid = true → d.owners ∈ P.parts ∧
        ∀ u ∈ d.owners, d.boundary u = decide (u ∈ BoundaryOwners.vertices
          (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ))
          (PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)) P.parts) := by
  let xs := OwnerRoleInputsCorrect.canonical G D S L Δ s a
  have hF := CanonicalRoleFrame.addresses_length G D S L Δ s a
  obtain ⟨ζ, hζ⟩ := OwnerRoleViewCorrect.extension Δ k Q T ((Δ + 1) ^ s) hQ i xs hF
  refine ⟨ζ, ?_⟩
  dsimp only
  intro hvalid
  let J := PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)
  let low := PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)
  let P := partition G D S L Δ k hk t Q T hQ ζ
  let d := OwnerRoleTaskData.compute C Δ k t Q T ((Δ + 1) ^ s) hQ a i xs
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
        (ClosedNeighborBalls.owner_subset G D S L _ a ha k hu)]
    exact PriorityTaskView.correct J C Δ k hk t ht Q T hQ low ζ (PublicOwners.degree_bound G D S L Δ) u
  have hIball : d.owners ⊆ ball (fun w => J.neighborFinset w) a k := by
    have hh := RoleTaskChecks.owners_subset C Δ k t Q T ((Δ + 1) ^ s) hQ a i xs
    rwa [CanonicalRoleFrame.ball_eq G D S L Δ s k (by omega) a] at hh
  have hlabel : DisjointPartLabels.label P.parts a = d.owners := by
    have hh := RoleTaskChecks.valid_label C Δ k t Q T ((Δ + 1) ^ s) hQ a i xs hvalid
    rw [hview a (self_mem _ a k)] at hh
    exact hh
  obtain ⟨U, hU, _, he⟩ := DisjointPartLabels.exists_part J low k P a ha
  refine ⟨?_, ?_⟩
  · change d.owners ∈ P.parts
    rw [← hlabel, he]
    exact hU
  · intro u hu
    exact congrArg Prod.fst (hview u (hIball hu))

end Paper.OwnerRoleTaskSound
