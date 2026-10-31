import Paper.Owners.Construction.OwnerRootFrames
import Paper.Preliminaries.RootFrameUnion

/-! The actually received finite root frames suffice for every task anchor
and give the same canonical anchor frame at all its physical participants. -/
namespace Paper.OwnerRootFrameCorrect
open BroadcastModel SevenFoundation NeighborBalls
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

def received {b : ℕ} (C : BitCode V b) (D S : Finset V) (L Δ r : ℕ) (v : V) :=
  (((OwnerRootFrames.program C L Δ r).run G
    (fun u => (decide (u ∈ D), decide (u ∈ S))) v).1).val

theorem frame_keys {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    ∀ p ∈ received G C D S L Δ r v, TaggedDictionary.keys p.2.val =
      ball (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) p.1 r := by
  intro p hp
  have he := OwnerRootFrames.consistent G C D S hcover L Δ r v p hp
  rw [he]
  exact OwnerFramePayload.frame_keys G C D S hcover L Δ r p.1

theorem frame_true {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r : ℕ) (v : V) :
    ∀ p ∈ received G C D S L Δ r v, ∀ a ∈ p.2.val, a.2.val.toFinset =
      (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset a.1 := by
  intro p hp a ha
  have he := OwnerRootFrames.consistent G C D S hcover L Δ r v p hp
  rw [he] at ha
  exact OwnerFramePayload.record_true G C D S hcover L Δ r p.1 a ha

theorem anchors_eq {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k : ℕ) (hk : k ≤ r) (v : V) :
    RootFrameUnion.anchors k (received G C D S L Δ r v) =
      (RoleAnchorGeometry.roots G D S L v ∩ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ)).biUnion
        (fun u => ball (fun w => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset w) u k) := by
  rw [RootFrameUnion.anchors_eq _ _ (frame_keys G C D S hcover L Δ r v)
    (frame_true G C D S hcover L Δ r v) k hk]
  rw [received, OwnerRootFrames.keys G C D S hcover L Δ r v]

theorem anchors_subset {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k : ℕ) (hk : k ≤ r) (v : V) :
    RootFrameUnion.anchors k (received G C D S L Δ r v) ⊆ RoleAnchorGeometry.anchors G D S L Δ k v := by
  rw [anchors_eq G C D S hcover L Δ r k hk v]
  unfold RoleAnchorGeometry.anchors
  intro a ha
  obtain ⟨u, hu, ha⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr ⟨u, (Finset.mem_inter.mp hu).1, ha⟩

theorem anchors_card {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k : ℕ) (hk : k ≤ r) (v : V) :
    (RootFrameUnion.anchors k (received G C D S L Δ r v)).card ≤ (L + 1) * (Δ + 1) ^ k :=
  (Finset.card_le_card (anchors_subset G C D S hcover L Δ r k hk v)).trans
    (RoleAnchorGeometry.anchors_card G D S L Δ k v)

theorem task_anchor {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k : ℕ) (hk : k ≤ r)
    (I : Finset (OwnerTasks.Low D (OwnerVirtualFacts.high G D S L Δ)))
    (hI : ((OwnerTasks.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).induce (I : Set _)).Connected)
    (hsize : I.card ≤ k) (v a : V)
    (hv : v ∈ PhysicalTasks.vertices G D S L (OwnerVirtualFacts.high G D S L Δ) I)
    (ha : a ∈ PhysicalTasks.centers D (OwnerVirtualFacts.high G D S L Δ) I) :
    a ∈ RootFrameUnion.anchors k (received G C D S L Δ r v) := by
  obtain ⟨u, hu, huI⟩ := RoleAnchorGeometry.touches G D S L _ I v hv
  have huLow : u ∈ PublicOwners.image D (OwnerVirtualFacts.high G D S L Δ) := by
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    unfold PhysicalTasks.centers at huI
    rw [hinst] at huI
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp huI
    unfold PublicOwners.image
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  rw [anchors_eq G C D S hcover L Δ r k hk v]
  refine Finset.mem_biUnion.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, huLow⟩, ?_⟩
  have hc := RoleAnchorGeometry.centers_connected G D S L _ I hI
  have hs : (PhysicalTasks.centers D (OwnerVirtualFacts.high G D S L Δ) I).card ≤ k :=
    (PhysicalTasks.centers_card D _ I).trans_le hsize
  have hh := CandidateGeometry.connected_subset_ball _ _ hc k hs u huI u 0 (self_mem _ u 0) ha
  simpa only [Nat.zero_add] using hh

theorem canonical_eq {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k s : ℕ) (hks : k + s ≤ r) (v a : V)
    (ha : a ∈ RootFrameUnion.anchors k (received G C D S L Δ r v)) :
    RootFrameUnion.canonical s a (received G C D S L Δ r v) =
      (ball (fun u => (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)).neighborFinset u) a s).sort.map
        (TopologyGather.localData (PublicOwners.graph G D S L (OwnerVirtualFacts.high G D S L Δ)) Δ) :=
  RootFrameUnion.canonical_eq _ _ (frame_keys G C D S hcover L Δ r v)
    (frame_true G C D S hcover L Δ r v) k s hks a ha

theorem canonical_common {b : ℕ} (C : BitCode V b) (D S : Finset V) (hcover : S ⊆ covered G D)
    (L Δ r k s : ℕ) (hks : k + s ≤ r) (v w a : V)
    (hv : a ∈ RootFrameUnion.anchors k (received G C D S L Δ r v))
    (hw : a ∈ RootFrameUnion.anchors k (received G C D S L Δ r w)) :
    RootFrameUnion.canonical s a (received G C D S L Δ r v) =
      RootFrameUnion.canonical s a (received G C D S L Δ r w) := by
  rw [canonical_eq G C D S hcover L Δ r k s hks v a hv,
    canonical_eq G C D S hcover L Δ r k s hks w a hw]

end Paper.OwnerRootFrameCorrect
