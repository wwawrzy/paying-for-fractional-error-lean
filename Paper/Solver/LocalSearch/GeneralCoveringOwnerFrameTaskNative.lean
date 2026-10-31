import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskInputs
import Paper.Preliminaries.LocalSeedExtension

/-! Exact current-partition views at every owner of a candidate task.
All queried owners share one restricted global Boolean assignment, and the
larger canonical frame contains each queried owner's whole partition ball.
These are local decoder facts, preceding task execution and its finite mean. -/
namespace Paper.GeneralCoveringOwnerFrameTaskNative
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry NeighborBalls
open GeneralCoveringOwnerFrameTaskData
variable {V : Type} [LinearOrder V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only distinct frame addresses are extended; slot types never embed in V. -/
theorem extension (Δ k b n : ℕ) (i : Metadata Δ k b n) (xs : List (TopologyGather.Record V Δ))
    (h : (GeneralCoveringOwnerFramePartition.addresses xs).length ≤ frameSlots Δ k n) :
    ∃ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
      ∀ j, coins Δ k b n i (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) h j) =
        β ((GeneralCoveringOwnerFramePartition.addresses xs).get j) := by
  let l := GeneralCoveringOwnerFramePartition.addresses xs
  let τ := fun j => coins Δ k b n i (LocalSeedRecords.slot l h j)
  refine ⟨FrameInterpreter.inputs (LocalSeedRecords.base l τ)
    (GeneralCoveringOwnerFramePartition.zeroBits Δ k b n), ?_⟩
  intro j
  exact (LocalSeedExtension.inputs_get l (Finset.sort_nodup _ _) τ _ j).symm

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

section Correct
variable (C targets : V → Finset V) (D R : Finset V) (L Δ k t b n : ℕ)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
variable (input : V → GeneralCoveringOwners.Input V)
variable (hD : ∀ v, (input v).center = decide (v ∈ D)) (hR : ∀ v, (input v).demand = decide (v ∈ R))
variable (hC : ∀ v, (input v).candidates = C v) (hTargets : ∀ v, (input v).targets = targets v)
include hinc hlocal hD hR hC hTargets
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q
local notation "s" => frameRadius k n
local notation "r" => GeneralCoveringOwnerFrameTaskInputs.outerRadius k n

variable {idBits : ℕ} (ids : BitCode V idBits)

local notation "source" => Program.runEncoded G (GeneralCoveringOwnerRoleFrames.program ids L Δ r k s) input
local notation "xs" => GeneralCoveringOwnerRoleFrames.canonical G ids L Δ r s input

theorem frame_keys (v a : V) (ha : a ∈ (source v).anchors) :
    TaggedDictionary.keys (xs v a) = ball (fun w => SimpleGraph.neighborFinset J w) a s :=
  GeneralCoveringOwnerRoleFrames.canonical_keys G C targets D R L Δ r k s
    hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v a ha

theorem frame_capacity (v a : V) (ha : a ∈ (source v).anchors) :
    (GeneralCoveringOwnerFramePartition.addresses (xs v a)).length ≤ frameSlots Δ k n := by
  rw [GeneralCoveringOwnerFramePartition.addresses, Finset.length_sort,
    frame_keys G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha]
  exact NeighborBallGraph.graph_card_bound J Δ (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a s

theorem frame_low (v a : V) (ha : a ∈ (source v).anchors) :
    (GeneralCoveringOwnerFramePartition.addresses (xs v a)).toFinset ⊆ U := by
  rw [GeneralCoveringOwnerFramePartition.addresses, Finset.sort_toFinset,
    frame_keys G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha]
  apply GeneralCoveringOwnerRoleFrames.ball_low G C targets D R L Δ hinc hlocal input hD hR hC hTargets
  exact GeneralCoveringOwnerRoleFrames.anchors_low G C targets D R L Δ r k s
    hinc hlocal input hD hR hC hTargets ids (Nat.le_add_right _ _) v ha

/-- The same beta is used at all owners in the k-ball around the task anchor. -/
theorem view_native (v a u : V) (ha : a ∈ (source v).anchors)
    (hu : u ∈ ball (fun w => SimpleGraph.neighborFinset J w) a k)
    (i : Metadata Δ k b n) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (hβ : ∀ j, coins Δ k b n i (LocalSeedRecords.slot
      (GeneralCoveringOwnerFramePartition.addresses (xs v a))
      (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) j) =
        β ((GeneralCoveringOwnerFramePartition.addresses (xs v a)).get j)) :
    view ids Δ k t b n i (xs v a) u =
      (ActiveFiniteBitPartition.program ids Δ k t b n).runEncoded J (fun w => (decide (w ∈ U), β w)) u := by
  apply view_restricted J ids Δ k t b n i (xs v a) U β u
    (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) _ _
    (frame_low G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) hβ
  · intro p hp
    have ht := GeneralCoveringOwnerRoleFrames.canonical_true G C targets D R L Δ r k s
      hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v a ha p hp
    exact (congrArg List.toFinset ht).trans (Finset.sort_toFinset _ _)
  · rw [ActiveFiniteBitPartition.rounds,
      frame_keys G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha]
    exact subball _ k (GeneralCoveringOwnerFramePartition.radius k n) a u hu

/-- Full label and every task-owner boundary bit refer to one actual partition. -/
theorem view_partition (hk : 0 < k) (ht : 0 < t) (v a u : V) (ha : a ∈ (source v).anchors)
    (hu : u ∈ ball (fun w => SimpleGraph.neighborFinset J w) a k)
    (i : Metadata Δ k b n) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (hβ : ∀ j, coins Δ k b n i (LocalSeedRecords.slot
      (GeneralCoveringOwnerFramePartition.addresses (xs v a))
      (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) j) =
        β ((GeneralCoveringOwnerFramePartition.addresses (xs v a)).get j)) :
    let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
    view ids Δ k t b n i (xs v a) u =
      (DisjointPartLabels.label P.parts u, decide (u ∈ BoundaryOwners.vertices J U P.parts)) := by
  exact (view_native G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a u ha hu i β hβ).trans
    (ActiveFiniteBitPartition.correct J ids Δ k hk t ht b n U β
      (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) u)

/-- All carriers of one role decode the same task from the same finite data. -/
theorem common (v w a : V) (hv : a ∈ (source v).anchors) (hw : a ∈ (source w).anchors)
    (i : Metadata Δ k b n) :
    compute ids Δ k t b n a i (xs v a) = compute ids Δ k t b n a i (xs w a) :=
  same_frame ids Δ k t b n a i _ _ (GeneralCoveringOwnerRoleFrames.canonical_common G C targets D R L Δ r k s
    hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v w a hv hw)

/-- Every decoded candidate owner stays in the anchor's bounded k-ball. -/
theorem owners_ball (v a : V) (ha : a ∈ (source v).anchors) (i : Metadata Δ k b n) :
    (compute ids Δ k t b n a i (xs v a)).owners ⊆ ball (fun w => SimpleGraph.neighborFinset J w) a k := by
  have hs := FiniteSubsetCode.decode_subset
    ((ball (FrameInterpreter.neighbors (xs v a)) a k).sort (· ≤ ·)) (partSlots Δ k)
    (OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i)
  rw [Finset.sort_toFinset] at hs
  change FiniteSubsetCode.decode ((ball (FrameInterpreter.neighbors (xs v a)) a k).sort (· ≤ ·))
    (partSlots Δ k) (OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i) ⊆ _
  apply hs.trans
  rw [GeneralCoveringOwnerRoleFrames.canonical_ball G C targets D R L Δ r k s
    hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v a ha k (Nat.le_add_right _ _)]

/-- A valid role is a genuine current part, with all its owner's boundary bits. -/
theorem sound (hk : 0 < k) (ht : 0 < t) (v a : V) (ha : a ∈ (source v).anchors)
    (i : Metadata Δ k b n) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (hβ : ∀ j, coins Δ k b n i (LocalSeedRecords.slot
      (GeneralCoveringOwnerFramePartition.addresses (xs v a))
      (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) j) =
        β ((GeneralCoveringOwnerFramePartition.addresses (xs v a)).get j))
    (hv : (compute ids Δ k t b n a i (xs v a)).valid = true) :
    let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
    let d := compute ids Δ k t b n a i (xs v a)
    d.owners ∈ P.parts ∧ a ∈ d.owners ∧ d.owners.card ≤ k ∧
      ((J).induce (d.owners : Set V)).Connected ∧
      ∀ u ∈ d.owners, d.boundary u = decide (u ∈ BoundaryOwners.vertices J U P.parts) := by
  let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
  let d := compute ids Δ k t b n a i (xs v a)
  have hview : (view ids Δ k t b n i (xs v a) a).1 = d.owners := by
    simp only [compute, decide_eq_true_eq] at hv
    exact hv.2.2.2.2
  have haU : a ∈ U := GeneralCoveringOwnerRoleFrames.anchors_low G C targets D R L Δ r k s
    hinc hlocal input hD hR hC hTargets ids (Nat.le_add_right _ _) v ha
  obtain ⟨T, hT, haT, hlabel⟩ := DisjointPartLabels.exists_part J U k P a haU
  have hpa := view_partition G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids
    hk ht v a a ha (self_mem _ _ _) i β hβ
  have hd : d.owners = T := hview.symm.trans ((congrArg Prod.fst hpa).trans hlabel)
  refine ⟨hd.symm ▸ hT, hd.symm ▸ haT, hd.symm ▸ P.size T hT, hd.symm ▸ P.connected T hT, ?_⟩
  intro u hu
  exact congrArg Prod.snd (view_partition G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids
    hk ht v a u ha (owners_ball G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids v a ha i hu) i β hβ)

/-- Every actual part fits in the bounded local subset enumeration. -/
theorem part_ball (hk : 0 < k) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (T : Finset V) (hT : T ∈ (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts)
    (a : V) (ha : a ∈ T) : T ⊆ ball (fun w => SimpleGraph.neighborFinset J w) a k := by
  let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
  let f : (J).induce (T : Set V) →g J := { toFun := Subtype.val, map_rel' := by intro x y h; exact h }
  intro u hu
  obtain ⟨p, hp⟩ := (P.connected T hT (⟨a, ha⟩ : ↥(T : Set V)) ⟨u, hu⟩).exists_isPath
  have hlen : p.length < T.card := by simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hp.length_lt
  apply NeighborBallGraph.walk_mem J (p.map f) k
  rw [SimpleGraph.Walk.length_map]
  have hsize := P.size T hT
  omega

/-- Canonical masks recognize every actual part at its unique minimum anchor. -/
theorem complete (hk : 0 < k) (ht : 0 < t) (v a : V) (ha : a ∈ (source v).anchors)
    (i : Metadata Δ k b n) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (hβ : ∀ j, coins Δ k b n i (LocalSeedRecords.slot
      (GeneralCoveringOwnerFramePartition.addresses (xs v a))
      (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha) j) =
        β ((GeneralCoveringOwnerFramePartition.addresses (xs v a)).get j))
    (T : Finset V) (hT : T ∈ (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts)
    (hmin : MaskedMinimum.minimum T = some a)
    (hmask : OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i =
      FiniteSubsetCode.encode ((ball (FrameInterpreter.neighbors (xs v a)) a k).sort (· ≤ ·)) (partSlots Δ k) T) :
    (compute ids Δ k t b n a i (xs v a)).owners = T ∧
      (compute ids Δ k t b n a i (xs v a)).valid = true := by
  let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
  let l := (ball (FrameInterpreter.neighbors (xs v a)) a k).sort (· ≤ ·)
  have hball : ball (FrameInterpreter.neighbors (xs v a)) a k = ball (fun w => SimpleGraph.neighborFinset J w) a k :=
    GeneralCoveringOwnerRoleFrames.canonical_ball G C targets D R L Δ r k s
      hinc hlocal input hD hR hC hTargets ids (Nat.le_refl _) v a ha k (Nat.le_add_right _ _)
  have hlen : l.length ≤ partSlots Δ k := by
    rw [Finset.length_sort, hball]
    exact NeighborBallGraph.graph_card_bound J Δ (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a k
  have hsub : T ⊆ l.toFinset := by
    rw [Finset.sort_toFinset, hball]
    exact part_ball G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets hk β T hT a (MaskedMinimum.minimum_mem hmin)
  have hdec : FiniteSubsetCode.decode l (partSlots Δ k)
      (OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i) = T := by
    rw [hmask]
    exact FiniteSubsetCode.decode_encode l (partSlots Δ k) hlen T hsub
  have hview : (view ids Δ k t b n i (xs v a) a).1 = T :=
    (congrArg Prod.fst (view_partition G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids
      hk ht v a a ha (self_mem _ _ _) i β hβ)).trans
      (DisjointPartLabels.eq_of_mem P.parts P.disjoint T hT a (MaskedMinimum.minimum_mem hmin))
  dsimp only [compute]
  rw [hdec]
  simp only [decide_eq_true_eq]
  exact ⟨True.intro, frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha,
    hmask, P.size T hT, hmin, hview⟩

/-- Every valid role has an actual global-coin interpretation, derived locally. -/
theorem sound_exists (hk : 0 < k) (ht : 0 < t) (v a : V) (ha : a ∈ (source v).anchors)
    (i : Metadata Δ k b n) (hv : (compute ids Δ k t b n a i (xs v a)).valid = true) :
    ∃ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
      let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
      let d := compute ids Δ k t b n a i (xs v a)
      d.owners ∈ P.parts ∧ a ∈ d.owners ∧ d.owners.card ≤ k ∧
        ((J).induce (d.owners : Set V)).Connected ∧
        ∀ u ∈ d.owners, d.boundary u = decide (u ∈ BoundaryOwners.vertices J U P.parts) := by
  obtain ⟨β, hβ⟩ := extension Δ k b n i (xs v a)
    (frame_capacity G C targets D R L Δ k n hinc hlocal input hD hR hC hTargets ids v a ha)
  exact ⟨β, sound G C targets D R L Δ k t b n hinc hlocal input hD hR hC hTargets ids hk ht v a ha i β hβ hv⟩

end Correct
end Paper.GeneralCoveringOwnerFrameTaskNative

#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.frame_keys
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.frame_capacity
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.frame_low
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.view_native
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.view_partition

#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.owners_ball
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.sound

#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.extension
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.sound_exists

#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.common

#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.part_ball
#print axioms Paper.GeneralCoveringOwnerFrameTaskNative.complete
