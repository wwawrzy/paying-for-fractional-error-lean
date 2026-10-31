import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskRuntime

/-! Candidate masks interpreted under one actual public coin assignment.
Valid candidates have a unique minimum anchor and canonical subset code.
Their native partition membership is proved from the actual frame run. -/
namespace Paper.GeneralCoveringOwnerFrameTaskCandidates
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open GeneralCoveringOwnerFrameTaskData GeneralCoveringOwnerFrameTaskInputs
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

@[irreducible] noncomputable def candidate {ids : ℕ} (I : BitCode V ids) (C : V → Finset V) (D R : Finset V)
    (L Δ k t b n : ℕ) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (a : V) (mask : Fin (partSlots Δ k) → Bool) : GeneralCoveringOwnerFrameTaskData.Task V :=
  GeneralCoveringOwnerFrameTaskMean.decoded I Δ k t b n
    (GeneralCoveringOwnerFrameFractionalMean.canonical G C D R L Δ k n a) a mask
    (GeneralCoveringOwnerFrameTaskMean.restrict Δ k b n
      (GeneralCoveringOwnerFrameFractionalMean.canonical G C D R L Δ k n a) β)

noncomputable def partMask (C : V → Finset V) (D R : Finset V) (L Δ k n : ℕ) (a : V) (T : Finset V) :
    Fin (partSlots Δ k) → Bool :=
  FiniteSubsetCode.encode ((NeighborBalls.ball (FrameInterpreter.neighbors
    (GeneralCoveringOwnerFrameFractionalMean.canonical G C D R L Δ k n a)) a k).sort (· ≤ ·))
    (partSlots Δ k) T

theorem minimum {ids : ℕ} (I : BitCode V ids) (C : V → Finset V) (D R : Finset V)
    (L Δ k t b n : ℕ) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (a : V) (mask : Fin (partSlots Δ k) → Bool)
    (hv : (candidate G I C D R L Δ k t b n β a mask).valid = true) :
    MaskedMinimum.minimum (candidate G I C D R L Δ k t b n β a mask).owners = some a := by
  simp only [candidate, GeneralCoveringOwnerFrameTaskMean.decoded, compute,
    mask_encode, decide_eq_true_eq] at hv
  simpa only [candidate, GeneralCoveringOwnerFrameTaskMean.decoded, compute, mask_encode] using hv.2.2.2.1

theorem canonical_mask {ids : ℕ} (I : BitCode V ids) (C : V → Finset V) (D R : Finset V)
    (L Δ k t b n : ℕ) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (a : V) (mask : Fin (partSlots Δ k) → Bool)
    (hv : (candidate G I C D R L Δ k t b n β a mask).valid = true) :
    mask = FiniteSubsetCode.encode
      ((NeighborBalls.ball (FrameInterpreter.neighbors
        (GeneralCoveringOwnerFrameFractionalMean.canonical G C D R L Δ k n a)) a k).sort (· ≤ ·))
      (partSlots Δ k) (candidate G I C D R L Δ k t b n β a mask).owners := by
  simp only [candidate, GeneralCoveringOwnerFrameTaskMean.decoded, compute,
    mask_encode, decide_eq_true_eq] at hv
  simpa only [candidate, GeneralCoveringOwnerFrameTaskMean.decoded, compute, mask_encode] using hv.2.1

theorem injective {ids : ℕ} (I : BitCode V ids) (C : V → Finset V) (D R : Finset V)
    (L Δ k t b n : ℕ) (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
    (a a' : V) (mask mask' : Fin (partSlots Δ k) → Bool)
    (hv : (candidate G I C D R L Δ k t b n β a mask).valid = true)
    (hv' : (candidate G I C D R L Δ k t b n β a' mask').valid = true)
    (he : (candidate G I C D R L Δ k t b n β a mask).owners =
      (candidate G I C D R L Δ k t b n β a' mask').owners) : (a, mask) = (a', mask') := by
  have ha : a = a' := Option.some.inj
    ((minimum G I C D R L Δ k t b n β a mask hv).symm.trans
      ((congrArg MaskedMinimum.minimum he).trans (minimum G I C D R L Δ k t b n β a' mask' hv')))
  subst a'
  have hm : mask = mask' := (canonical_mask G I C D R L Δ k t b n β a mask hv).trans
    ((congrArg (FiniteSubsetCode.encode _ (partSlots Δ k)) he).trans
      (canonical_mask G I C D R L Δ k t b n β a mask' hv').symm)
  exact congrArg (fun z => (a, z)) hm

section Original
variable {ids B : ℕ} (I : BitCode V ids) (C targets : V → Finset V) (D R : Finset V)
variable (L Δ k t b n : ℕ) (hk : 0 < k) (ht : 0 < t)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u)
variable (hlocal : ∀ u ∈ R, C u ⊆ closed G u) (s : V → Input V B)
variable (hD : ∀ v, (s v).1.center = decide (v ∈ D))
variable (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
variable (hC : ∀ v, (s v).1.candidates = C v)
variable (hTargets : ∀ v, (s v).1.targets = targets v)
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "J" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q
include ht hinc hlocal hD hR hC hTargets

theorem sound (β : V → ActiveFiniteBitPartition.Bits Δ k b n) (v a : V)
    (ha : a ∈ (frames G I L Δ k n s v).anchors) (mask : Fin (partSlots Δ k) → Bool)
    (hv : (candidate G I C D R L Δ k t b n β a mask).valid = true) :
    let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
    let d := candidate G I C D R L Δ k t b n β a mask
    d.owners ∈ P.parts ∧ a ∈ d.owners ∧ d.owners.card ≤ k ∧
      ((J).induce (d.owners : Set V)).Connected ∧
      ∀ u ∈ d.owners, d.boundary u = decide (u ∈ BoundaryOwners.vertices J U P.parts) := by
  let xs := GeneralCoveringOwnerRoleFrames.canonical G I L Δ (outerRadius k n) (frameRadius k n)
    (fun u => (s u).1) v a
  have he : xs = GeneralCoveringOwnerFrameFractionalMean.canonical G C D R L Δ k n a :=
    GeneralCoveringOwnerRoleFrames.canonical_eq G C targets D R L Δ (outerRadius k n) k (frameRadius k n)
      hinc hlocal (fun u => (s u).1) hD hR hC hTargets I (Nat.le_refl _) v a ha
  dsimp only [xs] at he
  have hcap := GeneralCoveringOwnerFrameTaskNative.frame_capacity G C targets D R L Δ k n
    hinc hlocal (fun u => (s u).1) hD hR hC hTargets I v a ha
  let i := encode Δ k b n mask (GeneralCoveringOwnerFrameTaskMean.restrict Δ k b n xs β)
  have hcoins : ∀ j, coins Δ k b n i
      (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) hcap j) =
        β ((GeneralCoveringOwnerFramePartition.addresses xs).get j) := by
    intro j
    simp only [i, coins_encode]
    exact GeneralCoveringOwnerFrameTaskMean.restrict_slot Δ k b n xs β hcap j
  have hc : compute I Δ k t b n a i xs = candidate G I C D R L Δ k t b n β a mask := by
    unfold candidate GeneralCoveringOwnerFrameTaskMean.decoded
    exact congrArg (fun ys => compute I Δ k t b n a
      (encode Δ k b n mask (GeneralCoveringOwnerFrameTaskMean.restrict Δ k b n ys β)) ys) he
  dsimp only [xs] at hc
  have hv' : (compute I Δ k t b n a i xs).valid = true :=
    (congrArg GeneralCoveringOwnerFrameTaskData.Task.valid hc).trans hv
  have hs := GeneralCoveringOwnerFrameTaskNative.sound G C targets D R L Δ k t b n
    hinc hlocal (fun u => (s u).1) hD hR hC hTargets I hk ht v a ha i β hcoins hv'
  let P := ActiveFiniteBitPartition.partition J Δ k hk t b n U β
  let pred : GeneralCoveringOwnerFrameTaskData.Task V → Prop := fun d =>
    d.owners ∈ P.parts ∧ a ∈ d.owners ∧ d.owners.card ≤ k ∧
      ((J).induce (d.owners : Set V)).Connected ∧
      ∀ u ∈ d.owners, d.boundary u = decide (u ∈ BoundaryOwners.vertices J U P.parts)
  exact Eq.mp (congrArg pred hc) hs

theorem complete (β : V → ActiveFiniteBitPartition.Bits Δ k b n) (v a : V)
    (ha : a ∈ (frames G I L Δ k n s v).anchors) (T : Finset V)
    (hT : T ∈ (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts)
    (hmin : MaskedMinimum.minimum T = some a) :
    let d := candidate G I C D R L Δ k t b n β a (partMask G C D R L Δ k n a T)
    d.owners = T ∧ d.valid = true := by
  let xs := GeneralCoveringOwnerRoleFrames.canonical G I L Δ (outerRadius k n) (frameRadius k n)
    (fun u => (s u).1) v a
  have he : xs = GeneralCoveringOwnerFrameFractionalMean.canonical G C D R L Δ k n a :=
    GeneralCoveringOwnerRoleFrames.canonical_eq G C targets D R L Δ (outerRadius k n) k (frameRadius k n)
      hinc hlocal (fun u => (s u).1) hD hR hC hTargets I (Nat.le_refl _) v a ha
  dsimp only [xs] at he
  have hcap := GeneralCoveringOwnerFrameTaskNative.frame_capacity G C targets D R L Δ k n
    hinc hlocal (fun u => (s u).1) hD hR hC hTargets I v a ha
  let mask := partMask G C D R L Δ k n a T
  let i := encode Δ k b n mask (GeneralCoveringOwnerFrameTaskMean.restrict Δ k b n xs β)
  have hcoins : ∀ j, coins Δ k b n i
      (LocalSeedRecords.slot (GeneralCoveringOwnerFramePartition.addresses xs) hcap j) =
        β ((GeneralCoveringOwnerFramePartition.addresses xs).get j) := by
    intro j
    simp only [i, coins_encode]
    exact GeneralCoveringOwnerFrameTaskMean.restrict_slot Δ k b n xs β hcap j
  have hmask : OwnerRoleMetadata.mask (partSlots Δ k) (2 ^ b) n (frameSlots Δ k n) i =
      FiniteSubsetCode.encode ((NeighborBalls.ball (FrameInterpreter.neighbors xs) a k).sort (· ≤ ·))
        (partSlots Δ k) T := by
    rw [mask_encode]
    exact congrArg (fun ys => FiniteSubsetCode.encode
      ((NeighborBalls.ball (FrameInterpreter.neighbors ys) a k).sort (· ≤ ·)) (partSlots Δ k) T) he.symm
  have hs := GeneralCoveringOwnerFrameTaskNative.complete G C targets D R L Δ k t b n
    hinc hlocal (fun u => (s u).1) hD hR hC hTargets I hk ht v a ha i β hcoins T hT hmin hmask
  simpa only [candidate, GeneralCoveringOwnerFrameTaskMean.decoded, i, mask, xs, he] using hs

noncomputable def equiv (β : V → ActiveFiniteBitPartition.Bits Δ k b n) (v : V) :
    {p : V × (Fin (partSlots Δ k) → Bool) // p.1 ∈ (frames G I L Δ k n s v).anchors ∧
      (candidate G I C D R L Δ k t b n β p.1 p.2).valid = true} ≃
    {T : Finset V // T ∈ (ActiveFiniteBitPartition.partition J Δ k hk t b n U β).parts ∧
      ∃ a ∈ (frames G I L Δ k n s v).anchors, MaskedMinimum.minimum T = some a} :=
  Equiv.ofBijective (fun p =>
    ⟨(candidate G I C D R L Δ k t b n β p.val.1 p.val.2).owners,
      (sound G I C targets D R L Δ k t b n hk ht hinc hlocal s hD hR hC hTargets
        β v p.val.1 p.property.1 p.val.2 p.property.2).1,
      p.val.1, p.property.1, minimum G I C D R L Δ k t b n β p.val.1 p.val.2 p.property.2⟩) ⟨by
      intro p q he
      apply Subtype.ext
      exact injective G I C D R L Δ k t b n β p.val.1 q.val.1 p.val.2 q.val.2
        p.property.2 q.property.2 (congrArg Subtype.val he), by
      intro T
      obtain ⟨a, ha, hmin⟩ := T.property.2
      have hd := complete G I C targets D R L Δ k t b n hk ht hinc hlocal s hD hR hC hTargets
        β v a ha T.val T.property.1 hmin
      exact ⟨⟨(a, partMask G C D R L Δ k n a T.val), ha, hd.2⟩, Subtype.ext hd.1⟩⟩

end Original

end Paper.GeneralCoveringOwnerFrameTaskCandidates

#print axioms Paper.GeneralCoveringOwnerFrameTaskCandidates.sound
#print axioms Paper.GeneralCoveringOwnerFrameTaskCandidates.minimum
#print axioms Paper.GeneralCoveringOwnerFrameTaskCandidates.canonical_mask
#print axioms Paper.GeneralCoveringOwnerFrameTaskCandidates.injective
#print axioms Paper.GeneralCoveringOwnerFrameTaskCandidates.complete
#print axioms Paper.GeneralCoveringOwnerFrameTaskCandidates.equiv
