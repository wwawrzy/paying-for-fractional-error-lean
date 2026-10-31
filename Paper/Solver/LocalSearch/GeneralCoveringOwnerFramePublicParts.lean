import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskCandidates
import Paper.Solver.LocalSearch.GeneralCoveringTaskRandomPhysicalMarks

/-! The frame decoder and the accepted randomized physical pipeline use
the same public partition. Its actual low-owner pullback preserves every
part and every boundary flag used by a decoded physical task. -/
namespace Paper.GeneralCoveringOwnerFramePublicParts
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q).Adj :=
      fun _ _ => Classical.propDecidable _
noncomputable local instance mappedAdj {W : Type} [DecidableEq W] (J : SimpleGraph W) (e : W ↪ V) :
    DecidableRel (PublicEmbedding.graph J e).Adj := fun _ _ => Classical.propDecidable _

private theorem parts_congr (H J : SimpleGraph V) [dH : DecidableRel H.Adj] [dJ : DecidableRel J.Adj]
    (he : H = J) (S T : Finset V) (hST : S = T) (Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :
    (ActiveFiniteBitPartition.partition H Δ k hk t b n S β).parts =
      (ActiveFiniteBitPartition.partition J Δ k hk t b n T β).parts := by
  cases he
  cases hST
  have hd : dH = dJ := Subsingleton.elim _ _
  cases hd
  rfl

section Actual
variable (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ) (hk : 0 < k) (t b n : ℕ)
variable (β : V → ActiveFiniteBitPartition.Bits Δ k b n)
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
local notation "J" => graph G C D R L Q
local notation "e" => GeneralCoveringTaskPartitionMarks.lowEmbedding D Q
local notation "H" => GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L Q
local notation "U" => GeneralCoveringOwnerVirtualPrepare.image D Q
local notation "P" => ActiveFiniteBitPartition.partition H Δ k hk t b n U β
local notation "P'" => GeneralCoveringTaskRandomPhysicalMarks.publicPartition J e Δ k hk t b n β
local notation "S" => GeneralCoveringTaskRandomPhysicalMarks.partition G C D R L hk t β

theorem parts : (P).parts = (P').parts :=
  parts_congr H (PublicEmbedding.graph J e) (GeneralCoveringTaskPhysicalMarks.publicGraph_eq G C D R L Q)
    U (GeneralCoveringTaskPartitionMarks.activeImage e) (GeneralCoveringTaskPhysicalMarks.image_eq D Q)
    Δ k hk t b n β

theorem pull_part (T : Finset V) (hT : T ∈ (P).parts) : PublicPartPullback.pull e T ∈ (S).parts := by
  change PublicPartPullback.pull e T ∈ (P').parts.image (PublicPartPullback.pull e)
  exact Finset.mem_image.mpr ⟨T, (parts G C D R L Δ k hk t b n β) ▸ hT, rfl⟩

theorem image_pull (T : Finset V) (hT : T ∈ (P).parts) :
    (PublicPartPullback.pull e T).image e = T :=
  GeneralCoveringTaskPartitionMarks.image_part J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e) P' T ((parts G C D R L Δ k hk t b n β) ▸ hT)

theorem image_part (T : Finset (Low D Q)) (hT : T ∈ (S).parts) : T.image e ∈ (P).parts := by
  change T ∈ (P').parts.image (PublicPartPullback.pull e) at hT
  obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hT
  have hZ' : Z ∈ (P).parts := (parts G C D R L Δ k hk t b n β).symm ▸ hZ
  rw [image_pull G C D R L Δ k hk t b n β Z hZ']
  exact hZ'

theorem pull_image (T : Finset (Low D Q)) : PublicPartPullback.pull e (T.image e) = T := by
  ext i
  rw [PublicPartPullback.mem_pull, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (e).injective he ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

noncomputable def equiv : {T : Finset V // T ∈ (P).parts} ≃
    {T : Finset (Low D Q) // T ∈ (S).parts} where
  toFun T := ⟨PublicPartPullback.pull e T.val, pull_part G C D R L Δ k hk t b n β T.val T.property⟩
  invFun T := ⟨T.val.image e, image_part G C D R L Δ k hk t b n β T.val T.property⟩
  left_inv T := Subtype.ext (image_pull G C D R L Δ k hk t b n β T.val T.property)
  right_inv T := Subtype.ext (pull_image G C D R L Δ T.val)

theorem boundary (i : Low D Q) :
    i ∈ BoundaryOwners.vertices J Finset.univ (S).parts ↔ e i ∈ BoundaryOwners.vertices H U (P).parts := by
  have hb := PublicPartitionPullback.boundary J e (GeneralCoveringTaskPartitionMarks.activeImage e) k
    (GeneralCoveringTaskPartitionMarks.activeImage_iff e) P' i
  change i ∈ BoundaryOwners.vertices J Finset.univ (S).parts ↔ _ at hb
  rw [← parts G C D R L Δ k hk t b n β,
    ← GeneralCoveringTaskPhysicalMarks.publicGraph_eq G C D R L Q,
    ← GeneralCoveringTaskPhysicalMarks.image_eq D Q] at hb
  exact hb

end Actual
end Paper.GeneralCoveringOwnerFramePublicParts

#print axioms Paper.GeneralCoveringOwnerFramePublicParts.parts
#print axioms Paper.GeneralCoveringOwnerFramePublicParts.pull_part
#print axioms Paper.GeneralCoveringOwnerFramePublicParts.image_pull
#print axioms Paper.GeneralCoveringOwnerFramePublicParts.boundary
#print axioms Paper.GeneralCoveringOwnerFramePublicParts.image_part
#print axioms Paper.GeneralCoveringOwnerFramePublicParts.pull_image
#print axioms Paper.GeneralCoveringOwnerFramePublicParts.equiv
