import Paper.Partitions.Local.PublicPartitionPullback
import Paper.Owners.Construction.OwnerPublicTasks

/-! Exact original low-owner partition attached to a public-ID partition. -/
namespace Paper.OwnerPublicPartition
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem image_range (D : Finset V) (Q : Finset D) :
    ∀ v, v ∈ PublicOwners.image D Q ↔ v ∈ Set.range (PublicOwners.embedding D Q) := by
  rw [PublicOwners.range_eq]
  exact fun _ => Iff.rfl

noncomputable def data (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (PublicOwners.graph G D R L Q) (PublicOwners.image D Q) k) :
    SmallParts.Data (OwnerTasks.graph G D R L Q) Finset.univ k :=
  PublicPartitionPullback.data (OwnerTasks.graph G D R L Q) (PublicOwners.embedding D Q)
    (PublicOwners.image D Q) k (image_range D Q) P

theorem pull_centers (D : Finset V) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q)) :
    OwnerPublicTasks.pull D Q (PhysicalTasks.centers D Q I) = I := by
  ext d
  rw [OwnerPublicTasks.mem_pull]
  unfold PhysicalTasks.centers
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst, Finset.mem_image]
  constructor
  · rintro ⟨e, he, hed⟩
    have hh : e = d := Subtype.ext (Subtype.ext hed)
    exact hh ▸ he
  · intro hd
    exact ⟨d, hd, rfl⟩

theorem public_part (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (PublicOwners.graph G D R L Q) (PublicOwners.image D Q) k)
    (I : Finset (OwnerTasks.Low D Q)) (hI : I ∈ (data G D R L Q k P).parts) :
    PhysicalTasks.centers D Q I ∈ P.parts := by
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hI
  change PhysicalTasks.centers D Q (OwnerPublicTasks.pull D Q U) ∈ P.parts
  rw [OwnerPublicTasks.centers D Q U (P.subset U hU)]
  exact hU

theorem boundary (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (PublicOwners.graph G D R L Q) (PublicOwners.image D Q) k) :
    BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (data G D R L Q k P).parts =
      OwnerPublicTasks.pull D Q (BoundaryOwners.vertices (PublicOwners.graph G D R L Q)
        (PublicOwners.image D Q) P.parts) := by
  ext d
  rw [OwnerPublicTasks.mem_pull]
  exact PublicPartitionPullback.boundary (OwnerTasks.graph G D R L Q) (PublicOwners.embedding D Q)
    (PublicOwners.image D Q) k (image_range D Q) P d

theorem boundary_card (D R : Finset V) (L : ℕ) (Q : Finset D) (k : ℕ)
    (P : SmallParts.Data (PublicOwners.graph G D R L Q) (PublicOwners.image D Q) k) :
    (BoundaryOwners.vertices (OwnerTasks.graph G D R L Q) Finset.univ (data G D R L Q k P).parts).card =
      (BoundaryOwners.vertices (PublicOwners.graph G D R L Q) (PublicOwners.image D Q) P.parts).card := by
  rw [boundary G D R L Q k P]
  exact OwnerPublicTasks.card D Q _ (BoundaryOwners.subset _ _ _)

end Paper.OwnerPublicPartition
