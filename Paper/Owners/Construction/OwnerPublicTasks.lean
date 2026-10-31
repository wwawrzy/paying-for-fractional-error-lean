import Paper.Preliminaries.PublicPartPullback
import Paper.Averaging.Tasks.PhysicalTasks
import Paper.Owners.Construction.PublicOwners

/-! Public-ID parts describe exactly the existing original low-owner
physical task and demand sets. All subtype pullbacks are proof-only. -/
namespace Paper.OwnerPublicTasks
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]

def pull (D : Finset V) (Q : Finset D) (I : Finset V) : Finset (OwnerTasks.Low D Q) :=
  PublicPartPullback.pull (PublicOwners.embedding D Q) I

theorem mem_pull (D : Finset V) (Q : Finset D) (I : Finset V) (d : OwnerTasks.Low D Q) :
    d ∈ pull D Q I ↔ d.val.val ∈ I := PublicPartPullback.mem_pull _ I d

theorem centers (D : Finset V) (Q : Finset D) (I : Finset V) (hI : I ⊆ PublicOwners.image D Q) :
    PhysicalTasks.centers D Q (pull D Q I) = I := by
  have hr : (I : Set V) ⊆ Set.range (PublicOwners.embedding D Q) := by
    rw [PublicOwners.range_eq]
    exact hI
  have hh := PublicPartPullback.image_pull (PublicOwners.embedding D Q) I hr
  unfold PhysicalTasks.centers
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  exact hh

theorem card (D : Finset V) (Q : Finset D) (I : Finset V) (hI : I ⊆ PublicOwners.image D Q) :
    (pull D Q I).card = I.card := by
  rw [← PhysicalTasks.centers_card D Q (pull D Q I), centers D Q I hI]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem connected (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset V)
    (hI : I ⊆ PublicOwners.image D Q)
    (hc : ((PublicOwners.graph G D R L Q).induce (I : Set V)).Connected) :
    ((OwnerTasks.graph G D R L Q).induce (pull D Q I : Set _)).Connected := by
  apply PublicPartPullback.connected (PublicOwners.embedding D Q) (OwnerTasks.graph G D R L Q) I _ hc
  rw [PublicOwners.range_eq]
  exact hI

theorem mem_vertices (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset V)
    (hI : I ⊆ PublicOwners.image D Q) (v : V) :
    v ∈ PhysicalTasks.vertices G D R L Q (pull D Q I) ↔
      OwnerSupport.owner G D v ∈ I ∨ v ∉ HeavyRepair.heavy G D R L ∧
        (OwnerInteraction.actualSupport G D R L v ∩ I).Nonempty := by
  unfold PhysicalTasks.vertices
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst, centers D Q I hI]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_demands (D R : Finset V) (L : ℕ) (Q : Finset D) (I B : Finset V)
    (hI : I ⊆ PublicOwners.image D Q) (v : V) :
    v ∈ OwnerTasks.demands G D R L Q (pull D Q I) (pull D Q B) ↔
      v ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D v ∈ I ∧
        OwnerSupport.owner G D v ∉ B := by
  unfold OwnerTasks.demands
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  simp only [Finset.mem_filter, mem_pull]
  constructor
  · rintro ⟨hr, d, he, hd, hb⟩
    exact ⟨hr, he ▸ hd, he ▸ hb⟩
  · rintro ⟨hr, hi, hb⟩
    obtain ⟨d, he, hd⟩ := (PublicOwners.mem_image D Q _).mp (hI hi)
    exact ⟨hr, ⟨d, hd⟩, he, he.symm ▸ hi, he.symm ▸ hb⟩

end Paper.OwnerPublicTasks
