import Paper.Preliminaries.PublicEmbedding
import Paper.Owners.Construction.OwnerTasks
import Paper.Preliminaries.HighDegreeCut

/-! The low owner graph on public physical IDs. Low roots are embedded
injectively; every other physical identifier is an isolated virtual node. -/
namespace Paper.PublicOwners
variable {V : Type} [Fintype V] [LinearOrder V]

def embedding (D : Finset V) (Q : Finset D) : OwnerTasks.Low D Q ↪ V :=
  ⟨fun u => u.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩

noncomputable def image (D : Finset V) (Q : Finset D) : Finset V :=
  Finset.univ.image (embedding D Q)

theorem mem_image (D : Finset V) (Q : Finset D) (v : V) :
    v ∈ image D Q ↔ ∃ d : D, d.val = v ∧ d ∉ Q := by
  simp only [image, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u.val, hu, u.property⟩
  · rintro ⟨d, hd, hlow⟩
    exact ⟨⟨d, hlow⟩, hd⟩

theorem range_eq (D : Finset V) (Q : Finset D) : Set.range (embedding D Q) = (image D Q : Set V) := by
  ext v
  simp only [Set.mem_range, Finset.mem_coe, image, Finset.mem_image, Finset.mem_univ, true_and]

theorem image_card (D : Finset V) (Q : Finset D) : (image D Q).card = Fintype.card (OwnerTasks.Low D Q) := by
  rw [image, Finset.card_image_of_injective _ (embedding D Q).injective, Finset.card_univ]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def graph (D R : Finset V) (L : ℕ) (Q : Finset D) : SimpleGraph V :=
  PublicEmbedding.graph (OwnerTasks.graph G D R L Q) (embedding D Q)

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem neighbor_at (D R : Finset V) (L : ℕ) (Q : Finset D) (i : OwnerTasks.Low D Q) :
    (graph G D R L Q).neighborFinset i.val.val =
      ((OwnerTasks.graph G D R L Q).neighborFinset i).image (embedding D Q) :=
  PublicEmbedding.neighbor_at _ (embedding D Q) i

theorem neighbor_outside (D R : Finset V) (L : ℕ) (Q : Finset D) (v : V) (hv : v ∉ image D Q) :
    (graph G D R L Q).neighborFinset v = ∅ := by
  apply PublicEmbedding.neighbor_outside _ (embedding D Q) v
  rwa [range_eq]

theorem neighbor_filter (D R : Finset V) (L : ℕ) (Q : Finset D) (i : OwnerTasks.Low D Q) :
    (graph G D R L Q).neighborFinset i.val.val =
      (((OwnerInteraction.graph G D R L).neighborFinset i.val).filter (fun j => j ∉ Q)).image Subtype.val := by
  rw [neighbor_at]
  ext v
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j.val, ⟨(SimpleGraph.mem_neighborFinset (OwnerInteraction.graph G D R L) i.val j.val).mpr
      ((SimpleGraph.mem_neighborFinset (OwnerTasks.graph G D R L Q) i j).mp hj), j.property⟩, he⟩
  · rintro ⟨j, ⟨hj, hlow⟩, he⟩
    exact ⟨⟨j, hlow⟩, (SimpleGraph.mem_neighborFinset (OwnerTasks.graph G D R L Q) i ⟨j, hlow⟩).mpr
      ((SimpleGraph.mem_neighborFinset (OwnerInteraction.graph G D R L) i.val j).mp hj), he⟩

theorem degree_bound (D R : Finset V) (L Δ : ℕ) :
    ∀ v, (graph G D R L (HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ)).degree v ≤ Δ := by
  apply PublicEmbedding.degree_bound _ (embedding D _) Δ
  intro i
  exact HighDegreeCut.degree_bound (OwnerInteraction.graph G D R L) Δ i

noncomputable def imageIso (D R : Finset V) (L : ℕ) (Q : Finset D) :
    OwnerTasks.graph G D R L Q ≃g (graph G D R L Q).induce (image D Q : Set V) := by
  have he := PublicEmbedding.imageIso (OwnerTasks.graph G D R L Q) (embedding D Q)
  rw [range_eq] at he
  exact he
end Paper.PublicOwners
