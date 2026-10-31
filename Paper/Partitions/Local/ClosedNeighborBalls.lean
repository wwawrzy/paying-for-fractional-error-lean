import Paper.Partitions.Local.NeighborBalls
import Paper.Owners.Construction.PublicOwners

namespace Paper.ClosedNeighborBalls
section
variable {V : Type} [DecidableEq V]

theorem subset (N : V → Finset V) (S : Finset V) (hS : ∀ u ∈ S, N u ⊆ S)
    (v : V) (hv : v ∈ S) (r : ℕ) : NeighborBalls.ball N v r ⊆ S := by
  induction r generalizing v with
  | zero =>
    intro u hu
    have he := (NeighborBalls.mem_zero N v u).mp hu
    exact he ▸ hv
  | succ r ih =>
    intro u hu
    rcases (NeighborBalls.mem_succ N v u r).mp hu with he | ⟨w, hw, hu⟩
    · exact he ▸ hv
    · exact ih w (hS v hv hw) hu

end
variable {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D S : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D S L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D S : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D S L Q).Adj := fun _ _ => Classical.propDecidable _

theorem owner_subset (D S : Finset V) (L : ℕ) (Q : Finset D) (v : V)
    (hv : v ∈ PublicOwners.image D Q) (r : ℕ) :
    NeighborBalls.ball (fun u => (PublicOwners.graph G D S L Q).neighborFinset u) v r ⊆ PublicOwners.image D Q := by
  apply subset _ _ _ v hv r
  intro u hu w hw
  obtain ⟨d, hd, hnot⟩ := (PublicOwners.mem_image D Q u).mp hu
  let i : OwnerTasks.Low D Q := ⟨d, hnot⟩
  have hid : i.val.val = u := hd
  subst u
  rw [PublicOwners.neighbor_at G D S L Q i] at hw
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
  exact (PublicOwners.mem_image D Q j.val.val).mpr ⟨j.val, rfl, j.property⟩
end Paper.ClosedNeighborBalls
