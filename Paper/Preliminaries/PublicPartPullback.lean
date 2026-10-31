import Paper.Preliminaries.PublicEmbedding
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Proof-only pullback of finite public-ID regions through an embedding.
The actual programs keep public IDs and never call the inverse mapping. -/
namespace Paper.PublicPartPullback
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (e : W ↪ V)

def pull (I : Finset V) : Finset W := Finset.univ.filter (fun w => e w ∈ I)

theorem mem_pull (I : Finset V) (w : W) : w ∈ pull e I ↔ e w ∈ I := by
  simp only [pull, Finset.mem_filter, Finset.mem_univ, true_and]

theorem image_pull (I : Finset V) (hI : (I : Set V) ⊆ Set.range e) : (pull e I).image e = I := by
  ext v
  rw [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_pull e I w).mp hw
  · intro hv
    obtain ⟨w, he⟩ := hI hv
    exact ⟨w, (mem_pull e I w).mpr (he.symm ▸ hv), he⟩

theorem card_pull (I : Finset V) (hI : (I : Set V) ⊆ Set.range e) : (pull e I).card = I.card := by
  calc
    _ = ((pull e I).image e).card := (Finset.card_image_of_injective _ e.injective).symm
    _ = I.card := congrArg Finset.card (image_pull e I hI)

variable (J : SimpleGraph W) [DecidableRel J.Adj]

noncomputable local instance mappedAdj : DecidableRel (PublicEmbedding.graph J e).Adj :=
  fun _ _ => Classical.propDecidable _

noncomputable def inducedIso (I : Finset V) (hI : (I : Set V) ⊆ Set.range e) :
    (J.induce (pull e I : Set W)) ≃g ((PublicEmbedding.graph J e).induce (I : Set V)) where
  toEquiv := Equiv.ofBijective (fun w => ⟨e w.val, (mem_pull e I w.val).mp w.property⟩)
    ⟨fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h)), by
      intro v
      obtain ⟨w, he⟩ := hI v.property
      exact ⟨⟨w, (mem_pull e I w).mpr (he.symm ▸ v.property)⟩, Subtype.ext he⟩⟩
  map_rel_iff' := by
    intro u v
    change (J.map e).Adj (e u.val) (e v.val) ↔ J.Adj u.val v.val
    exact SimpleGraph.map_adj_apply

theorem connected (I : Finset V) (hI : (I : Set V) ⊆ Set.range e)
    (hc : ((PublicEmbedding.graph J e).induce (I : Set V)).Connected) :
    (J.induce (pull e I : Set W)).Connected :=
  (inducedIso e J I hI).connected_iff.mpr hc

end Paper.PublicPartPullback
