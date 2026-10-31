import Paper.Preliminaries.PublicPartPullback

namespace Paper.PublicInducedEmbedding
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (e : W ↪ V)

def embedding (I : Finset V) : ↥(PublicPartPullback.pull e I : Set W) ↪ ↥(I : Set V) where
  toFun w := ⟨e w.val, (PublicPartPullback.mem_pull e I w.val).mp w.property⟩
  inj' := fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))

theorem card (I : Finset V) : (PublicPartPullback.pull e I).card ≤ I.card := by
  have hh := Fintype.card_le_of_injective (embedding e I) (embedding e I).injective
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh

variable (J : SimpleGraph W) [DecidableRel J.Adj]

theorem graph_eq (I : Finset V) :
    PublicEmbedding.graph (J.induce (PublicPartPullback.pull e I : Set W)) (embedding e I) =
      (PublicEmbedding.graph J e).induce (I : Set V) := by
  ext v w
  change (PublicEmbedding.graph (J.induce (PublicPartPullback.pull e I : Set W)) (embedding e I)).Adj v w ↔
    (PublicEmbedding.graph J e).Adj v.val w.val
  rw [PublicEmbedding.adj_iff, PublicEmbedding.adj_iff]
  constructor
  · rintro ⟨x, y, ha, hx, hy⟩
    exact ⟨x.val, y.val, ha, congrArg Subtype.val hx, congrArg Subtype.val hy⟩
  · rintro ⟨x, y, ha, hx, hy⟩
    let x' : ↥(PublicPartPullback.pull e I : Set W) :=
      ⟨x, (PublicPartPullback.mem_pull e I x).mpr (hx.symm ▸ v.property)⟩
    let y' : ↥(PublicPartPullback.pull e I : Set W) :=
      ⟨y, (PublicPartPullback.mem_pull e I y).mpr (hy.symm ▸ w.property)⟩
    exact ⟨x', y', ha, Subtype.ext hx, Subtype.ext hy⟩

end Paper.PublicInducedEmbedding
