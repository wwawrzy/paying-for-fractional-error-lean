import Paper.Partitions.Separators.ConnectedSeparator
import Paper.Preliminaries.PublicPartPullback

/-! Lift a deletion separator through an embedding and add isolated IDs.
Every connected region is either represented or an isolated singleton. -/
namespace Paper.EmbeddedSeparator
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)

noncomputable local instance mappedAdj : DecidableRel (PublicEmbedding.graph J e).Adj :=
  fun _ _ => Classical.propDecidable _

theorem good (X : Finset W) (b c : ℝ) (hbc : b ≤ c) (hone : 1 ≤ c)
    (h : ConnectedSeparator.Good J X b) :
    ConnectedSeparator.Good (PublicEmbedding.graph J e) (X.image e) c := by
  intro S hc hd
  by_cases hs : (S : Set V) ⊆ Set.range e
  · have hp := PublicPartPullback.connected e J S hs hc
    have hdis : Disjoint (PublicPartPullback.pull e S) X := by
      apply Finset.disjoint_left.mpr
      intro w hw hx
      exact Finset.disjoint_left.mp hd ((PublicPartPullback.mem_pull e S w).mp hw)
        (Finset.mem_image.mpr ⟨w, hx, rfl⟩)
    have hh := h _ hp hdis
    rw [PublicPartPullback.card_pull e S hs] at hh
    exact hh.trans hbc
  · obtain ⟨v, hv, hn⟩ : ∃ v ∈ S, v ∉ Set.range e := by
      classical
      exact Set.not_subset.mp hs
    have hcard := ConnectedSeparator.isolated_card (PublicEmbedding.graph J e) S hc v hv
      (PublicEmbedding.neighbor_outside J e v hn)
    exact (show (S.card : ℝ) ≤ 1 by exact_mod_cast hcard).trans hone

end Paper.EmbeddedSeparator
