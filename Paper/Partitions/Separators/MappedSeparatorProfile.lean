import Paper.Partitions.Separators.EmbeddedSeparator
import Paper.Preliminaries.PublicInducedEmbedding
import Paper.Partitions.Separators.SeparatorProfile

/-! Sublinear half-balanced separators survive embedding and adding
isolated public IDs. The harmless extra constant handles singleton regions. -/
namespace Paper.MappedSeparatorProfile
attribute [local instance] Classical.propDecidable
open DeletionComponents
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)

noncomputable local instance mappedAdj : DecidableRel (PublicEmbedding.graph J e).Adj :=
  fun _ _ => Classical.propDecidable _

theorem bound {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound J C) :
    SeparatorProfile.Bound (PublicEmbedding.graph J e) (C + 1) := by
  intro I
  by_cases hsmall : I.card ≤ 1
  · refine ⟨Finset.univ, ?_, ?_⟩
    · simp only [Finset.card_univ, Finset.coe_sort_coe, Fintype.card_coe]
      have hn : I.card = 0 ∨ I.card = 1 := by omega
      rcases hn with hn | hn
      · simp only [hn, Nat.cast_zero, Real.sqrt_zero, mul_zero, le_refl]
      · simp only [hn, Nat.cast_one, Real.sqrt_one, mul_one]
        linarith
    · exact ConnectedSeparator.to_components _ _ _ (ConnectedSeparator.all_deleted _ _)
  · let Y := PublicPartPullback.pull e I
    obtain ⟨X, hX, hbalanced⟩ := hprofile Y
    let f := PublicInducedEmbedding.embedding e I
    have hcard : Y.card ≤ I.card := PublicInducedEmbedding.card e I
    have hreal : (Y.card : ℝ) ≤ I.card := by exact_mod_cast hcard
    have hn : (2 : ℝ) ≤ I.card := by exact_mod_cast (show 2 ≤ I.card by omega)
    have hgood := ConnectedSeparator.of_components (J.induce (Y : Set W)) X ((Y.card : ℝ) / 2) hbalanced
    have hlift := EmbeddedSeparator.good (J.induce (Y : Set W)) f X ((Y.card : ℝ) / 2) ((I.card : ℝ) / 2)
      (by linarith) (by linarith) hgood
    refine ⟨X.image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ f.injective]
      calc
        _ ≤ C * Real.sqrt Y.card := hX
        _ ≤ C * Real.sqrt I.card := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hreal) hC
        _ ≤ (C + 1) * Real.sqrt I.card := by nlinarith [Real.sqrt_nonneg (I.card : ℝ)]
    · have he := PublicInducedEmbedding.graph_eq e J I
      have hh : ConnectedSeparator.Good ((PublicEmbedding.graph J e).induce (I : Set V))
          (X.image f) ((I.card : ℝ) / 2) := by
        rw [← he]
        exact hlift
      exact ConnectedSeparator.to_components _ _ _ hh

end Paper.MappedSeparatorProfile
