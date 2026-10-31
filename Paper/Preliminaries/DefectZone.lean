import Paper.Preliminaries.DefectCharge

/-! Bound the actual solver region using degree-defect charges and radius two. -/
namespace Paper.DefectZone
attribute [local instance] Classical.propDecidable
open SevenFoundation
open WeightedBudget (defects auxiliary)
open SelectionGeometry SelectionSaving
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (t : ℝ) (x : V → ℝ)

/-- Every residual defect is in L, U, or is an original defect in Q. -/
theorem defects_subset :
    (ResidualDefects.localDefects G (residual G d t x) d).map
      (Function.Embedding.subtype (fun v => v ∈ (residual G d t x : Set V))) ⊆
    middle G d t x ∪ last G d t x ∪ (defects G d ∩ overlap G d t x) := by
  classical
  intro v hv
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hv
  have hqR : q.val ∈ residual G d t x := q.property
  by_cases hh : q.val ∈ high G d t x
  · have hqQ : q.val ∈ overlap G d t x := Finset.mem_inter.mpr ⟨hh, hqR⟩
    apply Finset.mem_union_right
    refine Finset.mem_inter.mpr ⟨?_, hqQ⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hregular
    change G.degree q.val = d at hregular
    have hlow := DefectCharge.overlap_degree G d t x hqQ
    have hsub : (residual G d t x).filter (G.Adj q.val) ⊆ G.neighborFinset q.val := by
      intro v hv
      exact (G.mem_neighborFinset q.val v).mpr (Finset.mem_filter.mp hv).2
    have hhigh := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree, hregular] at hhigh
    have hdeg : ((residual G d t x).filter (G.Adj q.val)).card = d := by omega
    have hbridge := InducedCounting.degree_induce_eq_inducedDegree G (residual G d t x) q
    change (G.induce (residual G d t x : Set V)).degree q =
      ((residual G d t x).filter (G.Adj q.val)).card at hbridge
    have hdef := (Finset.mem_filter.mp hq).2
    exact hdef.elim (fun hn => hn (hbridge.trans hdeg)) (fun hn => hn hregular)
  · apply Finset.mem_union_left
    by_cases hc : q.val ∈ covered G (high G d t x)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_inter.mpr ⟨hqR, hc⟩, hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hqR, hc⟩)

theorem defects_card_le (hden : MinorDensity.Bound G t) (hd : (d : ℝ) = 2 * t)
    (hx : feasible (auxiliary G d) x) :
    ((ResidualDefects.localDefects G (residual G d t x) d).card : ℝ) ≤
      t * (first G d t x).card + (t + 1) * (middle G d t x).card +
        d * slack G d t x := by
  have hcard := Finset.card_le_card (defects_subset G d t x)
  rw [Finset.card_map] at hcard
  have hu := Finset.card_union_le (middle G d t x ∪ last G d t x)
    (defects G d ∩ overlap G d t x)
  have hu' := Finset.card_union_le (middle G d t x) (last G d t x)
  have hnat : (ResidualDefects.localDefects G (residual G d t x) d).card ≤
      (middle G d t x).card + (last G d t x).card +
      (defects G d ∩ overlap G d t x).card := by omega
  have hr : ((ResidualDefects.localDefects G (residual G d t x) d).card : ℝ) ≤
      (middle G d t x).card + (last G d t x).card +
      (defects G d ∩ overlap G d t x).card := by exact_mod_cast hnat
  have hb := DefectCharge.original_defects_le G d t x hden hd
  have hU := last_card_le_slack G d t x hx
  linarith

theorem residual_card_le (hden : MinorDensity.Bound G t) (hd : (d : ℝ) = 2 * t)
    (hdpos : 1 ≤ d) (hx : feasible (auxiliary G d) x) :
    ((residual G d t x).card : ℝ) ≤ (1 + (d : ℝ) ^ 2) *
      (t * (first G d t x).card + (t + 1) * (middle G d t x).card +
        d * slack G d t x) := by
  classical
  have hedge := MinorDensity.induced_bound G hden (residual G d t x)
  have hreal : (2 : ℝ) * (G.induce (residual G d t x : Set V)).edgeFinset.card ≤
      d * (residual G d t x).card := by
    change ((G.induce (residual G d t x : Set V)).edgeFinset.card : ℝ) ≤
      t * (residual G d t x).card at hedge
    rw [hd]
    linarith
  have hnat : 2 * (G.induce (residual G d t x : Set V)).edgeFinset.card ≤
      d * (residual G d t x).card := by exact_mod_cast hreal
  have hr := ResidualDefects.residual_card_le G d t x hdpos hnat
  have hr' : ((residual G d t x).card : ℝ) ≤ (1 + (d : ℝ) ^ 2) *
      (ResidualDefects.localDefects G (residual G d t x) d).card := by exact_mod_cast hr
  exact hr'.trans (mul_le_mul_of_nonneg_left (defects_card_le G d t x hden hd hx)
    (by positivity))
end Paper.DefectZone
