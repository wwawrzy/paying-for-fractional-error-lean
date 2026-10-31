import Paper.Endpoints.Girth.CurrentGirthStructure
import Paper.Endpoints.Rounding.CurrentCountBound

/-! # Actual current rounding inputs for the girth selected-vertex count -/

namespace Paper.CurrentGirthCountInput

open SimpleGraph SevenFoundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (d : ℕ)
  (hd : (d : ℝ) = 2 * a) (x : V → ℝ)
  (hx : feasible (CurrentBudget.auxiliary G d) x)
  (hcap : ∀ v ∈ CurrentBudget.candidates G d, x v ≤ 1)

local notation "I" => CurrentCounting.input G a d hd x hx hcap
local notation "W" => CurrentRounding.first G a I
local notation "R" => CurrentRounding.residual G a I
local notation "Q" => CurrentRounding.overlap G a I
local notation "L" => CurrentRounding.middle G a I
local notation "U" => CurrentRounding.last G a I
local notation "f" => ComponentMinor.vertex G R W
local notation "K" => ComponentMinor.graph G R W
local notation "A" => ComponentMinor.contracted G R W

/-- The high-vertex condition supplies at least d neighbors in precisely
the retained Q∪L, rather than in the entire contracted graph. -/
theorem minor_overlap_degree
    (r : ComponentMinor.retained G R W) (hr : r ∈ (Q).image f) :
    d ≤ (K).inducedDegree r ((Q).image f ∪ (L).image f) := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  have hqR := CurrentCountBound.overlap_subset_residual G a d hd x hx hcap hq
  let S := (R).filter (G.Adj q)
  have hsR : S ⊆ R := Finset.filter_subset _ _
  have hcard := ComponentMinor.card_image_residual G R W S hsR
  have hsub : S.image f ⊆ ((Q).image f ∪ (L).image f).filter ((K).Adj (f q)) := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hvR := (Finset.mem_filter.mp hv).1
    have hqv := (Finset.mem_filter.mp hv).2
    have hvQL := CurrentCounting.overlap_neighbor_support G a d hd x hx hcap hq hvR hqv
    refine Finset.mem_filter.mpr ⟨?_, ComponentMinor.residual_edge G R W hqR hvR hqv⟩
    rcases Finset.mem_union.mp hvQL with hvQ | hvL
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hvQ, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hvL, rfl⟩)
  have hsmall : S.card ≤
      (((Q).image f ∪ (L).image f).filter ((K).Adj (f q))).card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  exact (CurrentCounting.overlap_degree G a d hd x hx hcap hq).trans hsmall

/-- The actual Q and L images are disjoint and both avoid the contracted set. -/
theorem minor_parts_disjoint :
    Disjoint A ((Q).image f ∪ (L).image f) ∧
      Disjoint ((Q).image f) ((L).image f) := by
  have hQR := CurrentCountBound.overlap_subset_residual G a d hd x hx hcap
  have hLR := CurrentCountBound.middle_subset_residual G a d hd x hx hcap
  refine ⟨Finset.disjoint_union_right.mpr
    ⟨ComponentMinor.contracted_disjoint_residual G R W Q hQR,
      ComponentMinor.contracted_disjoint_residual G R W L hLR⟩, ?_⟩
  apply CurrentCountBound.image_disjoint_residual G a d hd x hx hcap Q L hQR hLR
  exact (CurrentCountBound.overlap_disjoint_rest G a d hd x hx hcap).mono_right
    Finset.subset_union_left

/-- Every incident edge is counted once among the actual A--R crossings. -/
theorem incident_card_eq_residual_crossings :
    (CurrentFaceBound.incidentMarkedEdges (G := K) A).card =
      ((K).interedges A ((R).image f)).card := by
  rw [CurrentGirthStructure.contracted_incident_card_eq_degree_sum G R W,
    Incidence.card_interedges_eq_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have he : (K).neighborFinset r = ((R).image f).filter ((K).Adj r) := by
    ext s
    simp only [mem_neighborFinset, Finset.mem_filter]
    constructor
    · intro hrs
      have hsR := CurrentGirthStructure.contracted_neighbor_residual G R W r s hr hrs
      have hs : f s.val = s := Subtype.ext (ComponentMinor.label_residual G R W hsR)
      exact ⟨Finset.mem_image.mpr ⟨s.val, hsR, hs⟩, hrs⟩
    · exact fun h => h.2
  rw [← card_neighborFinset_eq_degree, he]

theorem minor_residual_partition :
    (R).image f = ((Q).image f ∪ (L).image f) ∪ (U).image f := by
  have h := congrArg (fun S : Finset V => S.image f)
    (CurrentCountBound.residual_partition G a d hd x hx hcap)
  simpa only [Finset.image_union] using h

/-- The touching vertex for Q\B is retained in L∪B, so its degree charge
does not go to a contracted vertex. -/
theorem minor_regular_overlap_touch_unmarked :
    ∀ r ∈ (Q).image f \ (WeightedBudget.defects G d ∩ Q).image f,
      ∃ s ∈ (L).image f ∪ (WeightedBudget.defects G d ∩ Q).image f,
        (K).Adj r s := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hr).1
  have hqR := CurrentCountBound.overlap_subset_residual G a d hd x hx hcap hq
  have hdeg : G.degree q = d := by
    by_contra hne
    have hqB : q ∈ WeightedBudget.defects G d := by simp [WeightedBudget.defects, hne]
    exact (Finset.mem_sdiff.mp hr).2
      (Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hqB, hq⟩, rfl⟩)
  obtain ⟨v, hv, hqv⟩ :=
    CurrentCounting.regular_overlap_touches_defect G a d hd x hx hcap hq hdeg
  have hvR : v ∈ R := by
    rcases Finset.mem_union.mp hv with hb | hl
    · exact CurrentCountBound.overlap_subset_residual G a d hd x hx hcap
        (Finset.mem_inter.mp hb).2
    · exact CurrentCountBound.middle_subset_residual G a d hd x hx hcap hl
  refine ⟨f v, ?_, ComponentMinor.residual_edge G R W hqR hvR hqv⟩
  rcases Finset.mem_union.mp hv with hb | hl
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hb, rfl⟩)
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hl, rfl⟩)

end Paper.CurrentGirthCountInput

#print axioms Paper.CurrentGirthCountInput.minor_overlap_degree
#print axioms Paper.CurrentGirthCountInput.minor_parts_disjoint
#print axioms Paper.CurrentGirthCountInput.incident_card_eq_residual_crossings
#print axioms Paper.CurrentGirthCountInput.minor_residual_partition
#print axioms Paper.CurrentGirthCountInput.minor_regular_overlap_touch_unmarked
