import Paper.Endpoints.Girth.CurrentGirthCountInput
import Paper.Endpoints.Girth.MarkedShellCount
import Paper.Endpoints.Girth.MarkedRestriction
import Paper.Endpoints.Girth.PlanarCrossingEdges

/-!
# The actual selected-vertex count on planar graphs of large girth

The contracted graph, its marked set, and every degree hypothesis come from
the existing current rounding. The incident-edge estimate uses a full
induced A∪Q∪L graph and the actual A--U bipartite crossing graph.
-/

namespace Paper.CurrentGirthCounting

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
local notation "p" => Finset.card (CurrentFaceBound.incidentMarkedEdges (G := K) A)

theorem incident_bound
    (hplanar : G.IsPlanar) (g : ℕ) (hg : 3 ≤ g)
    (ha : a = (g : ℝ) / ((g : ℝ) - 2))
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    (p : ℝ) ≤ ((g : ℝ) + 4) * (W).card +
      ((g : ℝ) + 2) * (L).card + 2 * (U).card := by
  have hm := ComponentMinor.isMinor G R W
  have hpK : (K).IsPlanar :=
    ⟨IsHMinorFree.minor hplanar.1 hm, IsHMinorFree.minor hplanar.2 hm⟩
  have hparts := CurrentGirthCountInput.minor_parts_disjoint G a d hd x hx hcap
  have hdg : (d : ℝ) = 2 * ((g : ℝ) / ((g : ℝ) - 2)) := by rw [hd, ha]
  have hcross := MarkedRestriction.crossing_bound K hpK A ((Q).image f) ((L).image f)
    hparts.1 hparts.2 (CurrentGirthStructure.contracted_independent G R W) g d hg hdg
    (CurrentGirthMinor.girth_outside_contracted G R W g hgirth)
    (CurrentGirthCountInput.minor_overlap_degree G a d hd x hx hcap)
  have hUR := CurrentCountBound.last_subset_residual G a d hd x hx hcap
  have hAU := PlanarCrossingEdges.planar_interedges_bound K hpK A ((U).image f)
    (ComponentMinor.contracted_disjoint_residual G R W U hUR)
  have hAUreal : (((K).interedges A ((U).image f)).card : ℝ) ≤
      2 * ((A).card + ((U).image f).card) := by exact_mod_cast hAU
  have hsplit : p ≤ ((K).interedges A ((Q).image f ∪ (L).image f)).card +
      ((K).interedges A ((U).image f)).card := by
    rw [CurrentGirthCountInput.incident_card_eq_residual_crossings G a d hd x hx hcap,
      CurrentGirthCountInput.minor_residual_partition G a d hd x hx hcap,
      MarkedRestriction.interedges_union_right]
    exact Finset.card_union_le _ _
  have hsplitR : (p : ℝ) ≤ ((K).interedges A ((Q).image f ∪ (L).image f)).card +
      ((K).interedges A ((U).image f)).card := by exact_mod_cast hsplit
  have hAcard : ((A).card : ℝ) ≤ (W).card := by
    exact_mod_cast ComponentMinor.contracted_card_le G R W
  have hLcard := ComponentMinor.card_image_residual G R W L
    (CurrentCountBound.middle_subset_residual G a d hd x hx hcap)
  have hUcard := ComponentMinor.card_image_residual G R W U hUR
  rw [hLcard] at hcross
  rw [hUcard] at hAUreal
  have hscaled := mul_le_mul_of_nonneg_left hAcard
    (show (0 : ℝ) ≤ (g : ℝ) + 2 by positivity)
  have hW0 : (0 : ℝ) ≤ (W).card := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ (L).card := Nat.cast_nonneg _
  nlinarith only [hcross, hAUreal, hsplitR, hscaled, hW0, hL0]

theorem overlap_bound
    (hplanar : G.IsPlanar) (g : ℕ) (hg : 3 ≤ g)
    (ha : a = (g : ℝ) / ((g : ℝ) - 2))
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    ((Q).card : ℝ) ≤ (d : ℝ) * (d + 2) * ((W).card + (L).card + (U).card) +
      (d + 2) * (((g : ℝ) - 4) / ((g : ℝ) - 2)) * p := by
  let κ : ℝ := ((g : ℝ) - 4) / ((g : ℝ) - 2)
  let B := (WeightedBudget.defects G d ∩ Q).image f
  let T := (L ∪ U).image f
  have hQR := CurrentCountBound.overlap_subset_residual G a d hd x hx hcap
  have hLR := CurrentCountBound.middle_subset_residual G a d hd x hx hcap
  have hUR := CurrentCountBound.last_subset_residual G a d hd x hx hcap
  have hTR : L ∪ U ⊆ R := Finset.union_subset hLR hUR
  have hAT : Disjoint A T := ComponentMinor.contracted_disjoint_residual G R W (L ∪ U) hTR
  have hBQ : B ⊆ (Q).image f := Finset.image_subset_image Finset.inter_subset_right
  have hQAT : Disjoint ((Q).image f) (A ∪ T) := by
    apply Finset.disjoint_union_right.mpr
    exact ⟨(ComponentMinor.contracted_disjoint_residual G R W Q hQR).symm,
      CurrentCountBound.image_disjoint_residual G a d hd x hx hcap Q (L ∪ U) hQR hTR
        (CurrentCountBound.overlap_disjoint_rest G a d hd x hx hcap)⟩
  have htouch : ∀ r ∈ (Q).image f \ B, ∃ s ∈ T ∪ B, (K).Adj r s := by
    intro r hr
    obtain ⟨s, hs, hrs⟩ :=
      CurrentGirthCountInput.minor_regular_overlap_touch_unmarked G a d hd x hx hcap r hr
    refine ⟨s, ?_, hrs⟩
    rcases Finset.mem_union.mp hs with hl | hb
    · exact Finset.mem_union_left _ ((Finset.image_subset_image Finset.subset_union_left) hl)
    · exact Finset.mem_union_right _ hb
  have hface := CurrentGirthMinor.edge_bound G R W hplanar g hg hgirth
  have hpos : (0 : ℝ) < (g : ℝ) - 2 := by
    have hgr : (3 : ℝ) ≤ g := by exact_mod_cast hg
    linarith
  have hcoef : 2 * (((g : ℝ) - 3) / ((g : ℝ) - 2)) = 1 + κ := by
    dsimp only [κ]
    field_simp [ne_of_gt hpos]
    ring
  have hdg : (d : ℝ) = 2 * ((g : ℝ) / ((g : ℝ) - 2)) := by rw [hd, ha]
  have hpd : ((∑ r ∈ A, (K).degree r) : ℝ) = (p : ℝ) := by
    exact_mod_cast (CurrentGirthStructure.contracted_incident_card_eq_degree_sum G R W).symm
  have hden : (2 : ℝ) * (K).edgeFinset.card ≤
      d * Fintype.card (ComponentMinor.retained G R W) +
        (1 + κ) * (∑ r ∈ A, (K).degree r) := by
    push_cast
    rw [hpd]
    have hh := mul_le_mul_of_nonneg_left hface (show (0 : ℝ) ≤ 2 by norm_num)
    have he : 2 * ((g : ℝ) / ((g : ℝ) - 2) *
          Fintype.card (ComponentMinor.retained G R W) +
          ((g : ℝ) - 3) / ((g : ℝ) - 2) * p) =
        d * Fintype.card (ComponentMinor.retained G R W) + (1 + κ) * p := by
      rw [hdg, ← hcoef]
      ring
    rw [he] at hh
    exact hh
  have hc := MarkedShellCount.regular_shell_count K A T ((Q).image f) B d κ
    hAT hBQ hQAT (CurrentCountBound.minor_regular_off G a d hd x hx hcap)
    (CurrentCountBound.minor_defect_degree G a d hd x hx hcap) htouch hden
  have hqcard := ComponentMinor.card_image_residual G R W Q hQR
  rw [hqcard] at hc
  push_cast at hc
  rw [hpd] at hc
  have hTcard : (A).card + T.card ≤ (W).card + (L).card + (U).card := by
    have h1 := ComponentMinor.contracted_card_le G R W
    have h2 : T.card ≤ (L ∪ U).card := Finset.card_image_le
    have h3 := Finset.card_union_le L U
    omega
  have hTcardR : ((A).card : ℝ) + T.card ≤ (W).card + (L).card + (U).card := by
    exact_mod_cast hTcard
  have hm := mul_le_mul_of_nonneg_left hTcardR
    (show (0 : ℝ) ≤ (d : ℝ) * (d + 2) by positivity)
  dsimp only [κ] at hc
  nlinarith only [hc.2, hm]

end Paper.CurrentGirthCounting

#print axioms Paper.CurrentGirthCounting.incident_bound
#print axioms Paper.CurrentGirthCounting.overlap_bound
