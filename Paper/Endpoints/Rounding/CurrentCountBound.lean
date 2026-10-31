import Paper.Endpoints.Rounding.CurrentCounting
import Paper.Endpoints.Rounding.ComponentMinor
import Paper.Endpoints.Rounding.Slack

/-!
The full current `simp:endpoint:count`. The component minor and every
degree premise of its sharp count are instantiated for the actual current
rounding sets. No overlap-cardinality, minor-model or degree-sum conclusion
is assumed. The resulting count also certifies the current integer-case
slack 1/(d*(d+1)^2).
-/

namespace Paper.CurrentCountBound

attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
open scoped BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ) (d : ℕ)
variable (hd : (d : ℝ) = 2 * a) (x : V → ℝ)
variable (hx : feasible (CurrentBudget.auxiliary G d) x)
variable (hcap : ∀ v ∈ CurrentBudget.candidates G d, x v ≤ 1)

local notation "I" => CurrentCounting.input G a d hd x hx hcap
local notation "W" => CurrentRounding.first G a I
local notation "R" => CurrentRounding.residual G a I
local notation "Q" => CurrentRounding.overlap G a I
local notation "L" => CurrentRounding.middle G a I
local notation "U" => CurrentRounding.last G a I
local notation "B" => WeightedBudget.defects G d ∩ Q
local notation "f" => ComponentMinor.vertex G R W
local notation "K" => ComponentMinor.graph G R W
local notation "A" => ComponentMinor.contracted G R W

theorem overlap_subset_residual : Q ⊆ R := Finset.inter_subset_right

theorem middle_subset_residual : L ⊆ R :=
  Finset.sdiff_subset.trans Finset.inter_subset_left

theorem last_subset_residual : U ⊆ R := CurrentRounding.last_subset G a I

theorem overlap_disjoint_rest : Disjoint Q (L ∪ U) := by
  apply Finset.disjoint_left.mpr
  intro v hvQ hv
  have hvH := (Finset.mem_inter.mp hvQ).1
  rcases Finset.mem_union.mp hv with hvL | hvU
  · exact (Finset.mem_sdiff.mp hvL).2 hvH
  · exact (Finset.mem_sdiff.mp hvU).2 (subset_covered G _ hvH)

theorem residual_partition : R = Q ∪ L ∪ U := by
  ext v
  constructor
  · intro hv
    by_cases hH : v ∈ CurrentRounding.high G a I
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hH, hv⟩))
    · by_cases hcov : v ∈ covered G (CurrentRounding.high G a I)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hv, hcov⟩, hH⟩))
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hcov⟩)
  · intro hv
    rcases Finset.mem_union.mp hv with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact overlap_subset_residual G a d hd x hx hcap h
      · exact middle_subset_residual G a d hd x hx hcap h
    · exact last_subset_residual G a d hd x hx hcap h

theorem image_disjoint_residual (S Z : Finset V) (hS : S ⊆ R) (hZ : Z ⊆ R)
    (hdis : Disjoint S Z) : Disjoint (S.image f) (Z.image f) := by
  apply Finset.disjoint_left.mpr
  intro r hrS hrZ
  obtain ⟨v, hv, hvr⟩ := Finset.mem_image.mp hrS
  obtain ⟨u, hu, hur⟩ := Finset.mem_image.mp hrZ
  have he := congrArg Subtype.val (hvr.trans hur.symm)
  change ComponentMinor.label G R W v = ComponentMinor.label G R W u at he
  rw [ComponentMinor.label_residual G R W (hS hv),
    ComponentMinor.label_residual G R W (hZ hu)] at he
  exact Finset.disjoint_left.mp hdis hv (he.symm ▸ hu)

theorem defects_outside_covered :
    ∀ v ∉ R, G.degree v ≠ d → v ∈ covered G W := by
  intro v hvR hdef
  have hvB : v ∈ WeightedBudget.defects G d := by simp [WeightedBudget.defects, hdef]
  have hv0 := CurrentBudget.defects_subset_demands G d hvB
  by_contra hn
  exact hvR (Finset.mem_sdiff.mpr ⟨hv0, hn⟩)

theorem minor_regular_off :
    ∀ r ∉ (A ∪ (L ∪ U).image f) ∪ (B).image f, (K).degree r = d := by
  intro r hr
  have hnA : r ∉ A := fun h => hr (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hnRest : r ∉ (L ∪ U).image f :=
    fun h => hr (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hnB : r ∉ (B).image f := fun h => hr (Finset.mem_union_right _ h)
  have hm : ¬ (ComponentMinor.marked G R W r.val).Nonempty := by
    intro h
    exact hnA (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hfix := ComponentMinor.retained_fixed G R W r.property
  have he : f r.val = r := Subtype.ext hfix
  rw [← he]
  by_cases hvR : r.val ∈ R
  · have hvQ : r.val ∈ Q := by
      have hv := (Finset.ext_iff.mp (residual_partition G a d hd x hx hcap) r.val).mp hvR
      rcases Finset.mem_union.mp hv with h | hU
      · rcases Finset.mem_union.mp h with hQ | hL
        · exact hQ
        · exact False.elim (hnRest (Finset.mem_image.mpr
            ⟨r.val, Finset.mem_union_left _ hL, he⟩))
      · exact False.elim (hnRest (Finset.mem_image.mpr
          ⟨r.val, Finset.mem_union_right _ hU, he⟩))
    have hdeg : G.degree r.val = d := by
      by_contra hne
      have hvB : r.val ∈ WeightedBudget.defects G d := by
        simp [WeightedBudget.defects, hne]
      exact hnB (Finset.mem_image.mpr ⟨r.val, Finset.mem_inter.mpr ⟨hvB, hvQ⟩, he⟩)
    rw [ComponentMinor.degree_residual G R W hvR
      (CurrentCounting.regular_overlap_neighbors G a d hd x hx hcap hvQ hdeg)]
    exact hdeg
  · exact ComponentMinor.uncontracted_regular_degree G R W d
      (CurrentRounding.residual_disjoint_first G a I).symm
      (defects_outside_covered G a d hd x hx hcap) hvR hm

theorem minor_defect_degree : ∀ r ∈ (B).image f, d + 1 ≤ (K).degree r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
  have hqQ := (Finset.mem_inter.mp hq).2
  have hqR := overlap_subset_residual G a d hd x hx hcap hqQ
  have hdef := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).1).2
  exact ComponentMinor.defect_residual_degree G R W d hqR
    (CurrentCounting.overlap_degree G a d hd x hx hcap hqQ) hdef

theorem minor_regular_overlap_touch :
    ∀ r ∈ (Q).image f \ (B).image f,
      ∃ s ∈ (A ∪ (L ∪ U).image f) ∪ (B).image f, (K).Adj r s := by
  intro r hr
  obtain ⟨q, hqQ, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hr).1
  have hqR := overlap_subset_residual G a d hd x hx hcap hqQ
  have hdeg : G.degree q = d := by
    by_contra hne
    have hqB : q ∈ WeightedBudget.defects G d := by simp [WeightedBudget.defects, hne]
    exact (Finset.mem_sdiff.mp hr).2
      (Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hqB, hqQ⟩, rfl⟩)
  obtain ⟨v, hv, hqv⟩ := CurrentCounting.regular_overlap_touches_defect G a d hd x hx hcap hqQ hdeg
  have hvR : v ∈ R := by
    rcases Finset.mem_union.mp hv with hB | hL
    · exact overlap_subset_residual G a d hd x hx hcap (Finset.mem_inter.mp hB).2
    · exact middle_subset_residual G a d hd x hx hcap hL
  refine ⟨f v, ?_, ComponentMinor.residual_edge G R W hqR hvR hqv⟩
  rcases Finset.mem_union.mp hv with hB | hL
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hB, rfl⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨v, Finset.mem_union_left _ hL, rfl⟩))

theorem overlap_card_le (hden : MinorDensity.Bound G a) :
    (Q).card ≤ d * (d + 2) * ((W).card + (L).card + (U).card) := by
  have hQR := overlap_subset_residual G a d hd x hx hcap
  have hLR := middle_subset_residual G a d hd x hx hcap
  have hUR := last_subset_residual G a d hd x hx hcap
  have hrestR : L ∪ U ⊆ R := Finset.union_subset hLR hUR
  have hBQ : (B).image f ⊆ (Q).image f := Finset.image_subset_image Finset.inter_subset_right
  have hQT : Disjoint ((Q).image f) (A ∪ (L ∪ U).image f) := by
    apply Finset.disjoint_union_right.mpr
    exact ⟨(ComponentMinor.contracted_disjoint_residual G R W Q hQR).symm,
      image_disjoint_residual G a d hd x hx hcap Q (L ∪ U) hQR hrestR
        (overlap_disjoint_rest G a d hd x hx hcap)⟩
  have hh := CurrentCounting.minor_regular_shell_count G a d K hden
    (ComponentMinor.isMinor G R W) hd (A ∪ (L ∪ U).image f) ((Q).image f) ((B).image f)
    hBQ hQT (minor_regular_off G a d hd x hx hcap)
    (minor_defect_degree G a d hd x hx hcap)
    (minor_regular_overlap_touch G a d hd x hx hcap)
  have hQcard := ComponentMinor.card_image_residual G R W Q hQR
  rw [hQcard] at hh
  have hT : (A ∪ (L ∪ U).image f).card ≤ (W).card + (L).card + (U).card := by
    have h1 := Finset.card_union_le A ((L ∪ U).image f)
    have h2 := ComponentMinor.contracted_card_le G R W
    have h3 : ((L ∪ U).image f).card ≤ (L ∪ U).card := Finset.card_image_le
    have h4 := Finset.card_union_le L U
    omega
  exact hh.2.trans (Nat.mul_le_mul_left (d * (d + 2)) hT)

/-- The current paper's complete selected-vertex count, with its
exact b² and db² constants and with the actual component minor discharged. -/
theorem output_card_le (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) :
    ((CurrentRounding.output G a I).card : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 * ((W).card + (L).card) +
        d * ((d + 1 : ℕ) : ℝ) ^ 2 * CurrentRounding.slack G a I := by
  have hQ := overlap_card_le G a d hd x hx hcap hden
  have hz := CurrentCounting.outside_le_middle G a d hd x hx hcap ha
    (MinorDensity.induced_bound G hden)
  have hh := CurrentRounding.high_card_split G a I
  have ho := CurrentRounding.output_card_split G a I
  have hn : (CurrentRounding.output G a I).card ≤
      (d + 1) ^ 2 * ((W).card + (L).card + (U).card) := by nlinarith
  have hr : ((CurrentRounding.output G a I).card : ℝ) ≤
      ((d + 1 : ℕ) : ℝ) ^ 2 * ((W).card + (L).card + (U).card) := by exact_mod_cast hn
  have hu := CurrentCounting.last_le_slack G a d hd x hx hcap
  calc
    _ ≤ ((d + 1 : ℕ) : ℝ) ^ 2 * ((W).card + (L).card + (U).card) := hr
    _ ≤ ((d + 1 : ℕ) : ℝ) ^ 2 *
        ((W).card + (L).card + d * CurrentRounding.slack G a I) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ = _ := by ring

noncomputable def accuracy : ℝ := 1 / ((d : ℝ) * ((d + 1 : ℕ) : ℝ) ^ 2)

theorem accuracy_pos (hda : (d : ℝ) = 2 * a) (ha : 1 ≤ a) : 0 < accuracy d := by
  have hdpos : (0 : ℝ) < d := by rw [hda]; linarith
  unfold accuracy
  positivity

/-- The current integer-case transformation has the exact advertised slack. -/
theorem output_slack (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) :
    (1 + accuracy d) * (CurrentRounding.output G a I).card ≤
      CurrentRounding.objective G a I := by
  have hcount := output_card_le G a d hd x hx hcap ha hden
  have hsave := CurrentRounding.selection_saving G a I ha
    (MinorDensity.induced_bound G hden) (CurrentCounting.high_full_cost G a d hd x hx hcap)
  have hdpos : (0 : ℝ) < d := by rw [hd]; linarith
  have hbpos : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hδpos := accuracy_pos a d hd ha
  have hscaled := mul_le_mul_of_nonneg_left hcount hδpos.le
  have he : accuracy d *
      (((d + 1 : ℕ) : ℝ) ^ 2 * ((W).card + (L).card) +
        d * ((d + 1 : ℕ) : ℝ) ^ 2 * CurrentRounding.slack G a I) =
      (((W).card + (L).card : ℝ) / d) + CurrentRounding.slack G a I := by
    unfold accuracy
    field_simp [ne_of_gt hdpos, ne_of_gt hbpos] <;> ring
  rw [he] at hscaled
  have hdenom : a + 1 ≤ (d : ℝ) := by rw [hd]; linarith
  have hdiv : ((W).card + (L).card : ℝ) / d ≤ ((W).card + (L).card : ℝ) / (a + 1) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hdenom
  nlinarith

theorem objective_eq_auxiliary :
    CurrentRounding.objective G a I = cost (CurrentBudget.auxiliary G d) x := by
  classical
  simp [CurrentRounding.objective, CurrentCounting.input, cost, CurrentBudget.auxiliary]

/-- The current transformation rounds every feasible vector with the fixed
advertised accuracy to at most the true transformed optimum. -/
theorem rounded_le_optimum (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (happrox : cost (CurrentBudget.auxiliary G d) x ≤
      (1 + accuracy d) * CurrentBudget.auxiliaryNumber G d) :
    ((CurrentRounding.output G a I).card : ℝ) ≤ CurrentBudget.auxiliaryNumber G d := by
  have hs := output_slack G a d hd x hx hcap ha hden
  rw [objective_eq_auxiliary G a d hd x hx hcap] at hs
  exact Slack.pays_for_error (accuracy_pos a d hd ha) hs happrox

/-- The exact integer-case mathematical endpoint for the current selected
region F, closing the budget/rounding/count chain for a solver output.
This does not silently identify an older broadcast preprocessing program. -/
theorem rounded_output_bound (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (happrox : cost (CurrentBudget.auxiliary G d) x ≤
      (1 + accuracy d) * CurrentBudget.auxiliaryNumber G d) :
    dominates G (CurrentBudget.selected G d ∪ CurrentRounding.output G a I) ∧
      ((CurrentBudget.selected G d ∪ CurrentRounding.output G a I).card : ℝ) ≤
        (d + 1 : ℕ) * fractionalNumber G := by
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v ∈ covered G (CurrentBudget.selected G d)
    · exact covered_mono G Finset.subset_union_left hv
    · have hr : v ∈ CurrentBudget.demands G d :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
      have hc := CurrentRounding.output_covers G a I hr
      exact covered_mono G Finset.subset_union_right hc
  · have hround := rounded_le_optimum G a d hd x hx hcap ha hden happrox
    have hbudget := CurrentBudget.fractional_budget G d
    have hcard : ((CurrentBudget.selected G d ∪ CurrentRounding.output G a I).card : ℝ) ≤
        (CurrentBudget.selected G d).card + (CurrentRounding.output G a I).card := by
      exact_mod_cast Finset.card_union_le (CurrentBudget.selected G d) (CurrentRounding.output G a I)
    linarith

end Paper.CurrentCountBound
