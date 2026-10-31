import Paper.Endpoints.Girth.CurrentGirthCounting

/-! # The paper's selected-output constants and fixed solver accuracies -/

namespace Paper.CurrentGirthOutput

open SimpleGraph SevenFoundation
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

section Four

variable (x : V → ℝ) (hx : feasible (CurrentBudget.auxiliary G 4) x)
  (hcap : ∀ v ∈ CurrentBudget.candidates G 4, x v ≤ 1)
local notation "I" => CurrentCounting.input G 2 4 (by norm_num) x hx hcap
local notation "W" => CurrentRounding.first G 2 I
local notation "L" => CurrentRounding.middle G 2 I
local notation "U" => CurrentRounding.last G 2 I
local notation "D" => CurrentRounding.output G 2 I

theorem count_four (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 4 ≤ c.length) :
    ((D).card : ℝ) ≤ 25 * ((W).card + (L).card) +
      100 * CurrentRounding.slack G 2 I := by
  have hden := CurrentPlanarFaceBound.induced_density hplanar 4 (by norm_num) hgirth
  norm_num at hden
  have hq := CurrentGirthCounting.overlap_bound G 2 4 (by norm_num) x hx hcap
    hplanar 4 (by norm_num) (by norm_num) hgirth
  norm_num at hq
  have hz := CurrentCounting.outside_le_middle G 2 4 (by norm_num) x hx hcap (by norm_num) hden
  have hh := CurrentRounding.high_card_split G 2 I
  have ho := CurrentRounding.output_card_split G 2 I
  have hzR : ((CurrentRounding.outside G 2 I).card : ℝ) ≤ (L).card := by exact_mod_cast hz
  have hhR : ((CurrentRounding.high G 2 I).card : ℝ) =
      (CurrentRounding.overlap G 2 I).card + (CurrentRounding.outside G 2 I).card := by
    exact_mod_cast hh
  have hoR : ((D).card : ℝ) = (W).card + (CurrentRounding.high G 2 I).card + (U).card := by
    exact_mod_cast ho
  have hb : ((D).card : ℝ) ≤ 25 * ((W).card + (L).card + (U).card) := by
    nlinarith only [hq, hzR, hhR, hoR]
  have hu := CurrentCounting.last_le_slack G 2 4 (by norm_num) x hx hcap
  norm_num at hu
  nlinarith only [hb, hu]

theorem slack_four (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 4 ≤ c.length) :
    (1 + (1 / 100 : ℝ)) * (D).card ≤ cost (CurrentBudget.auxiliary G 4) x := by
  have hcount := count_four G x hx hcap hplanar hgirth
  have hden := CurrentPlanarFaceBound.induced_density hplanar 4 (by norm_num) hgirth
  norm_num at hden
  have hs := CurrentRounding.selection_saving G 2 I (by norm_num) hden
    (CurrentCounting.high_full_cost G 2 4 (by norm_num) x hx hcap)
  rw [CurrentCountBound.objective_eq_auxiliary G 2 4 (by norm_num) x hx hcap] at hs
  norm_num at hs
  have hw : (0 : ℝ) ≤ (W).card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ (L).card := Nat.cast_nonneg _
  nlinarith only [hcount, hs, hw, hl]

theorem rounded_four (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 4 ≤ c.length)
    (hcost : cost (CurrentBudget.auxiliary G 4) x ≤
      (1 + (1 / 100 : ℝ)) * CurrentBudget.auxiliaryNumber G 4) :
    dominates G (CurrentBudget.selected G 4 ∪ D) ∧
      ((CurrentBudget.selected G 4 ∪ D).card : ℝ) ≤ 5 * fractionalNumber G := by
  have hr := Slack.pays_for_error (by norm_num : (0 : ℝ) < 1 / 100)
    (slack_four G x hx hcap hplanar hgirth) hcost
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v ∈ covered G (CurrentBudget.selected G 4)
    · exact covered_mono G Finset.subset_union_left hv
    · have hrv : v ∈ CurrentBudget.demands G 4 :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
      exact covered_mono G Finset.subset_union_right (CurrentRounding.output_covers G 2 I hrv)
  · have hb := CurrentBudget.fractional_budget G 4
    have hu : ((CurrentBudget.selected G 4 ∪ D).card : ℝ) ≤
        (CurrentBudget.selected G 4).card + (D).card := by
      exact_mod_cast Finset.card_union_le (CurrentBudget.selected G 4) D
    norm_num at hb
    linarith

end Four

section Six

variable (x : V → ℝ) (hx : feasible (CurrentBudget.auxiliary G 3) x)
  (hcap : ∀ v ∈ CurrentBudget.candidates G 3, x v ≤ 1)
local notation "I" => CurrentCounting.input G (3 / 2) 3 (by norm_num) x hx hcap
local notation "W" => CurrentRounding.first G (3 / 2) I
local notation "L" => CurrentRounding.middle G (3 / 2) I
local notation "U" => CurrentRounding.last G (3 / 2) I
local notation "D" => CurrentRounding.output G (3 / 2) I

theorem count_six (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length) :
    ((D).card : ℝ) ≤ 41 * ((W).card + (L).card) +
      63 * CurrentRounding.slack G (3 / 2) I := by
  have hden := CurrentPlanarFaceBound.induced_density hplanar 6 (by norm_num) hgirth
  norm_num at hden
  have hq := CurrentGirthCounting.overlap_bound G (3 / 2) 3 (by norm_num) x hx hcap
    hplanar 6 (by norm_num) (by norm_num) hgirth
  have hp := CurrentGirthCounting.incident_bound G (3 / 2) 3 (by norm_num) x hx hcap
    hplanar 6 (by norm_num) (by norm_num) hgirth
  norm_num at hq hp
  have hz := CurrentCounting.outside_le_middle G (3 / 2) 3 (by norm_num) x hx hcap
    (by norm_num) hden
  have hh := CurrentRounding.high_card_split G (3 / 2) I
  have ho := CurrentRounding.output_card_split G (3 / 2) I
  have hzR : ((CurrentRounding.outside G (3 / 2) I).card : ℝ) ≤ (L).card := by exact_mod_cast hz
  have hhR : ((CurrentRounding.high G (3 / 2) I).card : ℝ) =
      (CurrentRounding.overlap G (3 / 2) I).card + (CurrentRounding.outside G (3 / 2) I).card := by
    exact_mod_cast hh
  have hoR : ((D).card : ℝ) = (W).card + (CurrentRounding.high G (3 / 2) I).card + (U).card := by
    exact_mod_cast ho
  have hb : ((D).card : ℝ) ≤ 41 * (W).card + 36 * (L).card + 21 * (U).card := by
    nlinarith only [hq, hp, hzR, hhR, hoR]
  have hu := CurrentCounting.last_le_slack G (3 / 2) 3 (by norm_num) x hx hcap
  norm_num at hu
  have hl : (0 : ℝ) ≤ (L).card := Nat.cast_nonneg _
  nlinarith only [hb, hu, hl]

theorem slack_six (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length) :
    (1 + (2 / 205 : ℝ)) * (D).card ≤ cost (CurrentBudget.auxiliary G 3) x := by
  have hcount := count_six G x hx hcap hplanar hgirth
  have hden := CurrentPlanarFaceBound.induced_density hplanar 6 (by norm_num) hgirth
  norm_num at hden
  have hs := CurrentRounding.selection_saving G (3 / 2) I (by norm_num) hden
    (CurrentCounting.high_full_cost G (3 / 2) 3 (by norm_num) x hx hcap)
  rw [CurrentCountBound.objective_eq_auxiliary G (3 / 2) 3 (by norm_num) x hx hcap] at hs
  norm_num at hs
  have hP := CurrentRounding.slack_nonneg G (3 / 2) I (by
    intro v hv
    have h := (CurrentCounting.other_slack G (3 / 2) 3 (by norm_num) x hx hcap v hv).2
    change (CurrentRounding.hits G (3 / 2) I v : ℝ) ≤ CurrentBudget.boundaryCost G 3 v
    linarith)
  nlinarith only [hcount, hs, hP]

theorem rounded_six (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length)
    (hcost : cost (CurrentBudget.auxiliary G 3) x ≤
      (1 + (2 / 205 : ℝ)) * CurrentBudget.auxiliaryNumber G 3) :
    dominates G (CurrentBudget.selected G 3 ∪ D) ∧
      ((CurrentBudget.selected G 3 ∪ D).card : ℝ) ≤ 4 * fractionalNumber G := by
  have hr := Slack.pays_for_error (by norm_num : (0 : ℝ) < 2 / 205)
    (slack_six G x hx hcap hplanar hgirth) hcost
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v ∈ covered G (CurrentBudget.selected G 3)
    · exact covered_mono G Finset.subset_union_left hv
    · have hrv : v ∈ CurrentBudget.demands G 3 :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
      exact covered_mono G Finset.subset_union_right (CurrentRounding.output_covers G (3 / 2) I hrv)
  · have hb := CurrentBudget.fractional_budget G 3
    have hu : ((CurrentBudget.selected G 3 ∪ D).card : ℝ) ≤
        (CurrentBudget.selected G 3).card + (D).card := by
      exact_mod_cast Finset.card_union_le (CurrentBudget.selected G 3) D
    norm_num at hb
    linarith

end Six

end Paper.CurrentGirthOutput

#print axioms Paper.CurrentGirthOutput.count_four
#print axioms Paper.CurrentGirthOutput.slack_four
#print axioms Paper.CurrentGirthOutput.rounded_four
#print axioms Paper.CurrentGirthOutput.count_six
#print axioms Paper.CurrentGirthOutput.slack_six
#print axioms Paper.CurrentGirthOutput.rounded_six
