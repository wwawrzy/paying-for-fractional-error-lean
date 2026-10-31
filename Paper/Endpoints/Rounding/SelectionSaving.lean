import Paper.Endpoints.Rounding.SelectionGeometry
import Paper.Preliminaries.Incidence

/-! Actual graph-level saving for the critical-degree selection. -/

namespace Paper.SelectionSaving

open SevenFoundation (closed covered feasible cost subset_covered)
open WeightedBudget (zone initialDemands boundaryCost auxiliary)
open SelectionGeometry
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (t : ℝ) (x : V → ℝ)

noncomputable def overlap : Finset V := high G d t x ∩ residual G d t x
noncomputable def outside : Finset V := high G d t x \ residual G d t x
noncomputable def middle : Finset V :=
  (residual G d t x ∩ covered G (high G d t x)) \ high G d t x
noncomputable def excess : ℝ :=
  ∑ v ∈ high G d t x, ((hits G d t x v : ℝ) - (d + 1 : ℕ))

theorem localOutput_covers_demands {r : V} (hr : r ∈ initialDemands G d) :
    r ∈ covered G (localOutput G d t x) := by
  classical
  have hW : first G d t x ⊆ localOutput G d t x := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hH : high G d t x ⊆ localOutput G d t x := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  by_cases hw : r ∈ covered G (first G d t x)
  · exact SevenFoundation.covered_mono G hW hw
  have hR : r ∈ residual G d t x := Finset.mem_sdiff.mpr ⟨hr, hw⟩
  by_cases hh : r ∈ covered G (high G d t x)
  · exact SevenFoundation.covered_mono G hH hh
  have hu : r ∈ last G d t x := Finset.mem_sdiff.mpr ⟨hR, hh⟩
  exact subset_covered G _ (Finset.mem_union_right _ hu)

theorem high_middle_disjoint : Disjoint (high G d t x) (middle G d t x) := by
  classical
  exact Finset.disjoint_left.mpr (fun v hv hm => (Finset.mem_sdiff.mp hm).2 hv)

theorem covered_inter_high :
    high G d t x ∩ (residual G d t x ∩ covered G (high G d t x)) = overlap G d t x := by
  classical
  ext v
  simp only [Finset.mem_inter, overlap]
  constructor
  · rintro ⟨hh, hr, _⟩
    exact ⟨hh, hr⟩
  · rintro ⟨hh, hr⟩
    exact ⟨hh, hr, subset_covered G _ hh⟩

theorem covered_union_high :
    high G d t x ∪ (residual G d t x ∩ covered G (high G d t x)) =
      high G d t x ∪ middle G d t x := by
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, middle, Finset.mem_sdiff]
  tauto

theorem high_card_split :
    (high G d t x).card = (overlap G d t x).card + (outside G d t x).card := by
  have h := Finset.card_sdiff_add_card_inter (high G d t x) (residual G d t x)
  change (outside G d t x).card + (overlap G d t x).card = (high G d t x).card at h
  omega

theorem residual_card_split :
    (residual G d t x).card =
      (overlap G d t x).card + (middle G d t x).card + (last G d t x).card := by
  classical
  have h1 := Finset.card_sdiff_add_card_inter (residual G d t x) (covered G (high G d t x))
  have h2 := Finset.card_sdiff_add_card_inter
    (residual G d t x ∩ covered G (high G d t x)) (high G d t x)
  have hi : (residual G d t x ∩ covered G (high G d t x)) ∩ high G d t x =
      overlap G d t x := by
    rw [Finset.inter_comm]
    exact covered_inter_high G d t x
  rw [hi] at h2
  change (last G d t x).card + _ = _ at h1
  change (middle G d t x).card + _ = _ at h2
  omega

theorem output_card_split :
    (localOutput G d t x).card =
      (first G d t x).card + (high G d t x).card + (last G d t x).card := by
  classical
  have hwU : Disjoint (first G d t x) (last G d t x) := by
    apply Finset.disjoint_left.mpr
    intro v hw hu
    exact Finset.disjoint_left.mp (residual_disjoint_first G d t x)
      (last_subset_residual G d t x hu) hw
  have hhU := (last_disjoint_high G d t x).symm
  have hwH := (high_disjoint_first G d t x).symm
  unfold localOutput
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hwU, hhU⟩),
    Finset.card_union_of_disjoint hwH]

theorem output_card_identity :
    ((localOutput G d t x).card : ℝ) = (first G d t x).card +
      (residual G d t x).card - (middle G d t x).card + (outside G d t x).card := by
  have h1 := high_card_split G d t x
  have h2 := residual_card_split G d t x
  have h3 := output_card_split G d t x
  have hnat : (localOutput G d t x).card + (middle G d t x).card =
      (first G d t x).card + (residual G d t x).card + (outside G d t x).card := by omega
  have hr : ((localOutput G d t x).card : ℝ) + (middle G d t x).card =
      (first G d t x).card + (residual G d t x).card + (outside G d t x).card := by
    exact_mod_cast hnat
  linarith

/-- Lemma 11.2, obtained from actual edges and a real induced-density bound. -/
theorem excess_le (hd : (d : ℝ) = 2 * t) (hden : Incidence.InducedDensityBound G t) :
    excess G d t x ≤ t * (middle G d t x).card - (t + 1) * (outside G d t x).card := by
  classical
  have hinc := Incidence.closed_incidence_le_of_density G hden
    (high G d t x) (residual G d t x ∩ covered G (high G d t x))
  have hsum : (∑ v ∈ high G d t x,
      ((closed G v ∩ (residual G d t x ∩ covered G (high G d t x))).card : ℝ)) =
      ∑ v ∈ high G d t x, (hits G d t x v : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have heq : closed G v ∩ (residual G d t x ∩ covered G (high G d t x)) =
        closed G v ∩ residual G d t x := by
      ext r
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hc, hr, _⟩
        exact ⟨hc, hr⟩
      · rintro ⟨hc, hr⟩
        exact ⟨hc, hr, Finset.mem_biUnion.mpr ⟨v, hv, hc⟩⟩
    rw [heq]
    rfl
  rw [hsum, covered_inter_high, covered_union_high,
    Finset.card_union_of_disjoint (high_middle_disjoint G d t x)] at hinc
  have hcard : ((high G d t x).card : ℝ) =
      (overlap G d t x).card + (outside G d t x).card := by
    exact_mod_cast high_card_split G d t x
  have he : excess G d t x = (∑ v ∈ high G d t x, (hits G d t x v : ℝ)) -
      (d + 1 : ℕ) * (high G d t x).card := by
    simp [excess, Finset.sum_sub_distrib, mul_comm]
    ring
  push_cast at hinc he
  rw [hd, hcard] at he
  rw [hcard] at hinc
  rw [he]
  nlinarith

theorem cost_decomposition (hx : feasible (auxiliary G d) x) :
    cost (auxiliary G d) x =
      (d + 1 : ℕ) * (∑ v ∈ first G d t x, x v) +
      (∑ v, (hits G d t x v : ℝ) * x v) + slack G d t x -
      (∑ v ∈ high G d t x, ((hits G d t x v : ℝ) - (d + 1 : ℕ)) * x v) := by
  classical
  have hW : (d + 1 : ℕ) * (∑ v ∈ first G d t x, x v) =
      ∑ v, if v ∈ first G d t x then ((d + 1 : ℕ) : ℝ) * x v else 0 := by
    simp [Finset.mul_sum]
  have hP : slack G d t x = ∑ v, if v ∈ low G d t x then
      (boundaryCost G d v - hits G d t x v) * x v else 0 := by simp [slack]
  have hE : (∑ v ∈ high G d t x, ((hits G d t x v : ℝ) - (d + 1 : ℕ)) * x v) =
      ∑ v, if v ∈ high G d t x then ((hits G d t x v : ℝ) - (d + 1 : ℕ)) * x v else 0 := by simp
  rw [hW, hP, hE, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  change (if v ∈ zone G d then boundaryCost G d v else 0) * x v = _
  by_cases hz : v ∈ zone G d
  · rw [if_pos hz]
    by_cases hw : v ∈ first G d t x
    · have hnH : v ∉ high G d t x := fun hh =>
        Finset.disjoint_left.mp (high_disjoint_first G d t x) hh hw
      have hnL : v ∉ low G d t x := fun hl => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hl).1).2 hw
      simp [hw, hnH, hnL, first_cost G d t x hw, first_hits_zero G d t x hw]
    · rw [if_neg hw]
      by_cases hh : v ∈ high G d t x
      · have hnL : v ∉ low G d t x := by
          intro hl
          have h1 := (Finset.mem_filter.mp hh).2
          have h2 := (Finset.mem_filter.mp hl).2
          omega
        rw [if_pos hh, if_neg hnL, high_cost G d t x hh]
        ring
      · have hl : v ∈ low G d t x := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_sdiff.mpr ⟨hz, hw⟩, ?_⟩
          have hn : ¬ d + 1 ≤ hits G d t x v := by
            intro h
            exact hh (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hz, hw⟩, h⟩)
          omega
        rw [if_neg hh, if_pos hl]
        ring
  · have hx0 : x v = 0 := hx.2.1 v hz
    simp [hx0]

/-- The first inequality of Lemma 11.3, with no assumed incidence/saving estimate. -/
theorem selection_saving (ht : 1 ≤ t) (hd : (d : ℝ) = 2 * t)
    (hden : Incidence.InducedDensityBound G t) (hx : feasible (auxiliary G d) x) :
    cost (auxiliary G d) x - (localOutput G d t x).card ≥
      t / (t + 1) * (first G d t x).card +
      1 / (t + 1) * (middle G d t x).card + slack G d t x := by
  have htp : 0 < t + 1 := by linarith
  have hW := mul_le_mul_of_nonneg_left (first_mass_lower G d t x)
    (show (0 : ℝ) ≤ (d + 1 : ℕ) by positivity)
  have hR := auxiliary_coverage_sum G d x (residual G d t x)
    (residual_subset_demands G d t x) hx
  have hE := weighted_excess_bound G d t x
  have hI := div_le_div_of_nonneg_right (excess_le G d t x hd hden) (le_of_lt htp)
  have hcost := cost_decomposition G d t x hx
  have hcard := output_card_identity G d t x
  change (∑ v ∈ high G d t x, ((hits G d t x v : ℝ) - (d + 1 : ℕ)) * x v) ≤
    excess G d t x / (t + 1) at hE
  have hW' : (d + 1 : ℕ) * (first G d t x).card / (t + 1) ≤
      (d + 1 : ℕ) * (∑ v ∈ first G d t x, x v) := by
    simpa only [mul_one_div, mul_div_assoc] using hW
  have hR' : ((residual G d t x).card : ℝ) ≤ ∑ v, (hits G d t x v : ℝ) * x v := hR
  have hbase : (d + 1 : ℕ) * (first G d t x).card / (t + 1) +
      (residual G d t x).card + slack G d t x -
      (t * (middle G d t x).card - (t + 1) * (outside G d t x).card) / (t + 1) ≤
      cost (auxiliary G d) x := by linarith
  have hid : ((d + 1 : ℕ) : ℝ) = 2 * t + 1 := by push_cast; linarith
  rw [hid] at hbase
  rw [hcard]
  have heq : (2 * t + 1) * (first G d t x).card / (t + 1) +
      (residual G d t x).card + slack G d t x -
      (t * (middle G d t x).card - (t + 1) * (outside G d t x).card) / (t + 1) =
      (first G d t x).card + (residual G d t x).card - (middle G d t x).card +
      (outside G d t x).card + t / (t + 1) * (first G d t x).card +
      1 / (t + 1) * (middle G d t x).card + slack G d t x := by
    field_simp [ne_of_gt htp]
    ring
  linarith

end Paper.SelectionSaving
