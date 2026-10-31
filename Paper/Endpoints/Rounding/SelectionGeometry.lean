import Paper.Endpoints.Rounding.WeightedBudget

/-!
# Actual selection geometry for the critical-degree branch

The sets below use the original graph degree and the strict threshold in the
paper. The facts hold for any real threshold parameter t and natural d.
They do not assume a density bound or a fractional solver.
-/

namespace Paper.SelectionGeometry

open SevenFoundation (closed covered feasible cost dominates mem_closed closed_symm
  self_mem_closed subset_covered covered_mono)
open WeightedBudget (zone far initialDemands boundaryCost auxiliary)
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (t : ℝ) (x : V → ℝ)

noncomputable def first : Finset V := by
  classical
  exact (zone G d).filter (fun v => d + 1 ≤ G.degree v ∧ 1 / (t + 1) < x v)

noncomputable def residual : Finset V := initialDemands G d \ covered G (first G d t x)

noncomputable def hits (v : V) : ℕ := (closed G v ∩ residual G d t x).card

noncomputable def high : Finset V := by
  classical
  exact (zone G d \ first G d t x).filter (fun v => d + 1 ≤ hits G d t x v)

noncomputable def low : Finset V := by
  classical
  exact (zone G d \ first G d t x).filter (fun v => hits G d t x v ≤ d)

noncomputable def last : Finset V := residual G d t x \ covered G (high G d t x)

noncomputable def localOutput : Finset V := first G d t x ∪ high G d t x ∪ last G d t x

noncomputable def output : Finset V := far G d ∪ localOutput G d t x

noncomputable def slack : ℝ :=
  ∑ v ∈ low G d t x, (boundaryCost G d v - hits G d t x v) * x v

theorem first_subset_zone : first G d t x ⊆ zone G d := by
  classical
  exact Finset.filter_subset _ _

theorem residual_subset_demands : residual G d t x ⊆ initialDemands G d :=
  Finset.sdiff_subset

theorem residual_subset_zone : residual G d t x ⊆ zone G d :=
  (residual_subset_demands G d t x).trans Finset.sdiff_subset

theorem high_subset_zone : high G d t x ⊆ zone G d := by
  classical
  exact (Finset.filter_subset _ _).trans Finset.sdiff_subset

theorem last_subset_residual : last G d t x ⊆ residual G d t x := Finset.sdiff_subset

theorem residual_disjoint_first : Disjoint (residual G d t x) (first G d t x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hw)

theorem high_disjoint_first : Disjoint (high G d t x) (first G d t x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hw

theorem last_disjoint_high : Disjoint (last G d t x) (high G d t x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hh
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hh)

theorem first_hits_zero {v : V} (hv : v ∈ first G d t x) : hits G d t x v = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hr).2).2
    (Finset.mem_biUnion.mpr ⟨v, hv, (Finset.mem_inter.mp hr).1⟩)

theorem output_dominates : dominates G (output G d t x) := by
  classical
  intro v
  have hF : far G d ⊆ output G d t x := Finset.subset_union_left
  have hW : first G d t x ⊆ output G d t x := by
    intro u hu
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
  have hH : high G d t x ⊆ output G d t x := by
    intro u hu
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
  have hU : last G d t x ⊆ output G d t x := by
    intro u hu
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hu)
  by_cases hf : v ∈ covered G (far G d)
  · exact covered_mono G hF hf
  have hz : v ∈ zone G d := by
    by_contra hn
    have hvf : v ∈ far G d := by simp [far, hn]
    exact hf (subset_covered G _ hvf)
  have hr0 : v ∈ initialDemands G d := Finset.mem_sdiff.mpr ⟨hz, hf⟩
  by_cases hw : v ∈ covered G (first G d t x)
  · exact covered_mono G hW hw
  have hr : v ∈ residual G d t x := Finset.mem_sdiff.mpr ⟨hr0, hw⟩
  by_cases hh : v ∈ covered G (high G d t x)
  · exact covered_mono G hH hh
  exact subset_covered G _ (hU (Finset.mem_sdiff.mpr ⟨hr, hh⟩))

/-- Counting two disjoint parts of a closed neighborhood when neither contains v. -/
theorem two_parts_le_degree (S T : Finset V) (v : V)
    (hST : Disjoint S T) (hvS : v ∉ S) (hvT : v ∉ T) :
    (closed G v ∩ S).card + (closed G v ∩ T).card ≤ G.degree v := by
  classical
  have hd : Disjoint (closed G v ∩ S) (closed G v ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro u hs ht
    exact Finset.disjoint_left.mp hST (Finset.mem_inter.mp hs).2 (Finset.mem_inter.mp ht).2
  have hsub : (closed G v ∩ S) ∪ (closed G v ∩ T) ⊆ G.neighborFinset v := by
    intro u hu
    have hclosed : u ∈ closed G v := by
      rcases Finset.mem_union.mp hu with h | h <;> exact (Finset.mem_inter.mp h).1
    have hne : u ≠ v := by
      intro heq
      subst u
      rcases Finset.mem_union.mp hu with h | h
      · exact hvS (Finset.mem_inter.mp h).2
      · exact hvT (Finset.mem_inter.mp h).2
    simpa only [SimpleGraph.mem_neighborFinset] using
      ((mem_closed G u v).mp hclosed |>.resolve_left hne)
  rw [← Finset.card_union_of_disjoint hd]
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using Finset.card_le_card hsub

theorem residual_disjoint_far : Disjoint (residual G d t x) (far G d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hr hf
  exact (Finset.mem_sdiff.mp hf).2 (residual_subset_zone G d t x hr)

theorem cheap_hits {v : V} (hz : v ∈ zone G d)
    (hc : boundaryCost G d v < (d + 1 : ℕ)) :
    (hits G d t x v : ℝ) ≤ boundaryCost G d v - 1 := by
  have hp := WeightedBudget.cheap_cost G d hc
  have hvR : v ∉ residual G d t x := fun hv => hp.2 (residual_subset_demands G d t x hv)
  have hvF : v ∉ far G d := fun hv => (Finset.mem_sdiff.mp hv).2 hz
  have hn := two_parts_le_degree G (residual G d t x) (far G d) v
    (residual_disjoint_far G d t x) hvR hvF
  rw [hp.1] at hn
  have hr : (hits G d t x v : ℝ) + ((closed G v ∩ far G d).card : ℝ) ≤ d := by
    exact_mod_cast hn
  unfold boundaryCost
  push_cast
  linarith

theorem low_coefficient_pos {v : V} (hv : v ∈ low G d t x) :
    1 ≤ boundaryCost G d v - hits G d t x v := by
  classical
  have hz := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hh : hits G d t x v ≤ d := (Finset.mem_filter.mp hv).2
  have hc := WeightedBudget.boundaryCost_bounds G d hz
  by_cases hcheap : boundaryCost G d v < (d + 1 : ℕ)
  · have := cheap_hits G d t x hz hcheap
    linarith
  · have heq : boundaryCost G d v = (d + 1 : ℕ) := le_antisymm hc.2 (le_of_not_gt hcheap)
    have hr : (hits G d t x v : ℝ) ≤ d := by exact_mod_cast hh
    rw [heq]
    push_cast
    linarith

theorem high_cost {v : V} (hv : v ∈ high G d t x) :
    boundaryCost G d v = (d + 1 : ℕ) := by
  classical
  have hz := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hh : d + 1 ≤ hits G d t x v := (Finset.mem_filter.mp hv).2
  have hc := WeightedBudget.boundaryCost_bounds G d hz
  apply le_antisymm hc.2
  by_contra hn
  have hh' := cheap_hits G d t x hz (lt_of_not_ge hn)
  have hr : ((d + 1 : ℕ) : ℝ) ≤ hits G d t x v := by exact_mod_cast hh
  linarith

theorem first_cost {v : V} (hv : v ∈ first G d t x) :
    boundaryCost G d v = (d + 1 : ℕ) := by
  classical
  have hz := (Finset.mem_filter.mp hv).1
  have hd := (Finset.mem_filter.mp hv).2.1
  apply le_antisymm (WeightedBudget.boundaryCost_bounds G d hz).2
  by_contra hn
  have hp := WeightedBudget.cheap_cost G d (lt_of_not_ge hn)
  omega

theorem hits_le_degree_succ (v : V) : hits G d t x v ≤ G.degree v + 1 := by
  have h := Finset.card_le_card
    (Finset.inter_subset_left : closed G v ∩ residual G d t x ⊆ closed G v)
  simpa only [WeightedBudget.closed_card] using h

theorem high_heavy_weight_le {v : V} (hv : v ∈ high G d t x)
    (hh : d + 1 < hits G d t x v) : x v ≤ 1 / (t + 1) := by
  classical
  have hz := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).1
  have hw := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
  have hcard := hits_le_degree_succ G d t x v
  have hdeg : d + 1 ≤ G.degree v := by omega
  by_contra hn
  exact hw (Finset.mem_filter.mpr ⟨hz, hdeg, lt_of_not_ge hn⟩)

theorem first_mass_lower :
    ((first G d t x).card : ℝ) * (1 / (t + 1)) ≤ ∑ v ∈ first G d t x, x v := by
  classical
  calc
    ((first G d t x).card : ℝ) * (1 / (t + 1)) =
        ∑ _v ∈ first G d t x, (1 / (t + 1)) := by simp
    _ ≤ ∑ v ∈ first G d t x, x v := by
      apply Finset.sum_le_sum
      intro v hv
      exact le_of_lt (Finset.mem_filter.mp hv).2.2

theorem weighted_excess_bound :
    (∑ v ∈ high G d t x, ((hits G d t x v : ℝ) - (d + 1 : ℕ)) * x v) ≤
      (∑ v ∈ high G d t x, ((hits G d t x v : ℝ) - (d + 1 : ℕ))) / (t + 1) := by
  classical
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro v hv
  have hh : d + 1 ≤ hits G d t x v := (Finset.mem_filter.mp hv).2
  by_cases heq : hits G d t x v = d + 1
  · simp [heq]
  · have hgt : d + 1 < hits G d t x v := by omega
    have hcoef : (0 : ℝ) ≤ (hits G d t x v : ℝ) - (d + 1 : ℕ) := by
      have hcast : ((d + 1 : ℕ) : ℝ) ≤ hits G d t x v := by exact_mod_cast hh
      linarith
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (high_heavy_weight_le G d t x hv hgt) hcoef

theorem slack_nonneg (hx : ∀ v, 0 ≤ x v) : 0 ≤ slack G d t x := by
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (le_trans zero_le_one (low_coefficient_pos G d t x hv)) (hx v)

theorem low_mass_le_slack (hx : ∀ v, 0 ≤ x v) :
    ∑ v ∈ low G d t x, x v ≤ slack G d t x := by
  apply Finset.sum_le_sum
  intro v hv
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (low_coefficient_pos G d t x hv) (hx v)

/-- Coverage constraints for any actual subset of the auxiliary demand set. -/
theorem auxiliary_coverage_sum (S : Finset V) (hS : S ⊆ initialDemands G d)
    (hx : feasible (auxiliary G d) x) :
    (S.card : ℝ) ≤ ∑ v, ((closed G v ∩ S).card : ℝ) * x v := by
  classical
  rw [← WeightedBudget.incidence_sum G S x]
  calc
    (S.card : ℝ) = ∑ _r ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ r ∈ S, ∑ v ∈ closed G r, x v := by
      apply Finset.sum_le_sum
      intro r hr
      have hcov := hx.2.2 r (hS hr)
      exact le_trans hcov (Finset.sum_le_sum_of_subset_of_nonneg
        Finset.inter_subset_left (fun v _ _ => hx.1 v))

theorem no_last_incidence {v : V}
    (hv : v ∈ first G d t x ∪ high G d t x) :
    closed G v ∩ last G d t x = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hlast := (Finset.mem_inter.mp hr).2
  have hclosed := (Finset.mem_inter.mp hr).1
  rcases Finset.mem_union.mp hv with hw | hh
  · exact (Finset.mem_sdiff.mp (last_subset_residual G d t x hlast)).2
      (Finset.mem_biUnion.mpr ⟨v, hw, hclosed⟩)
  · exact (Finset.mem_sdiff.mp hlast).2
      (Finset.mem_biUnion.mpr ⟨v, hh, hclosed⟩)

/-- The second inequality of Lemma 11.3, with actual graph sets and slack. -/
theorem last_card_le_slack (hx : feasible (auxiliary G d) x) :
    ((last G d t x).card : ℝ) ≤ d * slack G d t x := by
  classical
  have hcov := auxiliary_coverage_sum G d x (last G d t x)
    ((last_subset_residual G d t x).trans (residual_subset_demands G d t x)) hx
  have hpoint : ∀ v, ((closed G v ∩ last G d t x).card : ℝ) * x v ≤
      if v ∈ low G d t x then (d : ℝ) * x v else 0 := by
    intro v
    by_cases hv : v ∈ low G d t x
    · rw [if_pos hv]
      have hsub : closed G v ∩ last G d t x ⊆ closed G v ∩ residual G d t x :=
        Finset.inter_subset_inter_left (last_subset_residual G d t x)
      have hn : (closed G v ∩ last G d t x).card ≤ d :=
        (Finset.card_le_card hsub).trans (Finset.mem_filter.mp hv).2
      apply mul_le_mul_of_nonneg_right _ (hx.1 v)
      exact_mod_cast hn
    · rw [if_neg hv]
      by_cases hz : v ∈ zone G d
      · have hwH : v ∈ first G d t x ∪ high G d t x := by
          by_cases hw : v ∈ first G d t x
          · exact Finset.mem_union_left _ hw
          · apply Finset.mem_union_right
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_sdiff.mpr ⟨hz, hw⟩, ?_⟩
            have hn : ¬ hits G d t x v ≤ d := by
              intro hh
              exact hv (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hz, hw⟩, hh⟩)
            omega
        rw [no_last_incidence G d t x hwH]
        simp
      · have hx0 : x v = 0 := hx.2.1 v hz
        simp [hx0]
  calc
    ((last G d t x).card : ℝ) ≤ ∑ v, ((closed G v ∩ last G d t x).card : ℝ) * x v := hcov
    _ ≤ ∑ v, if v ∈ low G d t x then (d : ℝ) * x v else 0 :=
      Finset.sum_le_sum (fun v _ => hpoint v)
    _ = d * ∑ v ∈ low G d t x, x v := by simp [Finset.mul_sum]
    _ ≤ d * slack G d t x :=
      mul_le_mul_of_nonneg_left (low_mass_le_slack G d t x hx.1) (Nat.cast_nonneg d)

end Paper.SelectionGeometry
