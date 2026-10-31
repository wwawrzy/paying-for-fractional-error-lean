import Paper.Preliminaries.Incidence

/-!
The current common rounding lemma for arbitrary candidates, partial demands,
and costs. No fixed defect zone or uniform-cost reduction is used.
The two supplementary cost hypotheses below are exactly the hypotheses on
H and O in `simp:endpoint:rounding`; none of its conclusions is assumed.
-/

namespace Paper.CurrentRounding

open SevenFoundation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (a : ℝ)

structure Input where
  candidates : Finset V
  demands : Finset V
  demands_subset : demands ⊆ candidates
  c : V → ℝ
  x : V → ℝ
  cost_pos : ∀ v ∈ candidates, 0 < c v
  cost_le : ∀ v ∈ candidates, c v ≤ 2 * a + 1
  nonneg : ∀ v ∈ candidates, 0 ≤ x v
  cap : ∀ v ∈ candidates, x v ≤ 1
  coverage : ∀ r ∈ demands, 1 ≤ ∑ v ∈ closed G r ∩ candidates, x v

variable (I : Input G a)

noncomputable def first : Finset V := by
  classical
  exact I.candidates.filter (fun v => I.c v = 2 * a + 1 ∧ 1 / (a + 1) < I.x v)

noncomputable def residual : Finset V := I.demands \ covered G (first G a I)

noncomputable def hits (v : V) : ℕ := (closed G v ∩ residual G a I).card

noncomputable def high : Finset V := by
  classical
  exact (I.candidates \ first G a I).filter (fun v => 2 * a + 1 ≤ (hits G a I v : ℝ))

noncomputable def last : Finset V := residual G a I \ covered G (high G a I)

noncomputable def output : Finset V := first G a I ∪ high G a I ∪ last G a I

noncomputable def other : Finset V := I.candidates \ (first G a I ∪ high G a I)

noncomputable def overlap : Finset V := high G a I ∩ residual G a I

noncomputable def outside : Finset V := high G a I \ residual G a I

noncomputable def middle : Finset V :=
  (residual G a I ∩ covered G (high G a I)) \ high G a I

noncomputable def excess : ℝ :=
  ∑ v ∈ high G a I, ((hits G a I v : ℝ) - (2 * a + 1))

noncomputable def slack : ℝ :=
  ∑ v ∈ other G a I, (I.c v - (hits G a I v : ℝ)) * I.x v

noncomputable def objective : ℝ := ∑ v ∈ I.candidates, I.c v * I.x v

theorem first_subset : first G a I ⊆ I.candidates := by
  classical
  exact Finset.filter_subset _ _

theorem high_subset : high G a I ⊆ I.candidates := by
  classical
  exact (Finset.filter_subset _ _).trans Finset.sdiff_subset

theorem other_subset : other G a I ⊆ I.candidates := Finset.sdiff_subset

theorem residual_subset : residual G a I ⊆ I.demands := Finset.sdiff_subset

theorem last_subset : last G a I ⊆ residual G a I := Finset.sdiff_subset

theorem first_hits_zero {v : V} (hv : v ∈ first G a I) : hits G a I v = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hr).2).2
    (Finset.mem_biUnion.mpr ⟨v, hv, (Finset.mem_inter.mp hr).1⟩)

theorem residual_disjoint_first : Disjoint (residual G a I) (first G a I) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hw)

theorem high_disjoint_first : Disjoint (high G a I) (first G a I) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hw

theorem last_disjoint_high : Disjoint (last G a I) (high G a I) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hh
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hh)

theorem output_covers : I.demands ⊆ covered G (output G a I) := by
  classical
  intro r hr
  have hW : first G a I ⊆ output G a I := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hH : high G a I ⊆ output G a I := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  by_cases hw : r ∈ covered G (first G a I)
  · exact covered_mono G hW hw
  have hR : r ∈ residual G a I := Finset.mem_sdiff.mpr ⟨hr, hw⟩
  by_cases hh : r ∈ covered G (high G a I)
  · exact covered_mono G hH hh
  have hu : r ∈ last G a I := Finset.mem_sdiff.mpr ⟨hR, hh⟩
  exact subset_covered G _ (Finset.mem_union_right _ hu)

theorem output_subset : output G a I ⊆ I.candidates := by
  classical
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact first_subset G a I h
    · exact high_subset G a I h
  · exact I.demands_subset (residual_subset G a I (last_subset G a I h))

theorem high_middle_disjoint : Disjoint (high G a I) (middle G a I) := by
  classical
  exact Finset.disjoint_left.mpr (fun v hv hm => (Finset.mem_sdiff.mp hm).2 hv)

theorem covered_inter_high :
    high G a I ∩ (residual G a I ∩ covered G (high G a I)) = overlap G a I := by
  classical
  ext v
  simp only [Finset.mem_inter, overlap]
  constructor
  · rintro ⟨hh, hr, _⟩
    exact ⟨hh, hr⟩
  · rintro ⟨hh, hr⟩
    exact ⟨hh, hr, subset_covered G _ hh⟩

theorem covered_union_high :
    high G a I ∪ (residual G a I ∩ covered G (high G a I)) =
      high G a I ∪ middle G a I := by
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, middle, Finset.mem_sdiff]
  tauto

theorem high_card_split :
    (high G a I).card = (overlap G a I).card + (outside G a I).card := by
  have h := Finset.card_sdiff_add_card_inter (high G a I) (residual G a I)
  change (outside G a I).card + (overlap G a I).card = (high G a I).card at h
  omega

theorem residual_card_split :
    (residual G a I).card =
      (overlap G a I).card + (middle G a I).card + (last G a I).card := by
  classical
  have h1 := Finset.card_sdiff_add_card_inter (residual G a I) (covered G (high G a I))
  have h2 := Finset.card_sdiff_add_card_inter
    (residual G a I ∩ covered G (high G a I)) (high G a I)
  have hi : (residual G a I ∩ covered G (high G a I)) ∩ high G a I =
      overlap G a I := by
    rw [Finset.inter_comm]
    exact covered_inter_high G a I
  rw [hi] at h2
  change (last G a I).card + _ = _ at h1
  change (middle G a I).card + _ = _ at h2
  omega

theorem output_card_split :
    (output G a I).card = (first G a I).card + (high G a I).card + (last G a I).card := by
  classical
  have hwU : Disjoint (first G a I) (last G a I) := by
    apply Finset.disjoint_left.mpr
    intro v hw hu
    exact Finset.disjoint_left.mp (residual_disjoint_first G a I)
      (last_subset G a I hu) hw
  unfold output
  rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hwU, (last_disjoint_high G a I).symm⟩),
    Finset.card_union_of_disjoint (high_disjoint_first G a I).symm]

theorem output_card_identity :
    ((output G a I).card : ℝ) = (first G a I).card + (residual G a I).card -
      (middle G a I).card + (outside G a I).card := by
  have h1 := high_card_split G a I
  have h2 := residual_card_split G a I
  have h3 := output_card_split G a I
  have hn : (output G a I).card + (middle G a I).card =
      (first G a I).card + (residual G a I).card + (outside G a I).card := by omega
  have hr : ((output G a I).card : ℝ) + (middle G a I).card =
      (first G a I).card + (residual G a I).card + (outside G a I).card := by
    exact_mod_cast hn
  linarith

/-- Exact closed-incidence double counting with an arbitrary candidate set. -/
theorem incidence_sum (S : Finset V) :
    (∑ r ∈ S, ∑ v ∈ closed G r ∩ I.candidates, I.x v) =
      ∑ v ∈ I.candidates, ((closed G v ∩ S).card : ℝ) * I.x v := by
  classical
  calc
    _ = ∑ r ∈ S, ∑ v ∈ I.candidates, if v ∈ closed G r then I.x v else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      have he : I.candidates.filter (fun v => v ∈ closed G r) = closed G r ∩ I.candidates := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_inter]
        tauto
      rw [← Finset.sum_filter, he]
    _ = ∑ v ∈ I.candidates, ∑ r ∈ S, if v ∈ closed G r then I.x v else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [closed_symm G v]
      have he : S.filter (fun r => r ∈ closed G v) = closed G v ∩ S := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_inter]
        tauto
      rw [← Finset.sum_filter, he]
      simp

theorem coverage_sum (S : Finset V) (hS : S ⊆ I.demands) :
    (S.card : ℝ) ≤ ∑ v ∈ I.candidates, ((closed G v ∩ S).card : ℝ) * I.x v := by
  rw [← incidence_sum G a I S]
  calc
    (S.card : ℝ) = ∑ _r ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun r hr => I.coverage r (hS hr))

/-- The density estimate is derived for the actual H,R,L sets, without
assuming the excess inequality or requiring the critical degree to be integral. -/
theorem excess_le (hden : Incidence.InducedDensityBound G a) :
    excess G a I + (a + 1) * (outside G a I).card ≤ a * (middle G a I).card := by
  classical
  have hinc := Incidence.closed_incidence_le_of_density G hden
    (high G a I) (residual G a I ∩ covered G (high G a I))
  have hsum : (∑ v ∈ high G a I,
      ((closed G v ∩ (residual G a I ∩ covered G (high G a I))).card : ℝ)) =
      ∑ v ∈ high G a I, (hits G a I v : ℝ) := by
    apply Finset.sum_congr rfl
    intro v hv
    have he : closed G v ∩ (residual G a I ∩ covered G (high G a I)) =
        closed G v ∩ residual G a I := by
      ext r
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨hc, hr, _⟩
        exact ⟨hc, hr⟩
      · rintro ⟨hc, hr⟩
        exact ⟨hc, hr, Finset.mem_biUnion.mpr ⟨v, hv, hc⟩⟩
    rw [he]
    rfl
  rw [hsum, covered_inter_high, covered_union_high,
    Finset.card_union_of_disjoint (high_middle_disjoint G a I)] at hinc
  have hcard : ((high G a I).card : ℝ) =
      (overlap G a I).card + (outside G a I).card := by
    exact_mod_cast high_card_split G a I
  have he : excess G a I = (∑ v ∈ high G a I, (hits G a I v : ℝ)) -
      (2 * a + 1) * (high G a I).card := by
    simp [excess, Finset.sum_sub_distrib, mul_comm]
    ring
  push_cast at hinc
  rw [hcard] at he hinc
  rw [he]
  nlinarith

theorem no_last_incidence {v : V} (hv : v ∈ first G a I ∪ high G a I) :
    closed G v ∩ last G a I = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hlast := (Finset.mem_inter.mp hr).2
  have hclosed := (Finset.mem_inter.mp hr).1
  rcases Finset.mem_union.mp hv with hw | hh
  · exact (Finset.mem_sdiff.mp (last_subset G a I hlast)).2
      (Finset.mem_biUnion.mpr ⟨v, hw, hclosed⟩)
  · exact (Finset.mem_sdiff.mp hlast).2
      (Finset.mem_biUnion.mpr ⟨v, hh, hclosed⟩)

theorem sum_over_subset (S : Finset V) (hS : S ⊆ I.candidates) (f : V → ℝ) :
    (∑ v ∈ S, f v) = ∑ v ∈ I.candidates, if v ∈ S then f v else 0 := by
  classical
  have he : I.candidates.filter (fun v => v ∈ S) = S := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨hS hv, hv⟩⟩
  rw [← Finset.sum_filter, he]

theorem leftover_bound :
    ((last G a I).card : ℝ) ≤ ∑ v ∈ other G a I, (hits G a I v : ℝ) * I.x v := by
  classical
  have hcov := coverage_sum G a I (last G a I)
    ((last_subset G a I).trans (residual_subset G a I))
  rw [sum_over_subset G a I (other G a I) (other_subset G a I)]
  refine hcov.trans (Finset.sum_le_sum ?_)
  intro v hvC
  by_cases hv : v ∈ other G a I
  · rw [if_pos hv]
    apply mul_le_mul_of_nonneg_right _ (I.nonneg v hvC)
    have hsub : closed G v ∩ last G a I ⊆ closed G v ∩ residual G a I :=
      Finset.inter_subset_inter_left (last_subset G a I)
    exact_mod_cast Finset.card_le_card hsub
  · rw [if_neg hv]
    have hwH : v ∈ first G a I ∪ high G a I := by
      by_contra hn
      exact hv (Finset.mem_sdiff.mpr ⟨hvC, hn⟩)
    rw [no_last_incidence G a I hwH]
    simp

theorem cost_decomposition
    (hhigh : ∀ v ∈ high G a I, I.c v = 2 * a + 1) :
    objective G a I =
      (2 * a + 1) * (∑ v ∈ first G a I, I.x v) +
      (∑ v ∈ I.candidates, (hits G a I v : ℝ) * I.x v) + slack G a I -
      (∑ v ∈ high G a I, ((hits G a I v : ℝ) - (2 * a + 1)) * I.x v) := by
  classical
  have hW : (2 * a + 1) * (∑ v ∈ first G a I, I.x v) =
      ∑ v ∈ I.candidates, if v ∈ first G a I then (2 * a + 1) * I.x v else 0 := by
    rw [Finset.mul_sum]
    exact sum_over_subset G a I _ (first_subset G a I) _
  have hP := sum_over_subset G a I (other G a I) (other_subset G a I)
    (fun v => (I.c v - (hits G a I v : ℝ)) * I.x v)
  have hE := sum_over_subset G a I (high G a I) (high_subset G a I)
    (fun v => ((hits G a I v : ℝ) - (2 * a + 1)) * I.x v)
  change slack G a I = _ at hP
  rw [hW, hP, hE, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  unfold objective
  apply Finset.sum_congr rfl
  intro v hvC
  by_cases hw : v ∈ first G a I
  · have hnH : v ∉ high G a I := fun hh =>
      Finset.disjoint_left.mp (high_disjoint_first G a I) hh hw
    have hnO : v ∉ other G a I := fun ho =>
      (Finset.mem_sdiff.mp ho).2 (Finset.mem_union_left _ hw)
    have hc := (Finset.mem_filter.mp hw).2.1
    simp [hw, hnH, hnO, hc, first_hits_zero G a I hw]
  · by_cases hh : v ∈ high G a I
    · have hnO : v ∉ other G a I := fun ho =>
        (Finset.mem_sdiff.mp ho).2 (Finset.mem_union_right _ hh)
      rw [if_neg hw, if_neg hnO, if_pos hh, hhigh v hh]
      ring
    · have ho : v ∈ other G a I := Finset.mem_sdiff.mpr
        ⟨hvC, by simpa only [Finset.mem_union, not_or] using And.intro hw hh⟩
      rw [if_neg hw, if_pos ho, if_neg hh]
      ring

theorem first_mass_lower :
    ((first G a I).card : ℝ) * (1 / (a + 1)) ≤ ∑ v ∈ first G a I, I.x v := by
  classical
  calc
    _ = ∑ _v ∈ first G a I, (1 / (a + 1)) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun v hv => le_of_lt (Finset.mem_filter.mp hv).2.2)

theorem high_weight
    (hhigh : ∀ v ∈ high G a I, I.c v = 2 * a + 1)
    {v : V} (hv : v ∈ high G a I) : I.x v ≤ 1 / (a + 1) := by
  classical
  have hvC := high_subset G a I hv
  have hnW := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
  by_contra hn
  exact hnW (Finset.mem_filter.mpr ⟨hvC, hhigh v hv, lt_of_not_ge hn⟩)

theorem weighted_excess_bound
    (hhigh : ∀ v ∈ high G a I, I.c v = 2 * a + 1) :
    (∑ v ∈ high G a I, ((hits G a I v : ℝ) - (2 * a + 1)) * I.x v) ≤
      excess G a I / (a + 1) := by
  classical
  rw [excess, Finset.sum_div]
  apply Finset.sum_le_sum
  intro v hv
  have hn : 0 ≤ (hits G a I v : ℝ) - (2 * a + 1) :=
    sub_nonneg.mpr (Finset.mem_filter.mp hv).2
  simpa only [mul_one_div] using
    mul_le_mul_of_nonneg_left (high_weight G a I hhigh hv) hn

theorem slack_nonneg
    (hother : ∀ v ∈ other G a I, (hits G a I v : ℝ) ≤ I.c v) : 0 ≤ slack G a I := by
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (sub_nonneg.mpr (hother v hv))
    (I.nonneg v (other_subset G a I hv))

theorem selection_saving (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a)
    (hhigh : ∀ v ∈ high G a I, I.c v = 2 * a + 1) :
    ((first G a I).card + (middle G a I).card : ℝ) / (a + 1) + slack G a I ≤
      objective G a I - (output G a I).card := by
  have hp : 0 < a + 1 := by linarith
  have hW := mul_le_mul_of_nonneg_left (first_mass_lower G a I)
    (show 0 ≤ 2 * a + 1 by linarith)
  have hR := coverage_sum G a I (residual G a I) (residual_subset G a I)
  change ((residual G a I).card : ℝ) ≤
    ∑ v ∈ I.candidates, (hits G a I v : ℝ) * I.x v at hR
  have hE := weighted_excess_bound G a I hhigh
  have hI := div_le_div_of_nonneg_right (excess_le G a I hden) (le_of_lt hp)
  have hcost := cost_decomposition G a I hhigh
  have hcard := output_card_identity G a I
  have hW' : (2 * a + 1) * (first G a I).card / (a + 1) ≤
      (2 * a + 1) * (∑ v ∈ first G a I, I.x v) := by
    simpa only [mul_one_div, mul_div_assoc] using hW
  have hexc : excess G a I ≤
      a * (middle G a I).card - (a + 1) * (outside G a I).card := by
    have h := excess_le G a I hden
    linarith
  have hI' := div_le_div_of_nonneg_right hexc (le_of_lt hp)
  have hbase : (2 * a + 1) * (first G a I).card / (a + 1) +
      (residual G a I).card + slack G a I -
      (a * (middle G a I).card - (a + 1) * (outside G a I).card) / (a + 1) ≤
      objective G a I := by linarith
  have heq : (2 * a + 1) * (first G a I).card / (a + 1) +
      (residual G a I).card + slack G a I -
      (a * (middle G a I).card - (a + 1) * (outside G a I).card) / (a + 1) =
      (first G a I).card + (residual G a I).card - (middle G a I).card +
      (outside G a I).card + a / (a + 1) * (first G a I).card +
      1 / (a + 1) * (middle G a I).card + slack G a I := by
    field_simp [ne_of_gt hp]
    ring
  have hcoef : 1 / (a + 1) ≤ a / (a + 1) :=
    div_le_div_of_nonneg_right ha (le_of_lt hp)
  have hfirst := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (first G a I).card)
  rw [heq] at hbase
  rw [hcard]
  have hdiv : ((first G a I).card + (middle G a I).card : ℝ) / (a + 1) =
      1 / (a + 1) * (first G a I).card + 1 / (a + 1) * (middle G a I).card := by
    ring
  rw [hdiv]
  linarith

/-- All conclusions of the current common rounding lemma, under exactly its
two supplementary cost hypotheses. The nonnegativity of P is also exposed. -/
theorem common_rounding (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a)
    (hhigh : ∀ v ∈ high G a I, I.c v = 2 * a + 1)
    (hother : ∀ v ∈ other G a I, (hits G a I v : ℝ) ≤ I.c v) :
    output G a I ⊆ I.candidates ∧
    I.demands ⊆ covered G (output G a I) ∧
    excess G a I + (a + 1) * (outside G a I).card ≤ a * (middle G a I).card ∧
    ((last G a I).card : ℝ) ≤ ∑ v ∈ other G a I, (hits G a I v : ℝ) * I.x v ∧
    ((first G a I).card + (middle G a I).card : ℝ) / (a + 1) + slack G a I ≤
      objective G a I - (output G a I).card ∧
    0 ≤ slack G a I := by
  exact ⟨output_subset G a I, output_covers G a I, excess_le G a I hden,
    leftover_bound G a I, selection_saving G a I ha hden hhigh,
    slack_nonneg G a I hother⟩

end Paper.CurrentRounding
