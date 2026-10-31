import Paper.Endpoints.Rounding.NoncriticalSaving

/-! Exact unfiltered geometry of `fv:imp:lemma`. The first set contains every
vertex above the threshold, independently of its degree. Integer hit cutoffs
are related explicitly to the paper's real critical value below.
The structural identities follow the existing noncritical proof patterns. -/
namespace Paper.ImprovedExcess
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (σ : ℝ) (x : V → ℝ)

noncomputable def first (_G : SimpleGraph V) (_k : ℕ) (σ : ℝ) (x : V → ℝ) : Finset V :=
  Finset.univ.filter (fun v => σ < x v)
noncomputable def residual : Finset V := Finset.univ \ covered G (first G k σ x)
noncomputable def hits (v : V) : ℕ := (closed G v ∩ residual G k σ x).card
noncomputable def high : Finset V := (Finset.univ \ first G k σ x).filter (fun v => k + 2 ≤ hits G k σ x v)
noncomputable def low : Finset V := (Finset.univ \ first G k σ x).filter (fun v => hits G k σ x v ≤ k + 1)
noncomputable def last : Finset V := residual G k σ x \ covered G (high G k σ x)
noncomputable def output : Finset V := first G k σ x ∪ high G k σ x ∪ last G k σ x

theorem residual_disjoint_first : Disjoint (residual G k σ x) (first G k σ x) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hw)

theorem high_disjoint_first : Disjoint (high G k σ x) (first G k σ x) := by
  exact Finset.disjoint_left.mpr (fun _ hv hw => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hw)

theorem last_subset_residual : last G k σ x ⊆ residual G k σ x := Finset.sdiff_subset

theorem last_disjoint_high : Disjoint (last G k σ x) (high G k σ x) := by
  apply Finset.disjoint_left.mpr
  intro v hv hh
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hh)

theorem first_hits_zero {v : V} (hv : v ∈ first G k σ x) : hits G k σ x v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hr).2).2
    (Finset.mem_biUnion.mpr ⟨v, hv, (Finset.mem_inter.mp hr).1⟩)

theorem hits_le_degree_succ (v : V) : hits G k σ x v ≤ G.degree v + 1 := by
  have h := Finset.card_le_card (Finset.inter_subset_left :
    closed G v ∩ residual G k σ x ⊆ closed G v)
  have he : (closed G v).card = G.degree v + 1 := by
    have heq : closed G v = insert v (G.neighborFinset v) := by
      ext u
      simp [mem_closed, SimpleGraph.mem_neighborFinset]
    rw [heq, Finset.card_insert_of_notMem (by simp)]
    rfl
  exact h.trans_eq he

theorem high_degree {v : V} (hv : v ∈ high G k σ x) : k + 1 ≤ G.degree v := by
  have hh := (Finset.mem_filter.mp hv).2
  have hn := hits_le_degree_succ G k σ x v
  omega

theorem high_weight {v : V} (hv : v ∈ high G k σ x) : x v ≤ σ := by
  by_contra hn
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hn⟩)

theorem first_mass_lower : σ * (first G k σ x).card ≤ ∑ v ∈ first G k σ x, x v := by
  calc
    _ = ∑ _v ∈ first G k σ x, σ := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun _ hv => le_of_lt (Finset.mem_filter.mp hv).2)

theorem output_dominates : dominates G (output G k σ x) := by
  have hW : first G k σ x ⊆ output G k σ x := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hH : high G k σ x ⊆ output G k σ x := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  intro v
  by_cases hw : v ∈ covered G (first G k σ x)
  · exact covered_mono G hW hw
  by_cases hh : v ∈ covered G (high G k σ x)
  · exact covered_mono G hH hh
  apply subset_covered G _
  exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, hh⟩)

noncomputable def overlap : Finset V := high G k σ x ∩ residual G k σ x
noncomputable def outside : Finset V := high G k σ x \ residual G k σ x
noncomputable def middle : Finset V :=
  (residual G k σ x ∩ covered G (high G k σ x)) \ high G k σ x

theorem high_middle_disjoint : Disjoint (high G k σ x) (middle G k σ x) := by
  classical
  exact Finset.disjoint_left.mpr (fun v hv hm => (Finset.mem_sdiff.mp hm).2 hv)

theorem covered_inter_high :
    high G k σ x ∩ (residual G k σ x ∩ covered G (high G k σ x)) = overlap G k σ x := by
  classical
  ext v
  simp only [Finset.mem_inter, overlap]
  constructor
  · rintro ⟨hh, hr, _⟩
    exact ⟨hh, hr⟩
  · rintro ⟨hh, hr⟩
    exact ⟨hh, hr, subset_covered G _ hh⟩

theorem covered_union_high :
    high G k σ x ∪ (residual G k σ x ∩ covered G (high G k σ x)) =
      high G k σ x ∪ middle G k σ x := by
  classical
  ext v
  simp only [Finset.mem_union, Finset.mem_inter, middle, Finset.mem_sdiff]
  tauto

theorem high_card_split :
    (high G k σ x).card = (overlap G k σ x).card + (outside G k σ x).card := by
  have h := Finset.card_sdiff_add_card_inter (high G k σ x) (residual G k σ x)
  change (outside G k σ x).card + (overlap G k σ x).card = (high G k σ x).card at h
  omega

theorem residual_card_split :
    (residual G k σ x).card =
      (overlap G k σ x).card + (middle G k σ x).card + (last G k σ x).card := by
  classical
  have h1 := Finset.card_sdiff_add_card_inter (residual G k σ x) (covered G (high G k σ x))
  have h2 := Finset.card_sdiff_add_card_inter
    (residual G k σ x ∩ covered G (high G k σ x)) (high G k σ x)
  have hi : (residual G k σ x ∩ covered G (high G k σ x)) ∩ high G k σ x =
      overlap G k σ x := by
    rw [Finset.inter_comm]
    exact covered_inter_high G k σ x
  rw [hi] at h2
  change (last G k σ x).card + _ = _ at h1
  change (middle G k σ x).card + _ = _ at h2
  omega

theorem output_card_split :
    (output G k σ x).card =
      (first G k σ x).card + (high G k σ x).card + (last G k σ x).card := by
  classical
  have hwU : Disjoint (first G k σ x) (last G k σ x) := by
    apply Finset.disjoint_left.mpr
    intro v hw hu
    exact Finset.disjoint_left.mp (residual_disjoint_first G k σ x)
      (last_subset_residual G k σ x hu) hw
  have hhU := (last_disjoint_high G k σ x).symm
  have hwH := (high_disjoint_first G k σ x).symm
  unfold ImprovedExcess.output
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hwU, hhU⟩),
    Finset.card_union_of_disjoint hwH]

theorem output_card_identity :
    ((output G k σ x).card : ℝ) = (first G k σ x).card +
      (residual G k σ x).card - (middle G k σ x).card + (outside G k σ x).card := by
  have h1 := high_card_split G k σ x
  have h2 := residual_card_split G k σ x
  have h3 := output_card_split G k σ x
  have hnat : (output G k σ x).card + (middle G k σ x).card =
      (first G k σ x).card + (residual G k σ x).card + (outside G k σ x).card := by omega
  have hr : ((output G k σ x).card : ℝ) + (middle G k σ x).card =
      (first G k σ x).card + (residual G k σ x).card + (outside G k σ x).card := by
    exact_mod_cast hnat
  linarith


noncomputable def excess (a : ℝ) : ℝ := ∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1))

theorem excess_lower (a θ : ℝ) (heq : 2 * a = k + θ) :
    (1 - θ) * (high G k σ x).card ≤ excess G k σ x a := by
  calc
    _ = ∑ _v ∈ high G k σ x, (1 - θ) := by simp [mul_comm]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v hv
      have hh : ((k + 2 : ℕ) : ℝ) ≤ hits G k σ x v := by
        exact_mod_cast (Finset.mem_filter.mp hv).2
      push_cast at hh
      linarith

theorem weighted_excess (a θ : ℝ) (heq : 2 * a = k + θ) (hθ : θ < 1) :
    (∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v) ≤
      σ * excess G k σ x a := by
  rw [excess, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hh : ((k + 2 : ℕ) : ℝ) ≤ hits G k σ x v := by
    exact_mod_cast (Finset.mem_filter.mp hv).2
  push_cast at hh
  have hn : 0 ≤ (hits G k σ x v : ℝ) - (2 * a + 1) := by linarith
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (high_weight G k σ x hv) hn

noncomputable def slack (a : ℝ) : ℝ :=
  ∑ v ∈ low G k σ x, ((2 * a + 1) - (hits G k σ x v : ℝ)) * x v

theorem low_coefficient (a θ : ℝ) (heq : 2 * a = k + θ) {v : V} (hv : v ∈ low G k σ x) :
    θ ≤ (2 * a + 1) - (hits G k σ x v : ℝ) := by
  have hh : (hits G k σ x v : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Finset.mem_filter.mp hv).2
  push_cast at hh
  linarith

theorem high_low_disjoint : Disjoint (high G k σ x) (low G k σ x) := by
  apply Finset.disjoint_left.mpr
  intro v hh hl
  have h1 := (Finset.mem_filter.mp hh).2
  have h2 := (Finset.mem_filter.mp hl).2
  omega

theorem low_not_first {v : V} (hv : v ∈ low G k σ x) : v ∉ first G k σ x :=
  (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2

theorem low_of_not {v : V} (hw : v ∉ first G k σ x) (hh : v ∉ high G k σ x) : v ∈ low G k σ x := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, ?_⟩
  have hn : ¬ k + 2 ≤ hits G k σ x v := fun h =>
    hh (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, h⟩)
  omega

theorem sum_partition : (∑ v, x v) =
    (∑ v ∈ first G k σ x, x v) + (∑ v ∈ high G k σ x, x v) + (∑ v ∈ low G k σ x, x v) := by
  have he : ∀ v, x v = (if v ∈ first G k σ x then x v else 0) +
      (if v ∈ high G k σ x then x v else 0) + (if v ∈ low G k σ x then x v else 0) := by
    intro v
    by_cases hw : v ∈ first G k σ x
    · have hh : v ∉ high G k σ x := fun h => Finset.disjoint_left.mp (high_disjoint_first G k σ x) h hw
      have hl : v ∉ low G k σ x := fun h => low_not_first G k σ x h hw
      simp only [if_pos hw, if_neg hh, if_neg hl, add_zero]
    · by_cases hh : v ∈ high G k σ x
      · have hl : v ∉ low G k σ x := fun h => Finset.disjoint_left.mp (high_low_disjoint G k σ x) hh h
        simp only [if_neg hw, if_pos hh, if_neg hl, zero_add, add_zero]
      · simp only [if_neg hw, if_neg hh, if_pos (low_of_not G k σ x hw hh), zero_add]
  calc
    _ = ∑ v, ((if v ∈ first G k σ x then x v else 0) +
      (if v ∈ high G k σ x then x v else 0) + (if v ∈ low G k σ x then x v else 0)) :=
      Finset.sum_congr rfl (fun v _ => he v)
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem low_mass (a θ : ℝ) (heq : 2 * a = k + θ) (hx : ∀ v, 0 ≤ x v) :
    θ * (∑ v ∈ low G k σ x, x v) ≤ slack G k σ x a := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_right (low_coefficient G k σ x a θ heq hv) (hx v))

theorem cost_decomposition (a : ℝ) :
    (2 * a + 1) * (∑ v, x v) = (2 * a + 1) * (∑ v ∈ first G k σ x, x v) +
      (∑ v, (hits G k σ x v : ℝ) * x v) + slack G k σ x a -
      (∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v) := by
  have hw : (2 * a + 1) * (∑ v ∈ first G k σ x, x v) =
      ∑ v, if v ∈ first G k σ x then (2 * a + 1) * x v else 0 := by simp [Finset.mul_sum]
  have hp : slack G k σ x a = ∑ v, if v ∈ low G k σ x then
      ((2 * a + 1) - (hits G k σ x v : ℝ)) * x v else 0 := by simp [slack]
  have he : (∑ v ∈ high G k σ x, ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v) =
      ∑ v, if v ∈ high G k σ x then ((hits G k σ x v : ℝ) - (2 * a + 1)) * x v else 0 := by simp
  rw [hw, hp, he, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hW : v ∈ first G k σ x
  · have hH : v ∉ high G k σ x := fun h => Finset.disjoint_left.mp (high_disjoint_first G k σ x) h hW
    have hL : v ∉ low G k σ x := fun h => low_not_first G k σ x h hW
    simp only [if_pos hW, if_neg hH, if_neg hL, first_hits_zero G k σ x hW,
      Nat.cast_zero, zero_mul, add_zero, sub_zero]
  · rw [if_neg hW]
    by_cases hH : v ∈ high G k σ x
    · have hL : v ∉ low G k σ x := fun h => Finset.disjoint_left.mp (high_low_disjoint G k σ x) hH h
      rw [if_pos hH, if_neg hL]
      ring
    · rw [if_neg hH, if_pos (low_of_not G k σ x hW hH)]
      ring

theorem residual_coverage (hx : PartialOptimum.Feasible G Finset.univ x) :
    ((residual G k σ x).card : ℝ) ≤ ∑ v, (hits G k σ x v : ℝ) * x v := by
  change ((residual G k σ x).card : ℝ) ≤ ∑ v, ((closed G v ∩ residual G k σ x).card : ℝ) * x v
  rw [← WeightedBudget.incidence_sum]
  calc
    _ = ∑ _r ∈ residual G k σ x, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun r _ => hx.2 r (Finset.mem_univ _))

theorem first_iff (v : V) : v ∈ first G k σ x ↔ σ < x v := by
  classical
  simp only [first, Finset.mem_filter, Finset.mem_univ, true_and]

theorem high_iff (a θ : ℝ) (heq : 2 * a = k + θ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (v : V) : v ∈ high G k σ x ↔
      v ∉ first G k σ x ∧ 2 * a + 1 ≤ (hits G k σ x v : ℝ) := by
  classical
  simp only [high, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hw, hh⟩
    refine ⟨hw, ?_⟩
    have hr : ((k + 2 : ℕ) : ℝ) ≤ hits G k σ x v := by exact_mod_cast hh
    push_cast at hr
    linarith
  · rintro ⟨hw, hh⟩
    refine ⟨hw, ?_⟩
    by_contra hn
    have hle : hits G k σ x v ≤ k + 1 := by omega
    have hr : (hits G k σ x v : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hle
    linarith

theorem low_eq_other : low G k σ x = Finset.univ \ (first G k σ x ∪ high G k σ x) := by
  classical
  ext v
  constructor
  · intro hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro h
      rcases Finset.mem_union.mp h with hw | hh
      · exact low_not_first G k σ x hv hw
      · exact Finset.disjoint_left.mp (high_low_disjoint G k σ x) hh hv⟩
  · intro hv
    have hn := (Finset.mem_sdiff.mp hv).2
    exact low_of_not G k σ x (fun h => hn (Finset.mem_union_left _ h))
      (fun h => hn (Finset.mem_union_right _ h))

end Paper.ImprovedExcess
#print axioms Paper.ImprovedExcess.output_card_identity
#print axioms Paper.ImprovedExcess.high_iff
#print axioms Paper.ImprovedExcess.cost_decomposition
