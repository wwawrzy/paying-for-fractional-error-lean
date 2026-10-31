import Paper.TotalDomination.Rounding

/-! The cost identity and saving in `fv:total:rounding`. The vector is
supported on the candidate set. R1--R3 are local cost and weight conditions;
the output bound is derived from the actual selection and graph density. -/

namespace Paper.TotalDomination

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (I : Input G)

noncomputable def other : Finset V := I.candidates \ (first G I ∪ high G I)

noncomputable def objective (c : V → ℝ) : ℝ := ∑ v ∈ I.candidates, c v * I.x v

noncomputable def penalty (c : V → ℝ) : ℝ :=
  ∑ v ∈ other G I, (c v - (hits G I v : ℝ)) * I.x v

noncomputable def oversupply : ℝ :=
  ∑ r ∈ residual G I, ((∑ v ∈ G.neighborFinset r, I.x v) - 1)

theorem high_disjoint_first : Disjoint (high G I) (first G I) := by
  classical
  exact Finset.disjoint_left.mpr fun v hv hw =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hw

/-- A first-step vertex has no open incidence to a residual demand. This
does not assert that the vertex itself is absent from the residual set. -/
theorem first_hits_zero {v : V} (hv : v ∈ first G I) : hits G I v = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨ha, hR⟩ := Finset.mem_inter.mp hr
  exact (Finset.mem_sdiff.mp hR).2 ((mem_neighbors G).mpr
    ⟨v, hv, ((G.mem_neighborFinset v r).mp ha).symm⟩)

/-- Weighted double counting of open incidences, with the self terms absent. -/
theorem open_incidence_sum (S : Finset V) :
    (∑ r ∈ S, ∑ v ∈ G.neighborFinset r, I.x v) =
      ∑ v, ((G.neighborFinset v ∩ S).card : ℝ) * I.x v := by
  classical
  calc
    _ = ∑ r ∈ S, ∑ v, if G.Adj r v then I.x v else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp
    _ = ∑ v, ∑ r ∈ S, if G.Adj r v then I.x v else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [G.adj_comm _ v]
      rw [← Finset.sum_filter]
      have he : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact and_comm
      rw [he]
      simp

theorem residual_mass_identity :
    (∑ v, (hits G I v : ℝ) * I.x v) = (residual G I).card + oversupply G I := by
  simp only [hits]
  rw [← open_incidence_sum G I (residual G I)]
  unfold oversupply
  rw [Finset.sum_sub_distrib]
  simp

theorem penalty_nonneg (c : V → ℝ)
    (hx : ∀ v ∈ I.candidates, 0 ≤ I.x v)
    (hR2 : ∀ v ∈ other G I, (hits G I v : ℝ) ≤ c v) :
    0 ≤ penalty G I c := by
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (sub_nonneg.mpr (hR2 v hv))
    (hx v (Finset.mem_sdiff.mp hv).1)

theorem oversupply_nonneg
    (hcover : ∀ r ∈ I.demands, 1 ≤ ∑ v ∈ G.neighborFinset r, I.x v) :
    0 ≤ oversupply G I := by
  apply Finset.sum_nonneg
  intro r hr
  exact sub_nonneg.mpr (hcover r (Finset.mem_sdiff.mp hr).1)

/-- Exact bookkeeping before either density or the threshold bound is used. -/
theorem cost_decomposition (a : ℝ) (c : V → ℝ)
    (hsupport : ∀ v ∉ I.candidates, I.x v = 0)
    (hR1 : ∀ v ∈ first G I ∪ high G I, c v = 2 * a) :
    objective G I c =
      2 * a * (∑ v ∈ first G I, I.x v) +
      (residual G I).card + oversupply G I + penalty G I c -
      (∑ v ∈ high G I, ((hits G I v : ℝ) - 2 * a) * I.x v) := by
  classical
  have hcost : objective G I c = ∑ v, c v * I.x v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    rw [hsupport v hv, mul_zero]
  have hpoint : (∑ v, c v * I.x v) =
      ∑ v, ((if v ∈ first G I then 2 * a * I.x v else 0) +
        (hits G I v : ℝ) * I.x v +
        (if v ∈ other G I then (c v - (hits G I v : ℝ)) * I.x v else 0) -
        (if v ∈ high G I then ((hits G I v : ℝ) - 2 * a) * I.x v else 0)) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hw : v ∈ first G I
    · have hnH : v ∉ high G I := fun hh =>
        Finset.disjoint_left.mp (high_disjoint_first G I) hh hw
      have hnO : v ∉ other G I := fun ho =>
        (Finset.mem_sdiff.mp ho).2 (Finset.mem_union_left _ hw)
      simp [hw, hnH, hnO, hR1 v (Finset.mem_union_left _ hw), first_hits_zero G I hw]
    · by_cases hh : v ∈ high G I
      · have hnO : v ∉ other G I := fun ho =>
          (Finset.mem_sdiff.mp ho).2 (Finset.mem_union_right _ hh)
        rw [if_neg hw, if_neg hnO, if_pos hh, hR1 v (Finset.mem_union_right _ hh)]
        ring
      · by_cases hv : v ∈ I.candidates
        · have ho : v ∈ other G I :=
            Finset.mem_sdiff.mpr ⟨hv, by simpa only [Finset.mem_union, not_or] using ⟨hw, hh⟩⟩
          rw [if_neg hw, if_pos ho, if_neg hh]
          ring
        · simp [hsupport v hv]
  rw [hcost, hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_mem_eq]
  rw [← Finset.mul_sum, residual_mass_identity G I]
  unfold penalty
  ring

/-- R3 is needed only for a strictly positive excess term. -/
theorem weighted_excess_le (a : ℝ) (hcutoff : 2 * a ≤ I.cutoff)
    (hR3 : ∀ v ∈ high G I, 2 * a < (hits G I v : ℝ) → I.x v ≤ I.threshold) :
    (∑ v ∈ high G I, ((hits G I v : ℝ) - 2 * a) * I.x v) ≤
      I.threshold * excess G I a := by
  classical
  rw [excess, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hn : (I.cutoff : ℝ) ≤ hits G I v := by
    exact_mod_cast (Finset.mem_filter.mp hv).2
  have hdeg := hcutoff.trans hn
  by_cases he : (hits G I v : ℝ) = 2 * a
  · simp [he]
  · have hx := hR3 v hv (lt_of_le_of_ne hdeg (Ne.symm he))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hdeg)

/-- The saving inequality of `fv:total:rounding`, together with the two
nonnegative budgets. No approximation guarantee is assumed. -/
theorem rounding_saving (a : ℝ) (ha : 0 ≤ a)
    (hdensity : Incidence.InducedDensityBound G a)
    (hcutoff : 2 * a ≤ I.cutoff) (ht : 0 < I.threshold) (c : V → ℝ)
    (hx : ∀ v ∈ I.candidates, 0 ≤ I.x v)
    (hsupport : ∀ v ∉ I.candidates, I.x v = 0)
    (hcover : ∀ r ∈ I.demands, 1 ≤ ∑ v ∈ G.neighborFinset r, I.x v)
    (hR1 : ∀ v ∈ first G I ∪ high G I, c v = 2 * a)
    (hR2 : ∀ v ∈ other G I, (hits G I v : ℝ) ≤ c v)
    (hR3 : ∀ v ∈ high G I, 2 * a < (hits G I v : ℝ) → I.x v ≤ I.threshold) :
    0 ≤ penalty G I c ∧ 0 ≤ oversupply G I ∧
      (2 * a * I.threshold - 1) * (first G I).card +
        (1 - a * I.threshold) * surplus G I + penalty G I c + oversupply G I ≤
      objective G I c - (output G I).card := by
  classical
  refine ⟨penalty_nonneg G I c hx hR2, oversupply_nonneg G I hcover, ?_⟩
  have hfirst : I.threshold * (first G I).card ≤ ∑ v ∈ first G I, I.x v := by
    calc
      _ = ∑ _v ∈ first G I, I.threshold := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2.le
  have hw := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2 * a by positivity)
  have hweighted := weighted_excess_le G I a hcutoff hR3
  have hE := mul_le_mul_of_nonneg_left (excess_le G I a hdensity) ht.le
  have hcost := cost_decomposition G I a c hsupport hR1
  have hcard := output_card_le G I
  nlinarith only [hw, hweighted, hE, hcost, hcard]

end Paper.TotalDomination

#print axioms Paper.TotalDomination.first_hits_zero
#print axioms Paper.TotalDomination.open_incidence_sum
#print axioms Paper.TotalDomination.cost_decomposition
#print axioms Paper.TotalDomination.weighted_excess_le
#print axioms Paper.TotalDomination.rounding_saving
