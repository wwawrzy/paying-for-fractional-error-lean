import Paper.Endpoints.Rounding.WeightedBudget

/-!
The current `simp:endpoint:budget`, with exactly F = V \ N[B].
`WeightedBudget.far` uses V \ N²[B], so it cannot be substituted for F.
The current residual LP is encoded as a cover instance with candidates V \ F
and zero coordinates elsewhere. Its budget is derived using the existing
closed-incidence double count, without assuming an attained optimum.
-/

namespace Paper.CurrentBudget

open SevenFoundation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

/-- The candidates V \ F = N[B] of the current paper. -/
def candidates : Finset V := covered G (WeightedBudget.defects G d)

/-- Exactly the current F, not the earlier distance-two regular region. -/
def selected : Finset V := Finset.univ \ candidates G d

def demands : Finset V := Finset.univ \ covered G (selected G d)

noncomputable def boundaryCost (v : V) : ℝ :=
  (d + 1 : ℕ) - ((closed G v ∩ selected G d).card : ℝ)

theorem selected_degree {v : V} (hv : v ∈ selected G d) : G.degree v = d := by
  by_contra hdeg
  have hvB : v ∈ WeightedBudget.defects G d := by
    simp [WeightedBudget.defects, hdeg]
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hvB)

theorem defects_subset_demands : WeightedBudget.defects G d ⊆ demands G d := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
  intro hc
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hc
  exact (Finset.mem_sdiff.mp hu).2
    (Finset.mem_biUnion.mpr ⟨v, hv, (closed_symm G v u).mp hvu⟩)

theorem demand_closed_subset_candidates {r : V} (hr : r ∈ demands G d) :
    closed G r ⊆ candidates G d := by
  intro v hv
  by_contra hn
  have hvF : v ∈ selected G d := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hn⟩
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_biUnion.mpr ⟨v, hvF, (closed_symm G v r).mp hv⟩)

theorem demands_subset_candidates : demands G d ⊆ candidates G d := by
  intro r hr
  exact demand_closed_subset_candidates G d hr (self_mem_closed G r)

theorem touches_selected_degree {v : V}
    (hv : (closed G v ∩ selected G d).Nonempty) : G.degree v = d := by
  obtain ⟨u, hu⟩ := hv
  by_contra hdeg
  have hvB : v ∈ WeightedBudget.defects G d := by
    simp [WeightedBudget.defects, hdeg]
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2
    (Finset.mem_biUnion.mpr ⟨v, hvB, (Finset.mem_inter.mp hu).1⟩)

theorem closed_inter_selected_subset_neighbors {v : V} (hv : v ∈ candidates G d) :
    closed G v ∩ selected G d ⊆ G.neighborFinset v := by
  intro u hu
  rcases (mem_closed G u v).mp (Finset.mem_inter.mp hu).1 with heq | hadj
  · subst u
    exact False.elim ((Finset.mem_sdiff.mp (Finset.mem_inter.mp hu).2).2 hv)
  · simpa only [SimpleGraph.mem_neighborFinset] using hadj

/-- The closed-neighborhood definition equals the current open-neighborhood cost. -/
theorem cost_eq_open (v : V) (hv : v ∈ candidates G d) :
    boundaryCost G d v =
      (d + 1 : ℕ) - ((G.neighborFinset v ∩ selected G d).card : ℝ) := by
  have he : closed G v ∩ selected G d = G.neighborFinset v ∩ selected G d := by
    apply Finset.Subset.antisymm
    · intro u hu
      exact Finset.mem_inter.mpr
        ⟨closed_inter_selected_subset_neighbors G d hv hu, (Finset.mem_inter.mp hu).2⟩
    · intro u hu
      exact Finset.mem_inter.mpr
        ⟨(mem_closed G u v).mpr (Or.inr (by
          simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hu).1)),
          (Finset.mem_inter.mp hu).2⟩
  unfold boundaryCost
  rw [he]

theorem boundary_card_le {v : V} (hv : v ∈ candidates G d) :
    (closed G v ∩ selected G d).card ≤ d := by
  by_cases hz : (closed G v ∩ selected G d).card = 0
  · omega
  have hdeg := touches_selected_degree G d (Finset.card_pos.mp (Nat.pos_of_ne_zero hz))
  have hc := Finset.card_le_card (closed_inter_selected_subset_neighbors G d hv)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, hdeg] using hc

theorem cost_integral_bounds {v : V} (hv : v ∈ candidates G d) :
    (∃ n : ℕ, boundaryCost G d v = (n : ℝ)) ∧
      1 ≤ boundaryCost G d v ∧ boundaryCost G d v ≤ (d + 1 : ℕ) := by
  have hc := boundary_card_le G d hv
  have hcR : ((closed G v ∩ selected G d).card : ℝ) ≤ d := by exact_mod_cast hc
  have hn : (0 : ℝ) ≤ ((closed G v ∩ selected G d).card : ℝ) := Nat.cast_nonneg _
  refine ⟨⟨d + 1 - (closed G v ∩ selected G d).card, ?_⟩, ?_, ?_⟩
  · unfold boundaryCost
    rw [Nat.cast_sub (by omega)]
  · unfold boundaryCost
    push_cast
    linarith
  · unfold boundaryCost
    linarith

theorem full_cost_iff {v : V} :
    boundaryCost G d v = (d + 1 : ℕ) ↔ v ∈ demands G d := by
  constructor
  · intro hc
    have hzR : ((closed G v ∩ selected G d).card : ℝ) = 0 := by
      unfold boundaryCost at hc
      linarith
    have hz : (closed G v ∩ selected G d).card = 0 := by exact_mod_cast hzR
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hcov
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hcov
    have hpos := Finset.card_pos.mpr
      ⟨u, Finset.mem_inter.mpr ⟨(closed_symm G v u).mp hvu, hu⟩⟩
    omega
  · intro hv
    have he : closed G v ∩ selected G d = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr
        ⟨u, (Finset.mem_inter.mp hu).2,
          (closed_symm G u v).mp (Finset.mem_inter.mp hu).1⟩)
    simp only [boundaryCost, he, Finset.card_empty, Nat.cast_zero, sub_zero]

theorem cheap_degree_and_not_demand {v : V}
    (hc : boundaryCost G d v < (d + 1 : ℕ)) :
    G.degree v = d ∧ v ∉ demands G d := by
  have hpR : (0 : ℝ) < ((closed G v ∩ selected G d).card : ℝ) := by
    unfold boundaryCost at hc
    linarith
  have hp : 0 < (closed G v ∩ selected G d).card := by exact_mod_cast hpR
  refine ⟨touches_selected_degree G d (Finset.card_pos.mp hp), ?_⟩
  intro hv
  exact (ne_of_lt hc) ((full_cost_iff G d).mpr hv)

theorem cheap_closed_card {v : V} (hv : v ∈ candidates G d)
    (hc : boundaryCost G d v < (d + 1 : ℕ)) :
    ((closed G v ∩ demands G d).card : ℝ) ≤ boundaryCost G d v - 1 := by
  obtain ⟨hdeg, hnR⟩ := cheap_degree_and_not_demand G d hc
  have hR : closed G v ∩ demands G d ⊆ G.neighborFinset v := by
    intro u hu
    rcases (mem_closed G u v).mp (Finset.mem_inter.mp hu).1 with heq | hadj
    · subst u
      exact False.elim (hnR (Finset.mem_inter.mp hu).2)
    · simpa only [SimpleGraph.mem_neighborFinset] using hadj
  have hdis : Disjoint (closed G v ∩ demands G d) (closed G v ∩ selected G d) := by
    apply Finset.disjoint_left.mpr
    intro u huR huF
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp huR).2).2
      (subset_covered G _ (Finset.mem_inter.mp huF).2)
  have hsub : (closed G v ∩ demands G d) ∪ (closed G v ∩ selected G d) ⊆
      G.neighborFinset v := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hR hu
    · exact closed_inter_selected_subset_neighbors G d hv hu
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, SimpleGraph.card_neighborFinset_eq_degree, hdeg] at hcard
  have hcardR : ((closed G v ∩ demands G d).card : ℝ) +
      ((closed G v ∩ selected G d).card : ℝ) ≤ d := by exact_mod_cast hcard
  unfold boundaryCost
  push_cast
  linarith

noncomputable def auxiliary : CoverInstance V where
  demands := demands G d
  candidates := candidates G d
  eligible := fun r => closed G r ∩ candidates G d
  eligible_subset := by intros; exact Finset.inter_subset_right
  cost := fun v => if v ∈ candidates G d then boundaryCost G d v else 0
  cost_nonneg := by
    intro v
    split_ifs with hv
    · exact zero_le_one.trans (cost_integral_bounds G d hv).2.1
    · exact le_refl _

noncomputable def restrict (y : V → ℝ) (v : V) : ℝ :=
  if v ∈ candidates G d then y v else 0

theorem restrict_feasible (y : V → ℝ) (hy : feasible (ordinary G) y) :
    feasible (auxiliary G d) (restrict G d y) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp [restrict]
    split_ifs <;> first | exact hy.1 v | exact le_refl _
  · intro v hv
    change v ∉ candidates G d at hv
    simp [restrict, hv]
  · intro r hr
    change r ∈ demands G d at hr
    have hsub := demand_closed_subset_candidates G d hr
    change 1 ≤ ∑ v ∈ closed G r ∩ candidates G d, restrict G d y v
    rw [Finset.inter_eq_left.mpr hsub]
    have he : (∑ v ∈ closed G r, restrict G d y v) = ∑ v ∈ closed G r, y v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [restrict, hsub hv]
    rw [he]
    exact hy.2.2 r (Finset.mem_univ _)

theorem restricted_cost (y : V → ℝ) :
    cost (auxiliary G d) (restrict G d y) =
      ∑ v ∈ candidates G d, boundaryCost G d v * y v := by
  classical
  simp [cost, auxiliary, restrict]

theorem weighted_budget (y : V → ℝ) (hy : feasible (ordinary G) y) :
    ((selected G d).card : ℝ) +
        ∑ v ∈ candidates G d, boundaryCost G d v * y v ≤
      (d + 1 : ℕ) * ∑ v, y v := by
  classical
  have hC : (∑ v ∈ candidates G d, boundaryCost G d v * y v) =
      ∑ v, if v ∈ candidates G d then boundaryCost G d v * y v else 0 := by simp
  calc
    _ ≤ (∑ v, ((closed G v ∩ selected G d).card : ℝ) * y v) +
          ∑ v ∈ candidates G d, boundaryCost G d v * y v :=
      add_le_add (WeightedBudget.coverage_sum G (selected G d) y hy) le_rfl
    _ = ∑ v, (((closed G v ∩ selected G d).card : ℝ) * y v +
        if v ∈ candidates G d then boundaryCost G d v * y v else 0) := by
      rw [hC, Finset.sum_add_distrib]
    _ ≤ ∑ v, (d + 1 : ℕ) * y v := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ candidates G d
      · simp only [if_pos hv, boundaryCost]
        nlinarith
      · simp only [if_neg hv, add_zero]
        apply mul_le_mul_of_nonneg_right _ (hy.1 v)
        have hcard := Finset.card_le_card (Finset.inter_subset_left :
          closed G v ∩ selected G d ⊆ closed G v)
        have hvF : v ∈ selected G d := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩
        rw [WeightedBudget.closed_card G v, selected_degree G d hvF] at hcard
        exact_mod_cast hcard
    _ = (d + 1 : ℕ) * ∑ v, y v := (Finset.mul_sum _ _ _).symm

def auxiliaryFeasibleCosts : Set ℝ :=
  {t | ∃ x, feasible (auxiliary G d) x ∧ cost (auxiliary G d) x = t}

noncomputable def auxiliaryNumber : ℝ := sInf (auxiliaryFeasibleCosts G d)

theorem auxiliaryFeasibleCosts_nonempty : (auxiliaryFeasibleCosts G d).Nonempty := by
  obtain ⟨a, y, hy, _⟩ := feasibleCosts_nonempty G
  exact ⟨_, restrict G d y, restrict_feasible G d y hy, rfl⟩

theorem auxiliaryFeasibleCosts_bddBelow : BddBelow (auxiliaryFeasibleCosts G d) := by
  refine ⟨0, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact cost_nonneg_of_feasible _ _ hx

theorem auxiliaryNumber_le_restricted_cost (y : V → ℝ)
    (hy : feasible (ordinary G) y) :
    auxiliaryNumber G d ≤ ∑ v ∈ candidates G d, boundaryCost G d v * y v := by
  apply csInf_le (auxiliaryFeasibleCosts_bddBelow G d)
  exact ⟨restrict G d y, restrict_feasible G d y hy, restricted_cost G d y⟩

theorem auxiliary_budget (y : V → ℝ) (hy : feasible (ordinary G) y) :
    ((selected G d).card : ℝ) + auxiliaryNumber G d ≤ (d + 1 : ℕ) * ∑ v, y v :=
  le_trans (add_le_add le_rfl (auxiliaryNumber_le_restricted_cost G d y hy))
    (weighted_budget G d y hy)

theorem fractional_budget :
    ((selected G d).card : ℝ) + auxiliaryNumber G d ≤
      (d + 1 : ℕ) * fractionalNumber G := by
  have hb : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  have hlow : (((selected G d).card : ℝ) + auxiliaryNumber G d) / (d + 1 : ℕ) ≤
      fractionalNumber G := by
    apply le_csInf (feasibleCosts_nonempty G)
    rintro a ⟨y, hy, rfl⟩
    apply (div_le_iff₀ hb).mpr
    simpa only [ordinary_cost, mul_comm] using auxiliary_budget G d y hy
  exact (div_le_iff₀ hb).mp hlow |>.trans_eq (mul_comm _ _)

/-- All three clauses of the current `simp:endpoint:budget`, with its own
F, R₀, integer candidate costs, and the actual residual covering optimum. -/
theorem current_budget :
    WeightedBudget.defects G d ⊆ demands G d ∧
    (∀ v ∈ candidates G d,
      (∃ n : ℕ, boundaryCost G d v = (n : ℝ)) ∧
      1 ≤ boundaryCost G d v ∧ boundaryCost G d v ≤ (d + 1 : ℕ) ∧
      (boundaryCost G d v = (d + 1 : ℕ) ↔ v ∈ demands G d) ∧
      (boundaryCost G d v < (d + 1 : ℕ) →
        ((closed G v ∩ demands G d).card : ℝ) ≤ boundaryCost G d v - 1)) ∧
    ((selected G d).card : ℝ) + auxiliaryNumber G d ≤
      (d + 1 : ℕ) * fractionalNumber G := by
  refine ⟨defects_subset_demands G d, ?_, fractional_budget G d⟩
  intro v hv
  obtain ⟨hint, hlo, hhi⟩ := cost_integral_bounds G d hv
  exact ⟨hint, hlo, hhi, full_cost_iff G d, cheap_closed_card G d hv⟩

end Paper.CurrentBudget
