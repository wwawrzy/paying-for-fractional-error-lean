import Paper.Preliminaries.SevenFoundation

/-!
# The graph-level weighted budget for the covering paper

This proves the weighted-budget subsection of the self-contained draft for any
finite simple graph and any natural critical degree. No density, planarity,
fractional solver, optimum attainment, or incidence inequality is assumed.
-/

namespace Paper.WeightedBudget

open SevenFoundation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

def defects : Finset V := Finset.univ.filter (fun v => G.degree v ≠ d)
def zone : Finset V := covered G (covered G (defects G d))
def far : Finset V := Finset.univ \ zone G d
def initialDemands : Finset V := zone G d \ covered G (far G d)

noncomputable def boundaryCost (v : V) : ℝ :=
  (d + 1 : ℕ) - ((closed G v ∩ far G d).card : ℝ)

theorem defects_subset_zone : defects G d ⊆ zone G d :=
  (subset_covered G _).trans (subset_covered G _)

theorem far_degree {v : V} (hv : v ∈ far G d) : G.degree v = d := by
  by_contra h
  exact (Finset.mem_sdiff.mp hv).2
    (defects_subset_zone G d (by simp [defects, h]))

theorem closed_card (v : V) : (closed G v).card = G.degree v + 1 := by
  have heq : closed G v = insert v (G.neighborFinset v) := by
    ext u
    simp [mem_closed, SimpleGraph.mem_neighborFinset]
  rw [heq, Finset.card_insert_of_notMem]
  · rfl
  · simp

theorem near_defect_no_far {v : V} (hv : v ∈ covered G (defects G d)) :
    Disjoint (closed G v) (far G d) := by
  apply Finset.disjoint_left.mpr
  intro u huv huf
  exact (Finset.mem_sdiff.mp huf).2 (Finset.mem_biUnion.mpr ⟨v, hv, huv⟩)

theorem near_defect_subset_demands :
    covered G (defects G d) ⊆ initialDemands G d := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨subset_covered G _ hv, ?_⟩
  intro hc
  obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp hc
  exact Finset.disjoint_left.mp (near_defect_no_far G d hv)
    ((closed_symm G v u).mp hvu) hu

theorem boundary_card_le {v : V} (hv : v ∈ zone G d) :
    (closed G v ∩ far G d).card ≤ d := by
  by_cases hzero : (closed G v ∩ far G d).card = 0
  · omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hzero)
  have hvdeg : G.degree v = d := by
    by_contra h
    have hvB : v ∈ defects G d := by simp [defects, h]
    exact Finset.disjoint_left.mp
      (near_defect_no_far G d (subset_covered G _ hvB))
      (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2
  have hsubset : closed G v ∩ far G d ⊆ G.neighborFinset v := by
    intro w hw
    rcases (mem_closed G w v).mp (Finset.mem_inter.mp hw).1 with heq | hadj
    · subst w
      exact False.elim ((Finset.mem_sdiff.mp (Finset.mem_inter.mp hw).2).2 hv)
    · simpa only [SimpleGraph.mem_neighborFinset] using hadj
  simpa only [SimpleGraph.card_neighborFinset_eq_degree, hvdeg] using
    Finset.card_le_card hsubset

theorem boundaryCost_bounds {v : V} (hv : v ∈ zone G d) :
    1 ≤ boundaryCost G d v ∧ boundaryCost G d v ≤ (d + 1 : ℕ) := by
  have hcard : ((closed G v ∩ far G d).card : ℝ) ≤ d := by
    exact_mod_cast boundary_card_le G d hv
  have hn : (0 : ℝ) ≤ ((closed G v ∩ far G d).card : ℝ) := Nat.cast_nonneg _
  unfold boundaryCost
  push_cast
  constructor <;> linarith

/-- Cheap candidates have critical degree and are already covered by F.
The implication in fact holds for every vertex, including outside Z. -/
theorem cheap_cost {v : V} (hc : boundaryCost G d v < (d + 1 : ℕ)) :
    G.degree v = d ∧ v ∉ initialDemands G d := by
  have hpos : (0 : ℝ) < ((closed G v ∩ far G d).card : ℝ) := by
    unfold boundaryCost at hc
    linarith
  have hposN : 0 < (closed G v ∩ far G d).card := by exact_mod_cast hpos
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hposN
  refine ⟨?_, ?_⟩
  · by_contra hdeg
    have hvB : v ∈ defects G d := by simp [defects, hdeg]
    exact Finset.disjoint_left.mp
      (near_defect_no_far G d (subset_covered G _ hvB))
      (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2
  · intro hvR
    exact (Finset.mem_sdiff.mp hvR).2
      (Finset.mem_biUnion.mpr ⟨u, (Finset.mem_inter.mp hu).2,
        (closed_symm G v u).mpr (Finset.mem_inter.mp hu).1⟩)

theorem demand_closed_subset_zone {r : V} (hr : r ∈ initialDemands G d) :
    closed G r ⊆ zone G d := by
  intro v hv
  by_contra hn
  have hvF : v ∈ far G d := by simp [far, hn]
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_biUnion.mpr ⟨v, hvF, (closed_symm G v r).mp hv⟩)

noncomputable def auxiliary : CoverInstance V where
  demands := initialDemands G d
  candidates := zone G d
  eligible := fun r => closed G r ∩ zone G d
  eligible_subset := by intros; exact Finset.inter_subset_right
  cost := fun v => if v ∈ zone G d then boundaryCost G d v else 0
  cost_nonneg := by
    intro v
    split_ifs with hv
    · exact le_trans zero_le_one (boundaryCost_bounds G d hv).1
    · exact le_refl _

noncomputable def restrict (y : V → ℝ) (v : V) : ℝ :=
  if v ∈ zone G d then y v else 0

theorem restrict_feasible (y : V → ℝ) (hy : feasible (ordinary G) y) :
    feasible (auxiliary G d) (restrict G d y) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp [restrict]
    split_ifs <;> first | exact hy.1 v | exact le_refl _
  · intro v hv
    simp only [auxiliary] at hv
    simp [restrict, hv]
  · intro r hr
    have hsubset := demand_closed_subset_zone G d hr
    have heq : closed G r ∩ zone G d = closed G r := Finset.inter_eq_left.mpr hsubset
    change 1 ≤ ∑ v ∈ closed G r ∩ zone G d, restrict G d y v
    rw [heq]
    have heqsum : (∑ v ∈ closed G r, restrict G d y v) = ∑ v ∈ closed G r, y v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [restrict, hsubset hv]
    rw [heqsum]
    exact hy.2.2 r (Finset.mem_univ _)

theorem restricted_cost (y : V → ℝ) :
    cost (auxiliary G d) (restrict G d y) =
      ∑ v ∈ zone G d, boundaryCost G d v * y v := by
  classical
  simp [cost, auxiliary, restrict]

/-- Closed-incidence double counting, derived from graph symmetry. -/
theorem incidence_sum (S : Finset V) (y : V → ℝ) :
    (∑ r ∈ S, ∑ v ∈ closed G r, y v) =
      ∑ v, ((closed G v ∩ S).card : ℝ) * y v := by
  classical
  calc
    (∑ r ∈ S, ∑ v ∈ closed G r, y v) =
        ∑ r ∈ S, ∑ v, if v ∈ closed G r then y v else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      simp
    _ = ∑ v, ∑ r ∈ S, if v ∈ closed G r then y v else 0 := Finset.sum_comm
    _ = ∑ v, ((closed G v ∩ S).card : ℝ) * y v := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [closed_symm G v]
      have heq : S.filter (fun r => r ∈ closed G v) = closed G v ∩ S := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_inter]
        tauto
      rw [← Finset.sum_filter, heq]
      simp

theorem coverage_sum (S : Finset V) (y : V → ℝ)
    (hy : feasible (ordinary G) y) :
    (S.card : ℝ) ≤ ∑ v, ((closed G v ∩ S).card : ℝ) * y v := by
  rw [← incidence_sum G S y]
  calc
    (S.card : ℝ) = ∑ _r ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ r ∈ S, ∑ v ∈ closed G r, y v :=
      Finset.sum_le_sum (fun r _ => hy.2.2 r (Finset.mem_univ _))

/-- The actual weighted budget, with all coefficients discharged from graph facts. -/
theorem weighted_budget (y : V → ℝ) (hy : feasible (ordinary G) y) :
    ((far G d).card : ℝ) + ∑ v ∈ zone G d, boundaryCost G d v * y v ≤
      (d + 1 : ℕ) * ∑ v, y v := by
  classical
  have hZ : (∑ v ∈ zone G d, boundaryCost G d v * y v) =
      ∑ v, if v ∈ zone G d then boundaryCost G d v * y v else 0 := by simp
  calc
    ((far G d).card : ℝ) + ∑ v ∈ zone G d, boundaryCost G d v * y v ≤
        (∑ v, ((closed G v ∩ far G d).card : ℝ) * y v) +
          ∑ v ∈ zone G d, boundaryCost G d v * y v :=
      add_le_add (coverage_sum G (far G d) y hy) le_rfl
    _ = ∑ v, (((closed G v ∩ far G d).card : ℝ) * y v +
        if v ∈ zone G d then boundaryCost G d v * y v else 0) := by
      rw [hZ, Finset.sum_add_distrib]
    _ ≤ ∑ v, (d + 1 : ℕ) * y v := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ zone G d
      · simp only [if_pos hv, boundaryCost]
        nlinarith
      · simp only [if_neg hv, add_zero]
        apply mul_le_mul_of_nonneg_right _ (hy.1 v)
        have hcard := Finset.card_le_card (Finset.inter_subset_left :
          closed G v ∩ far G d ⊆ closed G v)
        have hvF : v ∈ far G d := by simp [far, hv]
        rw [closed_card G v, far_degree G d hvF] at hcard
        exact_mod_cast hcard
    _ = (d + 1 : ℕ) * ∑ v, y v := (Finset.mul_sum _ _ _).symm

def auxiliaryFeasibleCosts : Set ℝ :=
  {a | ∃ x, feasible (auxiliary G d) x ∧ cost (auxiliary G d) x = a}

noncomputable def auxiliaryNumber : ℝ := sInf (auxiliaryFeasibleCosts G d)

theorem auxiliaryFeasibleCosts_nonempty : (auxiliaryFeasibleCosts G d).Nonempty := by
  obtain ⟨a, y, hy, _⟩ := feasibleCosts_nonempty G
  exact ⟨_, restrict G d y, restrict_feasible G d y hy, rfl⟩

theorem auxiliaryFeasibleCosts_bddBelow : BddBelow (auxiliaryFeasibleCosts G d) := by
  refine ⟨0, ?_⟩
  rintro a ⟨x, hx, rfl⟩
  exact cost_nonneg_of_feasible _ _ hx

theorem auxiliaryNumber_le_restricted_cost (y : V → ℝ)
    (hy : feasible (ordinary G) y) :
    auxiliaryNumber G d ≤ ∑ v ∈ zone G d, boundaryCost G d v * y v := by
  apply csInf_le (auxiliaryFeasibleCosts_bddBelow G d)
  exact ⟨restrict G d y, restrict_feasible G d y hy, restricted_cost G d y⟩

/-- No auxiliary or global optimum vector needs to be attained. -/
theorem auxiliary_budget (y : V → ℝ) (hy : feasible (ordinary G) y) :
    ((far G d).card : ℝ) + auxiliaryNumber G d ≤ (d + 1 : ℕ) * ∑ v, y v := by
  exact le_trans (add_le_add le_rfl (auxiliaryNumber_le_restricted_cost G d y hy))
    (weighted_budget G d y hy)

theorem fractional_budget :
    ((far G d).card : ℝ) + auxiliaryNumber G d ≤
      (d + 1 : ℕ) * fractionalNumber G := by
  have hb : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  have hlow : (((far G d).card : ℝ) + auxiliaryNumber G d) / (d + 1 : ℕ) ≤
      fractionalNumber G := by
    apply le_csInf (feasibleCosts_nonempty G)
    rintro a ⟨y, hy, rfl⟩
    apply (div_le_iff₀ hb).mpr
    simpa only [ordinary_cost, mul_comm] using auxiliary_budget G d y hy
  exact (div_le_iff₀ hb).mp hlow |>.trans_eq (mul_comm _ _)

end Paper.WeightedBudget
