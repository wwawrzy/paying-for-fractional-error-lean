import Paper.TotalDomination.InitialCosts

namespace Paper.TotalDomination.InitialSelection
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

noncomputable def residualOptimum : ℝ :=
  CoveringOptimum.number (fun r => G.neighborFinset r ∩ candidates G d)
    (remaining G d) (fun v => (boundaryCost G d v : ℝ))
noncomputable def totalFractionalNumber : ℝ :=
  CoveringOptimum.number (fun r => G.neighborFinset r) Finset.univ (fun _ => 1)

theorem open_incidence_sum (S : Finset V) (y : V → ℝ) :
    (∑ r ∈ S, ∑ v ∈ G.neighborFinset r, y v) =
      ∑ v, ((G.neighborFinset v ∩ S).card : ℝ)*y v := by
  classical
  calc
    _ = ∑ r ∈ S, ∑ v, if v ∈ G.neighborFinset r then y v else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter]
      congr 1
      ext v
      simp
    _ = ∑ v, ∑ r ∈ S, if v ∈ G.neighborFinset r then y v else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [SimpleGraph.mem_neighborFinset,G.adj_comm]
      have heq : S.filter (fun r => G.Adj v r) = G.neighborFinset v ∩ S := by
        ext r
        simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
        tauto
      rw [← Finset.sum_filter,heq]
      simp

theorem vector_budget (y : V → ℝ)
    (hy : CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ y) :
    ((selected G d).card : ℝ) + ∑ v, (boundaryCost G d v : ℝ)*y v ≤ d*(∑ v, y v) := by
  classical
  have hcov : ((selected G d).card : ℝ) ≤ ∑ v, (hits G d v : ℝ)*y v := by
    change ((selected G d).card : ℝ) ≤ ∑ v, ((G.neighborFinset v ∩ selected G d).card : ℝ)*y v
    rw [← open_incidence_sum]
    calc
      _ = ∑ _r ∈ selected G d, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun r _ => hy.2 r (Finset.mem_univ _)
  have hsum : (∑ v, (hits G d v : ℝ)*y v) +
      (∑ v, (boundaryCost G d v : ℝ)*y v) = d*(∑ v, y v) := by
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    have h : (boundaryCost G d v : ℝ)+(hits G d v : ℝ) = d := by
      exact_mod_cast cost_identity G d v
    rw [← add_mul,add_comm,h]
  linarith

theorem residual_number_le (hd : 0 < d) (y : V → ℝ)
    (hy : CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ y) :
    residualOptimum G d ≤ ∑ v, (boundaryCost G d v : ℝ)*y v := by
  classical
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (hx.1 v)
  · refine ⟨y,⟨hy.1,?_⟩,rfl⟩
    intro r hr
    change 1 ≤ ∑ v ∈ G.neighborFinset r ∩ candidates G d, y v
    rw [demand_rows G d hd hr]
    exact hy.2 r (Finset.mem_univ _)

theorem fractional_budget (hd : 0 < d)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    ((selected G d).card : ℝ) + residualOptimum G d ≤ d*totalFractionalNumber G := by
  obtain ⟨y,hy,heq⟩ := CoveringOptimum.exists_optimum_eq_number
    (fun r => G.neighborFinset r) Finset.univ (fun _ => (1:ℝ))
    (fun v _ => hfree v) (fun _ => zero_le_one)
  have hv := vector_budget G d y hy
  have hr := residual_number_le G d hd y hy
  have hobj : (∑ v, y v) = totalFractionalNumber G := by
    simpa only [CoveringOptimum.objective,one_mul,totalFractionalNumber] using heq
  rw [hobj] at hv
  linarith

theorem exists_residual_optimum (hd : 0 < d)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    ∃ x : V → ℝ, (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧
      (∀ v, v ∉ candidates G d → x v = 0) ∧
      (∀ r ∈ remaining G d, 1 ≤ ∑ v ∈ G.neighborFinset r, x v) ∧
      (∑ v, (boundaryCost G d v : ℝ)*x v) = residualOptimum G d := by
  classical
  let C := fun r => G.neighborFinset r ∩ candidates G d
  obtain ⟨y,hy,hcap,hmin⟩ := CoveringOptimum.exists_optimum C (remaining G d)
    (fun v => (boundaryCost G d v : ℝ))
    (fun r hr => by dsimp [C];rw [demand_rows G d hd hr];exact hfree r)
    (fun _ => Nat.cast_nonneg _)
  have hleast : IsLeast (CoveringOptimum.values C (remaining G d)
      (fun v => (boundaryCost G d v : ℝ)))
      (CoveringOptimum.objective (fun v => (boundaryCost G d v : ℝ)) y) := by
    refine ⟨⟨y,hy,rfl⟩,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact hmin x hx
  let x : V → ℝ := fun v => if v ∈ candidates G d then y v else 0
  refine ⟨x,?_,?_,?_,?_⟩
  · intro v
    dsimp [x]
    split_ifs
    · exact ⟨hy.1 v,hcap v⟩
    · exact ⟨le_rfl,zero_le_one⟩
  · intro v hv
    simp only [x,if_neg hv]
  · intro r hr
    have hrow : (∑ v ∈ G.neighborFinset r, x v) = ∑ v ∈ C r, y v := by
      dsimp [C]
      rw [demand_rows G d hd hr]
      apply Finset.sum_congr rfl
      intro v hv
      exact if_pos (remaining_neighbors_candidates G d hd hr ((G.mem_neighborFinset r v).mp hv))
    rw [hrow]
    exact hy.2 r hr
  · have heq : (∑ v, (boundaryCost G d v : ℝ)*x v) =
        CoveringOptimum.objective (fun v => (boundaryCost G d v : ℝ)) y := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ candidates G d
      · simp [x,hv]
      · have hc : boundaryCost G d v = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hp
          exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
        simp [x,hv,hc]
    rw [heq]
    exact hleast.csInf_eq.symm

/-- All clauses of fv:total:budget, including the attained capped residual LP. -/
theorem first_selection_budget (hd : 0 < d)
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (∀ v ∈ selected G d, ∃ u ∈ selected G d, G.Adj v u) ∧
    (∀ v ∈ covered G (covered G (selected G d)), G.degree v = d) ∧
    covered G (WeightedBudget.defects G d) ⊆ remaining G d ∧
    (∀ v ∈ covered G (WeightedBudget.defects G d), Disjoint (closed G v) (selected G d)) ∧
    ((remaining G d).Nonempty → (WeightedBudget.defects G d).Nonempty) ∧
    (∀ v ∈ remaining G d, ∃ u ∈ remaining G d, G.Adj v u) ∧
    (∀ v ∈ remaining G d, ∃ b ∈ WeightedBudget.defects G d, ∃ p : G.Path v b,
      (p : G.Walk v b).length ≤ 3 ∧ ∀ u ∈ (p : G.Walk v b).support, u ∈ remaining G d) ∧
    (∀ v ∈ candidates G d, 1 ≤ boundaryCost G d v ∧ boundaryCost G d v ≤ d) ∧
    (∀ r ∈ remaining G d, ∀ v, G.Adj r v → v ∈ candidates G d) ∧
    remaining G d ⊆ candidates G d ∧
    ((selected G d).card : ℝ) + residualOptimum G d ≤ d*totalFractionalNumber G := by
  exact ⟨fun _ hv => selected_neighbor G d hv,
    fun _ hv => distance_two_degree G d hv,near_defect_remaining G d,
    fun _ hv => near_defect_disjoint G d hv,defects_nonempty G d hfree,
    fun _ hv => remaining_neighbor G d hfree hv,
    fun _ hv => remaining_path G d hfree hv,
    fun _ hv => candidate_bounds G d hv,
    fun _ hr _ hv => remaining_neighbors_candidates G d hd hr hv,
    remaining_subset_candidates G d hd hfree,fractional_budget G d hd hfree⟩

end Paper.TotalDomination.InitialSelection
#print axioms Paper.TotalDomination.InitialSelection.vector_budget
#print axioms Paper.TotalDomination.InitialSelection.fractional_budget

#print axioms Paper.TotalDomination.InitialSelection.exists_residual_optimum
#print axioms Paper.TotalDomination.InitialSelection.first_selection_budget
