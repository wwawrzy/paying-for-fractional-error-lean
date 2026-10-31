import Paper.TotalDomination.HighGirthCosts

namespace Paper.TotalDomination.HighGirthSelection
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] 

noncomputable def residualOptimum : ℝ :=
  CoveringOptimum.number (fun r => G.neighborFinset r ∩ candidates G)
    (remaining G) (fun v => (boundaryCost G v : ℝ))
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
    ((selected G).card : ℝ) + ∑ v, (boundaryCost G v : ℝ)*y v ≤ 2*(∑ v, y v) := by
  classical
  have hcov : ((selected G).card : ℝ) ≤ ∑ v, (hits G v : ℝ)*y v := by
    change ((selected G).card : ℝ) ≤ ∑ v, ((G.neighborFinset v ∩ selected G).card : ℝ)*y v
    rw [← open_incidence_sum]
    calc
      _ = ∑ _r ∈ selected G, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun r _ => hy.2 r (Finset.mem_univ _)
  have hsum : (∑ v, (hits G v : ℝ)*y v) +
      (∑ v, (boundaryCost G v : ℝ)*y v) = 2*(∑ v, y v) := by
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    have h : (boundaryCost G v : ℝ)+(hits G v : ℝ) = 2 := by
      exact_mod_cast cost_identity G v
    rw [← add_mul,add_comm,h]
  linarith

theorem residual_number_le  (y : V → ℝ)
    (hy : CoveringOptimum.Feasible (fun r => G.neighborFinset r) Finset.univ y) :
    residualOptimum G ≤ ∑ v, (boundaryCost G v : ℝ)*y v := by
  classical
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (hx.1 v)
  · refine ⟨y,⟨hy.1,?_⟩,rfl⟩
    intro r hr
    change 1 ≤ ∑ v ∈ G.neighborFinset r ∩ candidates G, y v
    rw [demand_rows G hr]
    exact hy.2 r (Finset.mem_univ _)

theorem fractional_budget 
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    ((selected G).card : ℝ) + residualOptimum G ≤ 2*totalFractionalNumber G := by
  obtain ⟨y,hy,heq⟩ := CoveringOptimum.exists_optimum_eq_number
    (fun r => G.neighborFinset r) Finset.univ (fun _ => (1:ℝ))
    (fun v _ => hfree v) (fun _ => zero_le_one)
  have hv := vector_budget G y hy
  have hr := residual_number_le G y hy
  have hobj : (∑ v, y v) = totalFractionalNumber G := by
    simpa only [CoveringOptimum.objective,one_mul,totalFractionalNumber] using heq
  rw [hobj] at hv
  linarith

theorem exists_residual_optimum 
    (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    ∃ x : V → ℝ, (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧
      (∀ v, v ∉ candidates G → x v = 0) ∧
      (∀ r ∈ remaining G, 1 ≤ ∑ v ∈ G.neighborFinset r, x v) ∧
      (∑ v, (boundaryCost G v : ℝ)*x v) = residualOptimum G := by
  classical
  let C := fun r => G.neighborFinset r ∩ candidates G
  obtain ⟨y,hy,hcap,hmin⟩ := CoveringOptimum.exists_optimum C (remaining G)
    (fun v => (boundaryCost G v : ℝ))
    (fun r hr => by dsimp [C];rw [demand_rows G hr];exact hfree r)
    (fun _ => Nat.cast_nonneg _)
  have hleast : IsLeast (CoveringOptimum.values C (remaining G)
      (fun v => (boundaryCost G v : ℝ)))
      (CoveringOptimum.objective (fun v => (boundaryCost G v : ℝ)) y) := by
    refine ⟨⟨y,hy,rfl⟩,?_⟩
    rintro z ⟨x,hx,rfl⟩
    exact hmin x hx
  let x : V → ℝ := fun v => if v ∈ candidates G then y v else 0
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
      rw [demand_rows G hr]
      apply Finset.sum_congr rfl
      intro v hv
      exact if_pos (remaining_neighbors_candidates G hr ((G.mem_neighborFinset r v).mp hv))
    rw [hrow]
    exact hy.2 r hr
  · have heq : (∑ v, (boundaryCost G v : ℝ)*x v) =
        CoveringOptimum.objective (fun v => (boundaryCost G v : ℝ)) y := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ candidates G
      · simp [x,hv]
      · have hc : boundaryCost G v = 0 := by
          apply Nat.eq_zero_of_not_pos
          intro hp
          exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
        simp [x,hv,hc]
    rw [heq]
    exact hleast.csInf_eq.symm

/-- All mathematical clauses of fv:hg:t-budget for the actual branch exterior. -/
theorem exterior_budget (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    (∀ v ∈ selected G, ∃ u ∈ selected G, G.Adj v u) ∧
    (∀ v ∈ remaining G, ∃ b ∈ branch G, ∃ p : G.Path v b,
      (p : G.Walk v b).length ≤ 3 ∧
      ∀ u ∈ (p : G.Walk v b).support, u ≠ v → u ∈ zone G) ∧
    (∀ v ∈ covered G (branch G), Disjoint (closed G v) (selected G)) ∧
    (∀ v, (G.neighborFinset v ∩ selected G).Nonempty → G.degree v ≤ 2) ∧
    (∀ v, boundaryCost G v ≤ 2) ∧
    (∀ v ∈ covered G (branch G), boundaryCost G v = 2) ∧
    (∀ v, boundaryCost G v = 0 → ∀ r ∈ remaining G, ¬G.Adj v r) ∧
    remaining G ⊆ candidates G ∧
    (∀ r ∈ remaining G, G.neighborFinset r ⊆ candidates G) ∧
    ((selected G).card : ℝ) + residualOptimum G ≤ 2*totalFractionalNumber G := by
  refine ⟨fun _ hv => selected_neighbor G hv,
    fun _ hv => remaining_path_zone G hfree hv,
    fun _ hv => near_defect_disjoint G hv,
    fun _ hv => touches_degree G hv,
    fun _ => Nat.sub_le _ _, fun _ hv => near_cost G hv,?_,
    remaining_subset_candidates G hfree,?_,fractional_budget G hfree⟩
  · intro v hz r hr ha
    have hc := remaining_neighbors_candidates G hr ha.symm
    have hp := (Finset.mem_filter.mp hc).2
    omega
  · intro r hr v hv
    exact remaining_neighbors_candidates G hr ((G.mem_neighborFinset r v).mp hv)

end Paper.TotalDomination.HighGirthSelection
#print axioms Paper.TotalDomination.HighGirthSelection.fractional_budget
#print axioms Paper.TotalDomination.HighGirthSelection.exists_residual_optimum

#print axioms Paper.TotalDomination.HighGirthSelection.exterior_budget
