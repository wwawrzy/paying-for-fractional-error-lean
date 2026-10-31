import Paper.Solver.LocalSearch.IntegralFractionalOptima

namespace Paper.FourCycleOptima
open SevenFoundation
open scoped BigOperators

abbrev graph := SimpleGraph.cycleGraph 4

theorem closed_card (v : Fin 4) : (closed graph v).card = 3 := by
  fin_cases v <;> decide

theorem closed_zero : closed graph (0 : Fin 4) = {0, 1, 3} := by decide
theorem closed_one : closed graph (1 : Fin 4) = {0, 1, 2} := by decide
theorem closed_two : closed graph (2 : Fin 4) = {1, 2, 3} := by decide
theorem closed_three : closed graph (3 : Fin 4) = {0, 2, 3} := by decide

theorem fractional_cost_lower (x : Fin 4 → ℝ) (hx : feasible (ordinary graph) x) :
    4/3 ≤ cost (ordinary graph) x := by
  have h0 := hx.2.2 0 (Finset.mem_univ 0)
  have h1 := hx.2.2 1 (Finset.mem_univ 1)
  have h2 := hx.2.2 2 (Finset.mem_univ 2)
  have h3 := hx.2.2 3 (Finset.mem_univ 3)
  change 1 ≤ ∑ v ∈ closed graph 0, x v at h0
  change 1 ≤ ∑ v ∈ closed graph 1, x v at h1
  change 1 ≤ ∑ v ∈ closed graph 2, x v at h2
  change 1 ≤ ∑ v ∈ closed graph 3, x v at h3
  simp [closed_zero, closed_one, closed_two, closed_three] at h0 h1 h2 h3
  rw [ordinary_cost]
  simp only [Fin.sum_univ_succ]
  norm_num at *
  change 4/3 ≤ x 0 + (x 1 + (x 2 + x 3))
  linarith

theorem uniform_feasible : feasible (ordinary graph) (fun _ => (1/3 : ℝ)) := by
  refine ⟨fun _ => by norm_num, fun v hv => False.elim (hv (Finset.mem_univ v)), ?_⟩
  intro v _
  change 1 ≤ ∑ _ ∈ closed graph v, (1/3 : ℝ)
  simp [closed_card]

theorem fractional_eq : fractionalNumber graph = 4/3 := by
  apply le_antisymm
  · apply csInf_le (feasibleCosts_bddBelow graph)
    refine ⟨fun _ => 1/3, uniform_feasible, ?_⟩
    rw [ordinary_cost]
    norm_num
  · apply le_csInf (feasibleCosts_nonempty graph)
    rintro _ ⟨x, hx, rfl⟩
    exact fractional_cost_lower x hx

theorem domination_count (D : Finset (Fin 4)) (hD : dominates graph D) : 4 ≤ 3*D.card := by
  have he : covered graph D = Finset.univ := by
    ext v
    exact ⟨fun _ => Finset.mem_univ _, fun _ => hD v⟩
  calc
    4 = (covered graph D).card := by rw [he]; decide
    _ ≤ ∑ v ∈ D, (closed graph v).card := Finset.card_biUnion_le
    _ = 3*D.card := by simp [closed_card, mul_comm]

theorem integral_eq : graph.dominationNumber = 2 := by
  apply Nat.le_antisymm
  · have hd : dominates graph ({0, 2} : Finset (Fin 4)) := by unfold dominates; decide
    have hc := ((IntegralFractionalOptima.dominates_iff graph _).mp hd).dominationNumber_le
    simpa using hc
  · obtain ⟨D, hD, he⟩ := SimpleGraph.exists_isDominatingSetFinset_card_eq_dominationNumber (G := graph)
    have hc := domination_count D ((IntegralFractionalOptima.dominates_iff graph D).mpr hD)
    omega

theorem strict_gap : fractionalNumber graph < (graph.dominationNumber : ℝ) := by
  rw [fractional_eq, integral_eq]
  norm_num

end Paper.FourCycleOptima
