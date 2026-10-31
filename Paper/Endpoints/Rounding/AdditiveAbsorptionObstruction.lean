import Paper.Certificates.Counting.PartialOptimum
import Paper.Preliminaries.Incidence
import Paper.Communication.BroadcastModel

/-! A counterexample to `fv:imp:absorb` with only the hypothesis `r > 0`.
One isolated vertex is its own sole covering candidate and demand, at unit
cost. Its integral and fractional optima are both one. The additive premise
holds for r = 1/2 and q = 1, while epsilon = 1/4 makes the conclusion
impossible. Requiring r >= 1 excludes this obstruction; this file does not
claim that the additional restriction alone proves the corrected lemma. -/

namespace Paper.AdditiveAbsorptionObstruction

open SevenFoundation
open scoped BigOperators

def graph : SimpleGraph Unit := ⊥

instance : DecidableRel graph.Adj :=
  inferInstanceAs (DecidableRel (⊥ : SimpleGraph Unit).Adj)

def unitCost : Unit → ℝ := fun _ => 1

theorem closed_eq (v : Unit) : closed graph v = {v} := by
  ext u
  simp [closed, graph]

theorem dominates_iff (D : Finset Unit) : dominates graph D ↔ () ∈ D := by
  simp [dominates, covered, closed, graph]
  constructor
  · rintro ⟨v, hv⟩
    cases v
    exact hv
  · intro h
    exact ⟨(), h⟩

theorem dominating_card (D : Finset Unit) (hD : dominates graph D) : D.card = 1 := by
  have hmem := (dominates_iff D).mp hD
  have heq : D = {()} := by
    ext v
    cases v
    simp [hmem]
  simp [heq]

theorem univ_dominates : dominates graph Finset.univ :=
  (dominates_iff _).mpr (Finset.mem_univ _)

/-- This is the actual minimum integral cost, not a supplied optimum value. -/
theorem integral_optimum :
    IsLeast {c : ℝ | ∃ D : Finset Unit, dominates graph D ∧ (D.card : ℝ) = c} 1 := by
  refine ⟨⟨Finset.univ, univ_dominates, by simp⟩, ?_⟩
  rintro c ⟨D, hD, rfl⟩
  simp [dominating_card D hD]

theorem feasible_sum_ge_one (x : Unit → ℝ)
    (hx : PartialOptimum.Feasible graph Finset.univ x) : 1 ≤ ∑ v, x v := by
  have h := hx.2 () (Finset.mem_univ _)
  simpa only [closed_eq, Finset.sum_singleton, Fintype.sum_unique] using h

theorem one_feasible : PartialOptimum.Feasible graph Finset.univ (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, ?_⟩
  intro r _
  simp [closed_eq]

/-- The LP optimum is computed from the existing infimum definition. -/
theorem fractional_optimum : PartialOptimum.number graph Finset.univ unitCost = 1 := by
  have hleast : IsLeast (PartialOptimum.values graph Finset.univ unitCost) 1 := by
    refine ⟨⟨fun _ => 1, one_feasible, ?_⟩, ?_⟩
    · simp [PartialOptimum.objective, unitCost]
    · rintro c ⟨x, hx, rfl⟩
      simpa only [PartialOptimum.objective, unitCost, one_mul] using feasible_sum_ge_one x hx
  exact hleast.csInf_eq

theorem density_one : Incidence.InducedDensityBound graph 1 := by
  intro S
  have he : graph.inducedEdgeCount S = 0 := by
    simp [SimpleGraph.inducedEdgeCount, graph]
  rw [he]
  simpa only [Nat.cast_zero, one_mul] using
    (Nat.cast_nonneg S.card : (0 : ℝ) ≤ (S.card : ℝ))

/-- Select the sole vertex using a local operation and no transmissions. -/
def program : BroadcastModel.Program Unit PUnit Bool := .local fun _ _ _ => true

theorem program_resources : program.rounds = 0 ∧ program.maxBits = 0 := ⟨rfl, rfl⟩

theorem program_selects :
    program.run graph (fun _ => PUnit.unit) = fun _ => true := rfl

theorem additive_premise (delta : ℝ) (hdelta : 0 < delta) :
    dominates graph Finset.univ ∧
      ((Finset.univ : Finset Unit).card : ℝ) ≤
        (1 / 2 : ℝ) * (1 + delta) * PartialOptimum.number graph Finset.univ unitCost + 1 := by
  refine ⟨univ_dominates, ?_⟩
  rw [fractional_optimum]
  norm_num
  linarith

/-- With r = 1/2 and epsilon = 1/4 the desired cost is at most 3/4,
strictly below the proved optimum integral cost one. -/
theorem epsilon_obstruction :
    ¬ ∃ D : Finset Unit, dominates graph D ∧
      (D.card : ℝ) ≤ ((1 / 2 : ℝ) + 1 / 4) * 1 := by
  rintro ⟨D, hD, hbound⟩
  rw [dominating_card D hD] at hbound
  norm_num at hbound

/-- The additive guarantee holds at every positive accuracy, yet its claimed
multiplicative conclusion fails even on this density-one covering instance. -/
theorem obstruction :
    Incidence.InducedDensityBound graph 1 ∧
      (∀ delta : ℝ, 0 < delta → dominates graph Finset.univ ∧
        ((Finset.univ : Finset Unit).card : ℝ) ≤
          (1 / 2 : ℝ) * (1 + delta) * PartialOptimum.number graph Finset.univ unitCost + 1) ∧
      ¬ ∃ D : Finset Unit, dominates graph D ∧ (D.card : ℝ) ≤ (3 / 4 : ℝ) := by
  refine ⟨density_one, additive_premise, ?_⟩
  convert epsilon_obstruction using 1
  norm_num

end Paper.AdditiveAbsorptionObstruction

#print axioms Paper.AdditiveAbsorptionObstruction.integral_optimum
#print axioms Paper.AdditiveAbsorptionObstruction.fractional_optimum
#print axioms Paper.AdditiveAbsorptionObstruction.program_selects
#print axioms Paper.AdditiveAbsorptionObstruction.obstruction
