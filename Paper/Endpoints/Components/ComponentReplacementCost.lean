import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-! Componentwise cost comparison for the actual mixed selected set.
The per-component comparison is a hypothesis; runtime optimality remains separate. -/

set_option maxHeartbeats 200000
namespace Paper.ComponentReplacementCost

theorem replacement_cost_le
    {V I : Type} [DecidableEq V] [Fintype I] [DecidableEq I]
    (D0 D1 : Finset V) (component : V → I) (solved : I → Bool)
    (c : V → Real)
    (hcost : ∀ i, solved i = true →
      (∑ v ∈ D1.filter (fun v => component v = i), c v) ≤
      ∑ v ∈ D0.filter (fun v => component v = i), c v) :
    (∑ v ∈ (D0 ∪ D1).filter
      (fun v => if solved (component v) then v ∈ D1 else v ∈ D0), c v) ≤
    ∑ v ∈ D0, c v := by
  classical
  let D := (D0 ∪ D1).filter
    (fun v => if solved (component v) then v ∈ D1 else v ∈ D0)
  have hpart (s : Finset V) :
      (∑ i : I, ∑ v ∈ s.filter (fun v => component v = i), c v) = ∑ v ∈ s, c v :=
    Finset.sum_fiberwise s component c
  change (∑ v ∈ D, c v) ≤ ∑ v ∈ D0, c v
  rw [← hpart D, ← hpart D0]
  apply Finset.sum_le_sum
  intro i _
  by_cases hs : solved i = true
  · have hf : D.filter (fun v => component v = i) = D1.filter (fun v => component v = i) := by
      ext v
      by_cases hv : component v = i
      · simp [D, Finset.mem_filter, Finset.mem_union, hv, hs]
        exact fun h => Or.inr h
      · simp [D, Finset.mem_filter, Finset.mem_union, hv]
    rw [hf]
    exact hcost i hs
  · have hf : D.filter (fun v => component v = i) = D0.filter (fun v => component v = i) := by
      ext v
      by_cases hv : component v = i
      · simp [D, Finset.mem_filter, Finset.mem_union, hv, hs]
        exact fun h => Or.inl h
      · simp [D, Finset.mem_filter, Finset.mem_union, hv]
    rw [hf]

end Paper.ComponentReplacementCost

#print axioms Paper.ComponentReplacementCost.replacement_cost_le
