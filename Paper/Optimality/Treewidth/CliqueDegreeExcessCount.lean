import Paper.Optimality.Treewidth.CliqueRegionNine
namespace Paper.CliqueDegreeExcessCount
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
theorem at_most_one (T : Finset V) (d : V → ℕ)
    (hlow : ∀ x ∈ T, 8 ≤ d x) (hsum : (∑ x ∈ T, d x) ≤ 8*T.card+1) :
    (T.filter (fun x => 9 ≤ d x)).card ≤ 1 := by
  classical
  have hp : ∀ x ∈ T, 8+(if 9 ≤ d x then 1 else 0) ≤ d x := by
    intro x hx
    have hh := hlow x hx
    split_ifs <;> omega
  have hh := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Finset.sum_boole] at hh
  norm_cast at hh
  omega
end Paper.CliqueDegreeExcessCount
