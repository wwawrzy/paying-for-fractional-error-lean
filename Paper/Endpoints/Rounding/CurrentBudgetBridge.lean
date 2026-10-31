import Paper.Endpoints.Rounding.CurrentBudget
import Paper.Endpoints.Rounding.NoncriticalOptimum
import Paper.Preliminaries.InducedExtension

/-! Bridges the current residual covering instance to the weighted LP on the
induced graph `G-F`, and records attainment of both residual and global
fractional optima. This file does not alter the budget theorem or its roots. -/
namespace Paper.CurrentBudgetBridge

attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

/-- The residual demands, transported to the subtype `V \ F`. -/
noncomputable def residualDemands :
    Finset ↥(CurrentBudget.candidates G d : Set V) :=
  InducedSubsets.lift (CurrentBudget.candidates G d) (CurrentBudget.demands G d)

/-- The current candidate cost, viewed as a cost on `G-F`. -/
noncomputable def residualCost
    (v : ↥(CurrentBudget.candidates G d : Set V)) : ℝ :=
  CurrentBudget.boundaryCost G d v.val

theorem residual_demands_subset :
    CurrentBudget.demands G d ⊆ CurrentBudget.candidates G d :=
  CurrentBudget.demands_subset_candidates G d

theorem to_auxiliary (z : ↥(CurrentBudget.candidates G d : Set V) → ℝ)
    (hz : PartialOptimum.Feasible (G.induce (CurrentBudget.candidates G d : Set V))
      (residualDemands G d) z) :
    feasible (CurrentBudget.auxiliary G d)
      (InducedExtension.extend (CurrentBudget.candidates G d) z) := by
  have hgraph := InducedExtension.feasible G (CurrentBudget.candidates G d)
    (CurrentBudget.demands G d) (residual_demands_subset G d)
    (fun r hr => CurrentBudget.demand_closed_subset_candidates G d hr) z hz
  refine ⟨hgraph.1, ?_, ?_⟩
  · intro v hv
    change v ∉ CurrentBudget.candidates G d at hv
    exact dif_neg hv
  · intro r hr
    change r ∈ CurrentBudget.demands G d at hr
    change 1 ≤ ∑ v ∈ closed G r ∩ CurrentBudget.candidates G d,
      InducedExtension.extend (CurrentBudget.candidates G d) z v
    rw [Finset.inter_eq_left.mpr
      (CurrentBudget.demand_closed_subset_candidates G d hr)]
    exact hgraph.2 r hr

theorem extension_cost (z : ↥(CurrentBudget.candidates G d : Set V) → ℝ) :
    cost (CurrentBudget.auxiliary G d)
      (InducedExtension.extend (CurrentBudget.candidates G d) z) =
    PartialOptimum.objective (residualCost G d) z := by
  classical
  have hcost :
      cost (CurrentBudget.auxiliary G d)
          (InducedExtension.extend (CurrentBudget.candidates G d) z) =
        PartialOptimum.objective (CurrentBudget.boundaryCost G d)
          (InducedExtension.extend (CurrentBudget.candidates G d) z) := by
    apply Finset.sum_congr rfl
    intro v _
    change (if v ∈ CurrentBudget.candidates G d then
        CurrentBudget.boundaryCost G d v else 0) *
      InducedExtension.extend (CurrentBudget.candidates G d) z v = _
    by_cases hv : v ∈ CurrentBudget.candidates G d
    · rw [if_pos hv]
    · simp only [if_neg hv, InducedExtension.extend, dif_neg hv, mul_zero]
  exact hcost.trans
    (InducedExtension.cost (CurrentBudget.candidates G d) z
      (CurrentBudget.boundaryCost G d))

theorem from_auxiliary (x : V → ℝ)
    (hx : feasible (CurrentBudget.auxiliary G d) x) :
    PartialOptimum.Feasible (G.induce (CurrentBudget.candidates G d : Set V))
      (residualDemands G d) (fun v => x v.val) := by
  refine ⟨fun v => hx.1 v.val, ?_⟩
  intro r hr
  have hrR : r.val ∈ CurrentBudget.demands G d :=
    Finset.mem_subtype.mp hr
  rw [InducedCover.closed_sum G (CurrentBudget.candidates G d) r x
    (CurrentBudget.demand_closed_subset_candidates G d hrR)]
  have hs := hx.2.2 r.val hrR
  change 1 ≤ ∑ v ∈ closed G r.val ∩ CurrentBudget.candidates G d, x v at hs
  rwa [Finset.inter_eq_left.mpr
    (CurrentBudget.demand_closed_subset_candidates G d hrR)] at hs

theorem restriction_cost (x : V → ℝ)
    (hx : feasible (CurrentBudget.auxiliary G d) x) :
    cost (CurrentBudget.auxiliary G d) x =
      PartialOptimum.objective (residualCost G d) (fun v => x v.val) := by
  have he :
      InducedExtension.extend (CurrentBudget.candidates G d)
        (fun v => x v.val) = x := by
    funext v
    by_cases hv : v ∈ CurrentBudget.candidates G d
    · exact dif_pos hv
    · have hz := hx.2.1 v hv
      simpa only [InducedExtension.extend, dif_neg hv] using hz.symm
  calc
    _ = cost (CurrentBudget.auxiliary G d)
        (InducedExtension.extend (CurrentBudget.candidates G d)
          (fun v => x v.val)) := congrArg _ he.symm
    _ = _ := extension_cost G d _

/-- Feasible objective values agree exactly between the current CoverInstance
and the weighted fractional-cover LP on the induced graph `G-F`. -/
theorem values_eq :
    PartialOptimum.values
        (G.induce (CurrentBudget.candidates G d : Set V))
        (residualDemands G d) (residualCost G d) =
      CurrentBudget.auxiliaryFeasibleCosts G d := by
  ext t
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨InducedExtension.extend (CurrentBudget.candidates G d) z,
      to_auxiliary G d z hz, (extension_cost G d z).trans he⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨(fun v => x v.val), from_auxiliary G d x hx,
      (restriction_cost G d x hx).symm.trans he⟩

/-- The two LP values are equal as infima; `PartialOptimum` also proves that
the induced-graph value is attained. -/
theorem number_eq :
    PartialOptimum.number
        (G.induce (CurrentBudget.candidates G d : Set V))
        (residualDemands G d) (residualCost G d) =
      CurrentBudget.auxiliaryNumber G d :=
  congrArg sInf (values_eq G d)

theorem residual_optimum_attained :
    ∃ z : ↥(CurrentBudget.candidates G d : Set V) → ℝ,
      PartialOptimum.Feasible
        (G.induce (CurrentBudget.candidates G d : Set V))
        (residualDemands G d) z ∧
      PartialOptimum.objective (residualCost G d) z =
        CurrentBudget.auxiliaryNumber G d := by
  have hcost_nonneg : ∀ v : ↥(CurrentBudget.candidates G d : Set V),
      0 ≤ residualCost G d v := by
    intro v
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans
      (CurrentBudget.cost_integral_bounds G d v.property).2.1
  obtain ⟨z, hz, he⟩ := PartialOptimum.exists_optimum_eq_number
    (G.induce (CurrentBudget.candidates G d : Set V))
    (residualDemands G d) (residualCost G d) hcost_nonneg
  exact ⟨z, hz, he.trans (number_eq G d)⟩

/-- The infimum used by the auxiliary CoverInstance is an attained minimum
inside that same CoverInstance. -/
theorem auxiliary_optimum_attained :
    ∃ x : V → ℝ, feasible (CurrentBudget.auxiliary G d) x ∧
      cost (CurrentBudget.auxiliary G d) x = CurrentBudget.auxiliaryNumber G d := by
  obtain ⟨z, hz, he⟩ := residual_optimum_attained G d
  refine ⟨InducedExtension.extend (CurrentBudget.candidates G d) z,
    to_auxiliary G d z hz, ?_⟩
  calc
    _ = PartialOptimum.objective (residualCost G d) z := extension_cost G d z
    _ = CurrentBudget.auxiliaryNumber G d := he

/-- The global fractional domination infimum is likewise attained, matching
the paper's minimum definition of `gf(G)`. -/
theorem global_fractional_minimum :
    ∃ y : V → ℝ, feasible (ordinary G) y ∧
      cost (ordinary G) y = fractionalNumber G ∧
      ∀ z, feasible (ordinary G) z →
        cost (ordinary G) y ≤ cost (ordinary G) z := by
  obtain ⟨y, hy, _, hmin⟩ := PartialOptimum.exists_optimum
    G Finset.univ (fun _ => (1 : ℝ)) (by intro; norm_num)
  have hy' := (NoncriticalOptimum.feasible_iff G y).mp hy
  have hleast : IsLeast
      (PartialOptimum.values G Finset.univ (fun _ => (1 : ℝ)))
      (PartialOptimum.objective (fun _ => (1 : ℝ)) y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact hmin z hz
  have hopt : PartialOptimum.objective (fun _ => (1 : ℝ)) y =
      PartialOptimum.number G Finset.univ (fun _ => (1 : ℝ)) :=
    hleast.csInf_eq.symm
  have hvalue : cost (ordinary G) y = fractionalNumber G := by
    calc
      cost (ordinary G) y = ∑ v, y v := ordinary_cost G y
      _ = PartialOptimum.objective (fun _ => (1 : ℝ)) y := by
        simp [PartialOptimum.objective]
      _ = PartialOptimum.number G Finset.univ (fun _ => (1 : ℝ)) := hopt
      _ = fractionalNumber G := NoncriticalOptimum.number_eq G
  refine ⟨y, hy', hvalue, ?_⟩
  intro z hz
  calc
    cost (ordinary G) y =
        PartialOptimum.objective (fun _ => (1 : ℝ)) y := by
      simp [ordinary_cost, PartialOptimum.objective]
    _ ≤ PartialOptimum.objective (fun _ => (1 : ℝ)) z :=
      hmin z ((NoncriticalOptimum.feasible_iff G z).mpr hz)
    _ = cost (ordinary G) z := by
      simp [ordinary_cost, PartialOptimum.objective]

/-- The budget clauses with the residual optimum expressed on `G-F` itself.
The `PartialOptimum.number` in the last clause is an attained minimum by
`residual_optimum_attained`, and `fractionalNumber` is an attained global
minimum by `global_fractional_minimum`. -/
theorem current_budget_on_residual_lp :
    WeightedBudget.defects G d ⊆ CurrentBudget.demands G d ∧
    (∀ v ∈ CurrentBudget.candidates G d,
      (∃ n : ℕ, CurrentBudget.boundaryCost G d v = (n : ℝ)) ∧
      1 ≤ CurrentBudget.boundaryCost G d v ∧
      CurrentBudget.boundaryCost G d v ≤ (d + 1 : ℕ) ∧
      (CurrentBudget.boundaryCost G d v = (d + 1 : ℕ) ↔
        v ∈ CurrentBudget.demands G d) ∧
      (CurrentBudget.boundaryCost G d v < (d + 1 : ℕ) →
        ((closed G v ∩ CurrentBudget.demands G d).card : ℝ) ≤
          CurrentBudget.boundaryCost G d v - 1)) ∧
    ((CurrentBudget.selected G d).card : ℝ) +
      PartialOptimum.number
        (G.induce (CurrentBudget.candidates G d : Set V))
        (residualDemands G d) (residualCost G d) ≤
      (d + 1 : ℕ) * fractionalNumber G := by
  obtain ⟨hdef, hcost, hbudget⟩ := CurrentBudget.current_budget G d
  refine ⟨hdef, hcost, ?_⟩
  rw [number_eq G d]
  exact hbudget

end Paper.CurrentBudgetBridge
