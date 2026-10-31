import Paper.Preliminaries.InducedExtension
import Paper.Endpoints.Rounding.WeightedBudget

/-! Exact equivalence between the auxiliary cover instance and partial
weighted domination on the actual induced defect zone. Their true LP
optima agree; no auxiliary solver assumption is introduced. -/
namespace Paper.AuxiliaryGraph
attribute [local instance] Classical.propDecidable
open SevenFoundation WeightedBudget
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

noncomputable def demands : Finset ↥(zone G d : Set V) :=
  InducedSubsets.lift (zone G d) (initialDemands G d)

noncomputable def weights (v : ↥(zone G d : Set V)) : ℝ := boundaryCost G d v.val

theorem demands_subset : initialDemands G d ⊆ zone G d := Finset.sdiff_subset

theorem weights_bounds (v : ↥(zone G d : Set V)) : 1 ≤ weights G d v ∧ weights G d v ≤ (d + 1 : ℕ) :=
  boundaryCost_bounds G d v.property

theorem to_auxiliary (z : ↥(zone G d : Set V) → ℝ)
    (hz : PartialOptimum.Feasible (G.induce (zone G d : Set V)) (demands G d) z) :
    feasible (auxiliary G d) (InducedExtension.extend (zone G d) z) := by
  have hg := InducedExtension.feasible G (zone G d) (initialDemands G d) (demands_subset G d)
    (fun r hr => demand_closed_subset_zone G d hr) z hz
  refine ⟨hg.1, ?_, ?_⟩
  · intro v hv
    change v ∉ zone G d at hv
    exact dif_neg hv
  · intro r hr
    change r ∈ initialDemands G d at hr
    change 1 ≤ ∑ v ∈ closed G r ∩ zone G d, InducedExtension.extend (zone G d) z v
    rw [Finset.inter_eq_left.mpr (demand_closed_subset_zone G d hr)]
    exact hg.2 r hr

theorem extension_cost (z : ↥(zone G d : Set V) → ℝ) :
    cost (auxiliary G d) (InducedExtension.extend (zone G d) z) = PartialOptimum.objective (weights G d) z := by
  classical
  have hcost : cost (auxiliary G d) (InducedExtension.extend (zone G d) z) =
      PartialOptimum.objective (boundaryCost G d) (InducedExtension.extend (zone G d) z) := by
    apply Finset.sum_congr rfl
    intro v _
    change (if v ∈ zone G d then boundaryCost G d v else 0) * InducedExtension.extend (zone G d) z v = _
    by_cases hv : v ∈ zone G d
    · rw [if_pos hv]
    · simp only [if_neg hv, InducedExtension.extend, dif_neg hv, mul_zero]
  exact hcost.trans (InducedExtension.cost (zone G d) z (boundaryCost G d))

theorem from_auxiliary (x : V → ℝ) (hx : feasible (auxiliary G d) x) :
    PartialOptimum.Feasible (G.induce (zone G d : Set V)) (demands G d) (fun v => x v.val) := by
  refine ⟨fun v => hx.1 v.val, ?_⟩
  intro r hr
  have hrR : r.val ∈ initialDemands G d := Finset.mem_subtype.mp hr
  rw [InducedCover.closed_sum G (zone G d) r x (demand_closed_subset_zone G d hrR)]
  have hs := hx.2.2 r.val hrR
  change 1 ≤ ∑ v ∈ closed G r.val ∩ zone G d, x v at hs
  rwa [Finset.inter_eq_left.mpr (demand_closed_subset_zone G d hrR)] at hs

theorem restriction_cost (x : V → ℝ) (hx : feasible (auxiliary G d) x) :
    cost (auxiliary G d) x = PartialOptimum.objective (weights G d) (fun v => x v.val) := by
  have he : InducedExtension.extend (zone G d) (fun v => x v.val) = x := by
    funext v
    by_cases hv : v ∈ zone G d
    · exact dif_pos hv
    · have hz := hx.2.1 v hv
      simpa only [InducedExtension.extend, dif_neg hv] using hz.symm
  calc
    _ = cost (auxiliary G d) (InducedExtension.extend (zone G d) (fun v => x v.val)) := congrArg _ he.symm
    _ = _ := extension_cost G d _

theorem values_eq :
    PartialOptimum.values (G.induce (zone G d : Set V)) (demands G d) (weights G d) = auxiliaryFeasibleCosts G d := by
  ext t
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨InducedExtension.extend (zone G d) z, to_auxiliary G d z hz, (extension_cost G d z).trans he⟩
  · rintro ⟨x, hx, he⟩
    exact ⟨fun v => x v.val, from_auxiliary G d x hx, (restriction_cost G d x hx).symm.trans he⟩

theorem number_eq :
    PartialOptimum.number (G.induce (zone G d : Set V)) (demands G d) (weights G d) = auxiliaryNumber G d :=
  congrArg sInf (values_eq G d)
end Paper.AuxiliaryGraph
