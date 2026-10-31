import Paper.Communication.ZoneProgram
import Paper.Preliminaries.MaskedLPOptimum
import Paper.Endpoints.Rounding.AuxiliaryGraph

/-! Restrict the real masked-zone solver output to the auxiliary cover.
Its weighted optimum is exactly the paper's auxiliary optimum. -/
namespace Paper.AuxiliaryFromMasked
open SevenFoundation WeightedBudget
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def weights (d : ℕ) (v : V) : ℝ := ((ZoneProgram.expected G d v).cost.val : ℝ)

theorem weights_eq (d : ℕ) (v : ↥(zone G d : Set V)) :
    weights G d v.val = AuxiliaryGraph.weights G d v := ZoneProgram.cost_correct G d v.property

theorem optimum (d : ℕ) :
    PartialOptimum.number (MaskedTaskGraph.graph G (zone G d)) (initialDemands G d) (weights G d) =
      auxiliaryNumber G d := by
  rw [MaskedLPOptimum.number_eq G (zone G d) (initialDemands G d) (AuxiliaryGraph.demands_subset G d)
    (weights G d) (fun _ => Nat.cast_nonneg _)]
  have he : (fun v : ↥(zone G d : Set V) => weights G d v.val) = AuxiliaryGraph.weights G d :=
    funext (weights_eq G d)
  rw [he]
  exact AuxiliaryGraph.number_eq G d

theorem spec (d : ℕ) (y : V → ℝ)
    (hy : PartialOptimum.Feasible (MaskedTaskGraph.graph G (zone G d)) (initialDemands G d) y)
    (δ : ℝ)
    (hc : PartialOptimum.objective (weights G d) y ≤ (1 + δ) *
      PartialOptimum.number (MaskedTaskGraph.graph G (zone G d)) (initialDemands G d) (weights G d)) :
    feasible (auxiliary G d) (fun v => if v ∈ zone G d then y v else 0) ∧
      cost (auxiliary G d) (fun v => if v ∈ zone G d then y v else 0) ≤
        (1 + δ) * auxiliaryNumber G d := by
  let z : ↥(zone G d : Set V) → ℝ := fun v => y v.val
  have hz := MaskedLP.restrict_feasible G (zone G d) (initialDemands G d)
    (AuxiliaryGraph.demands_subset G d) y hy
  have he : InducedExtension.extend (zone G d) z = (fun v => if v ∈ zone G d then y v else 0) := by
    funext v
    unfold InducedExtension.extend
    split_ifs <;> rfl
  refine ⟨he ▸ AuxiliaryGraph.to_auxiliary G d z hz, ?_⟩
  rw [← he, AuxiliaryGraph.extension_cost]
  have hw : AuxiliaryGraph.weights G d = (fun v : ↥(zone G d : Set V) => weights G d v.val) :=
    (funext (weights_eq G d)).symm
  rw [hw]
  exact (MaskedLP.restrict_cost_le (zone G d) (weights G d) y (fun _ => Nat.cast_nonneg _) hy.1).trans
    (by simpa only [optimum G d] using hc)

end Paper.AuxiliaryFromMasked
