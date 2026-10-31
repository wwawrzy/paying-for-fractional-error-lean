import Paper.Endpoints.Girth.HighGirthThreeEndpoint
import Paper.Preliminaries.MaskedLPOptimum

/-! The exact high-girth auxiliary problem as a weighted partial LP on
original identifiers, with nonparticipating vertices isolated. -/
namespace Paper.HighGirthMaskedInput
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def graph : SimpleGraph V := MaskedTaskGraph.graph G (HighGirthTransformation.zone G)

instance : DecidableRel (graph G).Adj := MaskedTaskGraph.maskedAdj G _

noncomputable def weight (v : V) : Fin 4 :=
  if h : v ∈ HighGirthTransformation.zone G then
    ⟨HighGirthTransformation.candidateCost G v,
      Nat.lt_succ_of_le (HighGirthCostBounds.candidate_cost_bounds G v h).2.1⟩
  else ⟨1, by decide⟩

noncomputable def weights (v : V) : Real := (weight G v).val

noncomputable def capped (y : V → Real) : V → Real :=
  HighGirthAuxiliary.restrict G (PartialOptimum.cap y)

theorem weight_pos (v : V) : 1 ≤ (weight G v).val := by
  classical
  unfold weight
  split_ifs with h
  · exact (HighGirthCostBounds.candidate_cost_bounds G v h).1
  · exact le_rfl

theorem weight_at (v : V) (hv : v ∈ HighGirthTransformation.zone G) :
    weights G v = (HighGirthTransformation.candidateCost G v : Real) := by
  classical
  simp [weights, weight, hv]

theorem closed_at_demand (r : V) (hr : r ∈ HighGirthTransformation.demands G) :
    closed (graph G) r = closed G r ∩ HighGirthTransformation.zone G :=
  MaskedTaskGraph.closed_inside G _ r (Finset.mem_sdiff.mp hr).1

end Paper.HighGirthMaskedInput
#print axioms Paper.HighGirthMaskedInput.weight_pos
#print axioms Paper.HighGirthMaskedInput.weight_at
#print axioms Paper.HighGirthMaskedInput.closed_at_demand
