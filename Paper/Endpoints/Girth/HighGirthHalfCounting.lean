import Paper.Endpoints.Girth.HighGirthUnattachedEndpoint

/-! True aggregate charge budget and its explicitly conditional counting step.
The per-component half-slack condition is not proved here for all special paths
from fv:hg:half; this module must not certify the whole named assertion. -/
namespace Paper.HighGirthHalfCounting

theorem aggregate_budget
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (family : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent) :
    (∑ K ∈ family, (HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K)) ≤
      2 * HighGirthRounding.penalty G x + HighGirthRounding.oversupply G x := by
  rw [Finset.sum_add_distrib]
  exact add_le_add (HighGirthChargePacking.component_positive_charge_bound G x hx family)
    (HighGirthExcessPacking.component_row_excess_bound G x hx family)

theorem count_of_half_slack
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Real)
    (hx : SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) x)
    (family : Finset (G.induce (↑(HighGirthRounding.last G x) : Set V)).ConnectedComponent)
    (hslack : ∀ K ∈ family, (1 : Real) / 2 ≤
      HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K) :
    (family.card : Real) ≤ 4 * HighGirthRounding.penalty G x + 2 * HighGirthRounding.oversupply G x := by
  have hlo : (family.card : Real) / 2 ≤
      ∑ K ∈ family, (HighGirthPathCharges.positiveCharge G x K + HighGirthPathCharges.rowExcess G x K) := by
    calc
      _ = ∑ _K ∈ family, (1 : Real) / 2 := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum hslack
  have hhi := aggregate_budget G x hx family
  linarith

end Paper.HighGirthHalfCounting

#print axioms Paper.HighGirthHalfCounting.aggregate_budget
#print axioms Paper.HighGirthHalfCounting.count_of_half_slack
