import Paper.Endpoints.Components.SmallComponentPhysicalCost
import Paper.Endpoints.Components.ComponentOptimumCost
set_option maxHeartbeats 200000
namespace Paper.ActualComponentReplacementCost

theorem selected_component_cost_le
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed G r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (A0 : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => A0.runEncoded G s u = true)))
    (v : V) (hv : v ∈ X.supp)
    (hsolved : ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded
      G s v).1 = true) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    let D := H.filter (fun u => ((Paper.SmallComponentProgram.program ids a B K hB).runEncoded
      G s u).2 = true)
    D.sum (fun u => (s u).cost.val) ≤
      ((Finset.univ.filter (fun u => A0.runEncoded G s u = true)) ∩ H).sum
        (fun u => (s u).cost.val) := by
  have heq := Paper.SmallComponentPhysicalCost.physical_selected_cost_eq_optimum G cover targets R
    hinc hlocal a ha hden B K hB ids s hd hC ht X hc v hv hsolved
  apply heq.le.trans
  apply Paper.ComponentOptimumCost.component_optimum_le_cover_cost cover R
    (Finset.univ.filter (fun u => A0.runEncoded G s u = true))
    (fun u => (s u).cost.val) X hcover0

end Paper.ActualComponentReplacementCost

#print axioms Paper.ActualComponentReplacementCost.selected_component_cost_le
