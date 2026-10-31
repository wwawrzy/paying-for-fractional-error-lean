import Paper.Endpoints.Components.SmallComponentSelectedOptimal
import Paper.Endpoints.Components.OptimumCertificate
set_option maxHeartbeats 200000
namespace Paper.SmallComponentSelectedCost

theorem logical_selected_cost_eq_optimum
    {V : Type} [Fintype V] [LinearOrder V]
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (a : Nat) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound (Paper.CoveringIncidence.graph cover R) (a : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (v : V) (hv : v ∈ X.supp)
    (hsolved : ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s v).1 = true) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    let D := H.filter (fun u => ((Paper.SmallComponentProgram.logical ids a B K hB).runEncoded
      (Paper.CoveringIncidence.graph cover R) s u).2 = true)
    D.sum (fun u => (s u).cost.val) =
      Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val) := by
  classical
      dsimp only
      obtain ⟨hadm, hcover, _, hmin⟩ :=
        Paper.SmallComponentSelectedOptimal.logical_selected_optimal cover targets R hinc
          a ha hden B K hB ids s hd hC ht X hc v hv hsolved
      exact Paper.IntegralCoverOptimum.cost_eq_optimum cover _ _ _
        ⟨hadm, hcover⟩ (fun O hO => hmin O hO.1 hO.2)

end Paper.SmallComponentSelectedCost

#print axioms Paper.SmallComponentSelectedCost.logical_selected_cost_eq_optimum
