import Paper.Endpoints.Components.SmallComponentPortCorrectness
import Paper.Endpoints.Components.ComponentDensity
set_option maxHeartbeats 200000
namespace Paper.SmallComponentRealDensity

theorem real_density_port_correct
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed G r)
    (a : Real) (ha : 1 ≤ a)
    (hden : Paper.Incidence.InducedDensityBound G a)
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (X : (Paper.CoveringIncidence.graph cover R).ConnectedComponent)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty) :
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    let out := (Paper.SmallComponentProgram.portProgram ids (Nat.ceil a) B K hB).runEncoded G ports s
    (∀ v ∈ X.supp, ∀ u ∈ X.supp, (out v).1 = (out u).1) ∧
    (∀ v ∈ X.supp, (out v).1 = true →
      let D := H.filter (fun u => (out u).2 = true)
      Paper.IntegralCoverOptimum.Feasible cover (R ∩ H) D ∧
        Paper.IntegralCoverOptimum.cost (fun u => (s u).cost.val) D =
          Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val)) ∧
    (Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val) ≤ K →
      ∀ v ∈ X.supp, (out v).1 = true) ∧
    (∀ v, (out v).2 = true → (out v).1 = true) := by
  obtain ⟨hp, hdenI⟩ := Paper.ComponentDensity.ceil_bound G
    (Paper.CoveringIncidence.graph cover R) (Paper.CoveringIncidence.graph_le G cover R hlocal)
    a ha hden
  exact Paper.SmallComponentPortCorrectness.port_correct G ports cover targets R hinc hlocal
    (Nat.ceil a) hp hdenI B K hB ids s hd hC ht X hc hK hrows

end Paper.SmallComponentRealDensity

#print axioms Paper.SmallComponentRealDensity.real_density_port_correct
