import Paper.Endpoints.Components.SmallComponentRealDensity
import Paper.Endpoints.Components.SmallComponentOptimumDiameter
set_option maxHeartbeats 200000
namespace Paper.SmallComponentExactEndpoint

theorem endpoint
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
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (c : Nat) (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    let P := Paper.SmallComponentProgram.portProgram ids (Nat.ceil a) B K hB
    let H := Paper.IncidenceComponent.vertices (Paper.CoveringIncidence.graph cover R) X
    let out := P.runEncoded G ports s
    P.rounds = 1 + Paper.SmallComponentProgram.roundBound (Nat.ceil a) K ∧
    P.maxBits ≤ max c (Paper.SmallComponentProgram.messageConstant (Nat.ceil a) B K c) *
      Nat.clog 2 (Fintype.card V + 2) ∧
    ((∀ v ∈ X.supp, ∀ u ∈ X.supp, (out v).1 = (out u).1) ∧
    (∀ v ∈ X.supp, (out v).1 = true →
      let D := H.filter (fun u => (out u).2 = true)
      Paper.IntegralCoverOptimum.Feasible cover (R ∩ H) D ∧
        Paper.IntegralCoverOptimum.cost (fun u => (s u).cost.val) D =
          Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val)) ∧
    (Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val) ≤ K →
      ∀ v ∈ X.supp, (out v).1 = true) ∧
    (∀ v, (out v).2 = true → (out v).1 = true)) ∧
    (Paper.IntegralCoverOptimum.optimum cover (R ∩ H) (fun u => (s u).cost.val) ≤ K →
      (∀ x y : X, X.toSimpleGraph.dist x y ≤ 5 * K - 1) ∧
      ((∀ r ∈ X.supp, r ∈ R) → ∀ x y : X, X.toSimpleGraph.dist x y ≤ 3 * K - 1)) := by
  dsimp only
  refine ⟨Paper.SmallComponentProgram.port_rounds ids (Nat.ceil a) B K hB,
    Paper.SmallComponentProgram.port_logarithmic_bits ids (Nat.ceil a) B K hB
      (Fintype.card V) c hids,
    Paper.SmallComponentRealDensity.real_density_port_correct G ports cover targets R hinc hlocal
      a ha hden B K hB ids s hd hC ht X hc hK hrows, ?_⟩
  intro hopt
  exact Paper.SmallComponentOptimumDiameter.small_optimum_diameter cover R
    (fun u => (s u).cost.val) X K hK hrows hc hopt

end Paper.SmallComponentExactEndpoint

#print axioms Paper.SmallComponentExactEndpoint.endpoint
