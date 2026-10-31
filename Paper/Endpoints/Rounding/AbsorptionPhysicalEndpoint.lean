import Paper.Endpoints.Rounding.AbsorptionRuntimeBound
import Paper.Endpoints.Rounding.AbsorptionPortResources
import Paper.Endpoints.Components.ComponentDensity
set_option maxHeartbeats 200000
namespace Paper.AbsorptionPhysicalEndpoint

theorem absorption_physical_endpoint
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ports : Paper.PortBroadcastModel.Numbering G)
    (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ Paper.SevenFoundation.closed G r)
    (rho : Rat) (hrho : 1 ≤ rho)
    (hden : Paper.Incidence.InducedDensityBound G (rho : Real))
    (B K : Nat) (hB : 1 ≤ B) {bits : Nat} (ids : Paper.BroadcastModel.BitCode V bits)
    (s : V → Paper.GeneralCoveringFractional.Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ x ∈ Paper.CoveringSupport.admissible cover R, 1 ≤ (s x).cost.val)
    (hK : 1 ≤ K) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (A0 : Paper.BroadcastModel.Program V (Paper.GeneralCoveringFractional.Input V B) Bool)
    (hcover0 : Paper.GeneralCoveringIntegral.Covers cover R
      (Finset.univ.filter (fun u => A0.runEncoded G s u = true)))
    (r epsilon : Real) (q : Nat) (delta : Rat)
    (hr : 1 ≤ r) (hepsilon : 0 < epsilon) (hdelta_pos : 0 < delta)
    (hdelta : (delta : Real) ≤ epsilon / (2 * r))
    (hthreshold : 2 * (q : Real) / epsilon ≤ (K : Real))
    (happrox : (((Finset.univ.filter (fun u => A0.runEncoded G s u = true)).sum
      (fun u => (s u).cost.val) : Nat) : Real) ≤
      r * (1 + (delta : Real)) * Paper.CoveringOptimum.number cover R
        (fun u => ((s u).cost.val : Real)) + (q : Real))
    (cid C : Nat)
    (hids : bits ≤ cid * Nat.clog 2 (Fintype.card V + 2))
    (hA0 : A0.maxBits ≤ C * Nat.clog 2 (Fintype.card V + 2)) :
    let Q := Paper.ComponentReplacementProgram.program A0
      (Paper.SmallComponentProgram.program ids (Nat.ceil (rho : Real)) B K hB)
    let P := Paper.KT0Compiler.program ids Q
    let D := Finset.univ.filter (fun u => P.runEncoded G ports s u = true)
    Paper.GeneralCoveringIntegral.Covers cover R D ∧
      ((D.sum (fun u => (s u).cost.val) : Nat) : Real) ≤
        (r + epsilon) * (Paper.IntegralCoverOptimum.optimum cover R
          (fun u => (s u).cost.val) : Real) ∧
      P.rounds = 1 + (A0.rounds + Paper.SmallComponentProgram.roundBound
        (Nat.ceil (rho : Real)) K) ∧
      P.maxBits ≤ max cid (max C (Paper.SmallComponentProgram.messageConstant
        (Nat.ceil (rho : Real)) B K cid)) * Nat.clog 2 (Fintype.card V + 2) := by
  have hrhoR : (1 : Real) ≤ (rho : Real) := by exact_mod_cast hrho
  obtain ⟨ha, hdenI⟩ := Paper.ComponentDensity.ceil_bound G
    (Paper.CoveringIncidence.graph cover R) (Paper.CoveringIncidence.graph_le G cover R hlocal)
    (rho : Real) hrhoR hden
  have hcorrect := Paper.AbsorptionRuntimeBound.absorption_runtime_bound G cover targets R hinc hlocal
    (Nat.ceil (rho : Real)) ha hdenI B K hB ids s hd hC ht hc hK hrows A0 hcover0
    r epsilon q delta hr hepsilon hdelta_pos hdelta hthreshold happrox
  have hresources := Paper.AbsorptionPortResources.absorption_port_resources G ports
    (Nat.ceil (rho : Real)) B K hB ids A0 s (Fintype.card V) cid C hids hA0
  dsimp only
  refine ⟨?_, ?_, hresources.2.1, hresources.2.2⟩
  · simpa only [Paper.KT0Compiler.program_encoded_correct] using hcorrect.1
  · simpa only [Paper.KT0Compiler.program_encoded_correct] using hcorrect.2

end Paper.AbsorptionPhysicalEndpoint

#print axioms Paper.AbsorptionPhysicalEndpoint.absorption_physical_endpoint
