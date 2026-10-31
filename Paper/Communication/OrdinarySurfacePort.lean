import GraphTheory.Surfaces.OrdinarySurface
import Paper.Communication.SurfaceRotationPort
/-! Actual seven-approximation port algorithm from the ordinary topological
Euler-genus premise. The graph embedding and rotation are used in the proof,
not supplied to the program. Topology assumptions are explicitly reviewed. -/
namespace Paper.OrdinarySurfaceAlgorithm
open BroadcastModel SevenFoundation
theorem parameters (e : ℕ) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e → ∀ {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 7 q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        let a := SurfacePublicParameters.density e
        let K := SurfacePublicParameters.budget e
        let R := SurfaceFinalProgram.portProgram 6 D a K C P
        (∀ ports : PortBroadcastModel.Numbering G,
          let Z := Finset.univ.filter (fun v => R.runEncoded G ports (fun _ => ()) v = true)
          dominates G Z ∧ ∀ Y : Finset V, dominates G Y → Z.card ≤ 7 * Y.card) ∧
        R.rounds = SurfaceFinalProgram.roundConstant a K A r k T M ∧
        ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
          R.maxBits ≤ max c (SurfaceFinalProgram.messageConstant a K A L Δ r k Q T s q M c) *
            Nat.clog 2 (n + 2) := by
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,h⟩ :=
    SurfaceDensityAlgorithm.rotation_port_parameters (e : ℝ) (Nat.cast_nonneg e)
  refine ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,?_⟩
  intro V _ _ G _ hsurface
  exact h G (SimpleGraph.OrdinarySurface.signedRotation_real G e hsurface)
end Paper.OrdinarySurfaceAlgorithm
#print axioms Paper.OrdinarySurfaceAlgorithm.parameters
