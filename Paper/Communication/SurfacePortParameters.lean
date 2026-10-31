import Paper.Communication.SurfaceDensityAlgorithm
import Paper.Communication.SurfaceResourceBound

namespace Paper.SurfaceDensityAlgorithm
open BroadcastModel SevenFoundation
theorem port_parameters (e : ℝ) (he : 0 ≤ e) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        SurfaceRounding.MinorBound G e → ∀ {b : ℕ} (C : BitCode V b),
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
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,h⟩ := parameters e he
  refine ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,?_⟩
  intro V _ _ G _ hden b C
  dsimp only
  refine ⟨?_, SurfaceFinalProgram.port_uniform_rounds C _ _ A L Δ r k t Q T s q M hQ, ?_⟩
  · intro ports
    rw [SurfaceFinalProgram.port_correct]
    exact h G hden C
  · intro n c hids
    exact SurfaceFinalProgram.port_logarithmic_bits C _ _ A L Δ r k t Q T s q M hQ n c hids
end Paper.SurfaceDensityAlgorithm
