import Paper.Communication.SurfaceGirthResources
import Paper.Communication.SurfaceGirthAbsorbed
namespace Paper.SurfaceGirthPortParameters
open BroadcastModel SevenFoundation
theorem parameters (e : ℝ) (he : 0 ≤ e) (g : ℕ) (hg3 : 3 ≤ g) (ε : ℝ) (hε : 0 < ε) :
    ∃ A L Δ r k t Q T s q M K : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ rot : SimpleGraph.SignedRotation G, (rot.eulerGenus : ℝ) ≤ e) →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {b : ℕ} (C : BitCode V b),
      let P := CappedWholeProgram.program C A L Δ r k t Q T s q M hQ
      let D := PartialFractionalProgram.denominator Δ k Q T s q
      let R := OrdinaryAbsorption.portProgram C (Nat.ceil (3+3*e)) K (SurfaceGirthSolver.program P D g)
      (∀ ports : PortBroadcastModel.Numbering G,
        let Z := Finset.univ.filter (fun v => R.runEncoded G ports (fun _ => ()) v = true)
        dominates G Z ∧ ∀ Y : Finset V, dominates G Y →
          (Z.card : ℝ) ≤ (3+4/((g : ℝ)-2)+ε)*Y.card) ∧
      R.rounds = SurfaceGirthResources.roundConstant (Nat.ceil (3+3*e)) K A r k T M ∧
      ∀ n c : ℕ, b ≤ c*Nat.clog 2 (n+2) →
        R.maxBits ≤ SurfaceGirthResources.messageConstant (Nat.ceil (3+3*e)) K A L Δ r k Q T s q M c *
          Nat.clog 2 (n+2) := by
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,K,hQ,hq,hs⟩ := SurfaceGirthAbsorbed.parameters e he g hg3 ε hε
  refine ⟨A,L,Δ,r,k,t,Q,T,s,q,M,K,hQ,hq,?_⟩
  intro V _ _ G _ hrot hg b C
  dsimp only
  refine ⟨?_,SurfaceGirthResources.uniform_rounds C _ K g A L Δ r k t Q T s q M hQ,?_⟩
  · intro ports
    rw [OrdinaryAbsorption.port_correct]
    exact hs G hrot hg C
  · intro n c hids
    exact SurfaceGirthResources.logarithmic_bits C _ K g A L Δ r k t Q T s q M hQ n c hids
end Paper.SurfaceGirthPortParameters
#print axioms Paper.SurfaceGirthPortParameters.parameters
