import GraphTheory.Surfaces.OrdinarySurface
import Paper.Communication.SurfaceImprovedGirth
namespace Paper.OrdinarySurfaceImprovedGirth
open BroadcastModel SevenFoundation ImprovedExcessSolver
theorem parameters (e : ℕ) (g : ℕ) (hg : 5 ≤ g) (hne : g ≠ 6)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Config (NoncriticalGirth.density g), ∃ K : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G e →
      (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
      ∀ {b : ℕ} (C : BitCode V b),
      let a := Nat.ceil (3+3*(e : ℝ))
      let R := OrdinaryAbsorption.portProgram C a K (ImprovedExcessSolver.program C p)
      (∀ ports : PortBroadcastModel.Numbering G,
        let Z := Finset.univ.filter (fun v => R.runEncoded G ports (fun _ => ()) v = true)
        dominates G Z ∧ ∀ Y : Finset V, dominates G Y →
          (Z.card : ℝ) ≤ (ImprovedGirth.limitingCoefficient g+ε)*Y.card) ∧
      R.rounds = 1+(roundBound p+SmallComponentProgram.roundBound a K) ∧
      ∀ n c : ℕ, b ≤ c*Nat.clog 2 (n+2) →
        R.maxBits ≤ max c (max (messageConstant p c) (SmallComponentProgram.messageConstant a 1 K c))*
          Nat.clog 2 (n+2) := by
  obtain ⟨p,K,hs⟩ := SurfaceImprovedGirth.parameters (e : ℝ) (Nat.cast_nonneg e) g hg hne ε hε
  refine ⟨p,K,?_⟩
  intro V _ _ G _ hsurface
  exact hs G (SimpleGraph.OrdinarySurface.signedRotation_real G e hsurface)
end Paper.OrdinarySurfaceImprovedGirth
#print axioms Paper.OrdinarySurfaceImprovedGirth.parameters
