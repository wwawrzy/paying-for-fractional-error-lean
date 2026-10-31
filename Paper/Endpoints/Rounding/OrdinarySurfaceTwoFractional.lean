import GraphTheory.Surfaces.OrdinarySurface
import Paper.Endpoints.Rounding.SurfaceTwoFractional
namespace Paper.OrdinarySurfaceTwoFractional
open BroadcastModel SevenFoundation
theorem parameters :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      SimpleGraph.OrdinarySurface.HasEulerGenusAtMost G 2 →
      ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
      dominates G (MinorDensityKT0.output G ports C p) ∧
        ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ 7*fractionalNumber G ∧
        (MinorDensityKT0.program C p).rounds = 1+MinorDensityBroadcast.roundBound p ∧
        ∀ n c : ℕ, b ≤ c*Nat.clog 2 (n+2) →
          (MinorDensityKT0.program C p).maxBits ≤
            max c (MinorDensityBroadcast.messageConstant p c)*Nat.clog 2 (n+2) := by
  obtain ⟨p,hp⟩ := SurfaceTwoFractional.parameters
  refine ⟨p,?_⟩
  intro V _ _ G _ hsurface
  exact hp G (SimpleGraph.OrdinarySurface.signedRotation_of_genus G 2 hsurface)
end Paper.OrdinarySurfaceTwoFractional
#print axioms Paper.OrdinarySurfaceTwoFractional.parameters
