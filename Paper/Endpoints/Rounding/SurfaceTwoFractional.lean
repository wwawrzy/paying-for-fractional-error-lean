import GraphTheory.Surfaces.SignedRotationMinorGenus
import GraphTheory.Surfaces.SignedRotationDensity
import Paper.Endpoints.Rounding.MinorDensityKT0
namespace Paper.SurfaceTwoFractional
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
theorem minor_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : SimpleGraph.SignedRotation G) (hr : r.eulerGenus ≤ 2) : MinorDensity.Bound G 3 := by
  intro W _ _ H _ hm
  obtain ⟨s,hs⟩ := SimpleGraph.SignedRotation.exists_minor_genus_le G r H hm
  have hh := s.edge_bound (hs.trans hr)
  exact_mod_cast hh

theorem parameters :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∃ r : SimpleGraph.SignedRotation G, r.eulerGenus ≤ 2) →
      ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
      dominates G (MinorDensityKT0.output G ports C p) ∧
        ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ 7*fractionalNumber G ∧
        (MinorDensityKT0.program C p).rounds = 1+MinorDensityBroadcast.roundBound p ∧
        ∀ n c : ℕ, b ≤ c*Nat.clog 2 (n+2) →
          (MinorDensityKT0.program C p).maxBits ≤
            max c (MinorDensityBroadcast.messageConstant p c)*Nat.clog 2 (n+2) := by
  obtain ⟨p,hp⟩ := MinorDensityKT0.exact_minor_density 3 (by norm_num)
  refine ⟨p,?_⟩
  intro V _ _ G _ hrot ports b C
  obtain ⟨r,hr⟩ := hrot
  have hh := hp G (minor_density G r hr) ports C
  norm_num at hh
  exact hh
end Paper.SurfaceTwoFractional
#print axioms Paper.SurfaceTwoFractional.minor_density
#print axioms Paper.SurfaceTwoFractional.parameters
