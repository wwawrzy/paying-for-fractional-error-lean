import Paper.Optimality.Treewidth.Pathwidth
import Paper.Optimality.Treewidth.TreewidthBroadcast

/-! The exact constant-round encoded broadcast upper bound for pathwidth.
The public configuration depends on r, before graphs, ports and identifiers. -/
namespace Paper.PathwidthBroadcast

open SevenFoundation BroadcastModel

theorem exact_KT0 (r : ℕ) (hr : 1 ≤ r) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        Pathwidth.width G ≤ r → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ (2 * (r : ℝ) + 1) * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  obtain ⟨p, hp⟩ := TreewidthBroadcast.exact_KT0 r hr
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  exact hp G (Pathwidth.treeWidth_le_width.trans hG) ports C

end Paper.PathwidthBroadcast

#print axioms Paper.PathwidthBroadcast.exact_KT0
