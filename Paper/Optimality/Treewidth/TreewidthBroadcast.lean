import Paper.Optimality.Treewidth.TreewidthDensity
import Paper.Endpoints.Rounding.MinorDensityKT0

/-! Treewidth t gives exact (2t+1)*gamma_f in encoded constant-round BC.
The decomposition is a proof witness only, never an algorithm input.
KT1 counts and the proved one-round KT0 initialization are separate. -/
namespace Paper.TreewidthBroadcast
open SevenFoundation BroadcastModel

theorem exact_KT1 (t : ℕ) (ht : 1 ≤ t) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.treeWidth ≤ t → ∀ {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityBroadcast.output G C p) ∧
          ((MinorDensityBroadcast.output G C p).card : ℝ) ≤ (2 * (t : ℝ) + 1) * fractionalNumber G ∧
          (MinorDensityBroadcast.program C p).rounds = MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityBroadcast.program C p).maxBits ≤
              MinorDensityBroadcast.messageConstant p c * Nat.clog 2 (n + 2) := by
  have htQ : (1 : ℚ) ≤ t := by exact_mod_cast ht
  obtain ⟨p, hp⟩ := MinorDensityBroadcast.exact_minor_density (t : ℚ) htQ
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG b C
  have hden : MinorDensity.Bound G ((t : ℚ) : ℝ) := by
    simpa only [Rat.cast_natCast] using TreewidthDensity.minor_density G t hG
  simpa only [Rat.cast_natCast] using hp G hden C

theorem exact_KT0 (t : ℕ) (ht : 1 ≤ t) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.treeWidth ≤ t → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ (2 * (t : ℝ) + 1) * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  have htQ : (1 : ℚ) ≤ t := by exact_mod_cast ht
  obtain ⟨p, hp⟩ := MinorDensityKT0.exact_minor_density (t : ℚ) htQ
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  have hden : MinorDensity.Bound G ((t : ℚ) : ℝ) := by
    simpa only [Rat.cast_natCast] using TreewidthDensity.minor_density G t hG
  simpa only [Rat.cast_natCast] using hp G hden ports C

end Paper.TreewidthBroadcast
