import Paper.Partitions.Local.DeterministicPartitionBroadcast

/-! One deterministic stage with all candidate-color premises discharged
from a supplied distance-2k vertex coloring. This is a component theorem:
no distributed computation of that input coloring is claimed. -/
namespace Paper.DeterministicPartitionStage
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem remaining_bound {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ 1 / (t : ℝ))
    (Φ : ℕ) (χ : V → Fin Φ) (fallback : V)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) :
    (2 * k * (k * 2 ^ ((Δ + 1) ^ k))) *
        (DeterministicPartitionProgress.next (fun v => G.neighborFinset v) S k t
          (DeterministicPartitionColors.color (fun v => G.neighborFinset v) Δ k fallback Φ χ)
          (Φ * 2 ^ ((Δ + 1) ^ k))).card ≤
      (2 * k * (k * 2 ^ ((Δ + 1) ^ k)) - 1) * S.card := by
  apply DeterministicPartitionProgress.remaining_bound G hC hprofile Δ hdeg k hk t ht hparam
  · exact DeterministicPartitionColors.proper_eligible G Δ k hdeg fallback Φ χ hpower S t
  · intro U hU
    exact DeterministicPartitionColors.palette _ Δ k fallback Φ χ U

end Paper.DeterministicPartitionStage

#print axioms Paper.DeterministicPartitionStage.remaining_bound
