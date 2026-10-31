import Paper.Partitions.Local.FinitePartitionDistribution
import Paper.Owners.Construction.PrunedOwnerStructure

/-! An actual finite distribution of connected small-part partitions of
the pruned owner graph, with exact mean cut at most η times its order. -/
namespace Paper.OwnerPartitionDistribution
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h)
    {η : ℝ} (hη : 0 < η) :
    let W := {v : D // v ∉ HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ}
    let K : SimpleGraph W := HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ
    ∃ k b n : ℕ, ∃ hk : 0 < k, ∀ S : Finset W,
      (∑ ω : FiniteIteration.Seeds (Finset W → Fin (2 ^ b)) n,
        (PriorityCut.cut K k hk (η / 8) S n ω : ℝ)) ≤
        η * (Fintype.card (Finset W → Fin (2 ^ b)) : ℝ) ^ n * S.card := by
  dsimp only
  obtain ⟨hC, hprofile, hdeg⟩ := PrunedOwnerStructure.spec G D R L Δ hL hden ha h hh
  exact FinitePartitionDistribution.spec _ hC.le hprofile Δ hdeg hη
end Paper.OwnerPartitionDistribution
