import Paper.Partitions.Local.LocalPartitionDistribution
import Paper.Owners.Construction.PrunedOwnerStructure

/-! The actual owner partition has a finite bounded source at every owner
and the required exact mean cut. Finite-radius execution is still separate. -/
namespace Paper.OwnerLocalPartition
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec (D R : Finset V) (L Δ : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h)
    {η : ℝ} (hη : 0 < η) :
    let W := {v : D // v ∉ HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ}
    let K : SimpleGraph W := HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ
    LocalPartitionDistribution.Bound K Δ η := by
  dsimp only
  obtain ⟨hC, hprofile, hdeg⟩ := PrunedOwnerStructure.spec G D R L Δ hL hden ha h hh
  let W := {v : D // v ∉ HighDegreeCut.high (OwnerInteraction.graph G D R L) Δ}
  let K : SimpleGraph W := HighDegreeCut.pruned (OwnerInteraction.graph G D R L) Δ
  have transport (d e : DecidableEq W) :
      @SeparatorProfile.Bound W d K inferInstance (OwnerSeparator.constant a h L) →
        @SeparatorProfile.Bound W e K inferInstance (OwnerSeparator.constant a h L) := by
    cases Subsingleton.elim d e
    exact id
  with_reducible
    exact LocalPartitionDistribution.bound_of_profile K hC.le (transport _ _ hprofile) Δ hdeg hη
end Paper.OwnerLocalPartition
