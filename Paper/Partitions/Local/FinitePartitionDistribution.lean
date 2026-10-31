import Paper.Partitions.Local.PriorityCut
import Paper.Partitions.Local.PriorityIteration
import Paper.Partitions.Local.PartitionParameters

/-! Actual connected small-part partitions from a finite product of local
priorities, with arbitrarily small exact mean cut. Full broadcast execution
and the local bounded indexing of priority coordinates are separate steps. -/
namespace Paper.FinitePartitionDistribution
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem spec {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) {η : ℝ} (hη : 0 < η) :
    ∃ k b n : ℕ, ∃ hk : 0 < k, ∀ S : Finset V,
      (∑ ω : FiniteIteration.Seeds (Finset V → Fin (2 ^ b)) n,
        (PriorityCut.cut G k hk (η / 8) S n ω : ℝ)) ≤
        η * (Fintype.card (Finset V → Fin (2 ^ b)) : ℝ) ^ n * S.card := by
  let ε := η / 8
  have hε : 0 < ε := by dsimp only [ε]; positivity
  let δ := η / ((Δ : ℝ) + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨k, hk, hparam⟩ := PartitionParameters.exists_size C Δ hε
  let b := 2 * (k * 2 ^ ((Δ + 1) ^ k))
  let Q := 2 ^ b
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hsize : 2 * (k * 2 ^ ((Δ + 1) ^ k)) ≤ Q := (show b < 2 ^ b from Nat.lt_two_pow_self).le
  obtain ⟨n, hn⟩ := PriorityIteration.exists_stages Q hQ hδ
  refine ⟨k, b, n, hk, fun S => ?_⟩
  have hremaining := PriorityIteration.remaining G hC hprofile Δ hdeg k hk hε hparam Q hQ hsize n S
  have hr : (∑ ω : FiniteIteration.Seeds (Finset V → Fin Q) n,
      ((FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card : ℝ)) ≤
      δ * (Fintype.card (Finset V → Fin Q) : ℝ) ^ n * S.card :=
    hremaining.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (by positivity)) (Nat.cast_nonneg _))
  have hcut := PriorityCut.finite_mean G Δ hdeg k hk hε.le S n hr
  have he : ((Δ : ℝ) + 1) * δ = η := by dsimp only [δ]; field_simp
  have hcoefficient : 4 * ε + (Δ : ℝ) / 2 * δ ≤ η := by dsimp only [ε]; nlinarith [hδ.le]
  exact hcut.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoefficient (by positivity)) (Nat.cast_nonneg _))
end Paper.FinitePartitionDistribution
