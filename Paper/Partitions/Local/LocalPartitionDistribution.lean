import Paper.Preliminaries.LocalSourceDistribution
import Paper.Partitions.Local.FinitePartitionDistribution

/-! Actual finite partition distribution with a bounded independent source
at every owner: n stages and 2^((Δ+1)^k) priority words per stage.
The uniform transfer proves the mean cut bound for this exact source. -/
namespace Paper.LocalPartitionDistribution
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
local instance vertexEq : DecidableEq V := Classical.decEq _

def Bound (Δ : ℕ) (η : ℝ) : Prop :=
  ∃ k b n : ℕ, ∃ hk : 0 < k, ∀ S : Finset V,
    (∑ ω : (Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b),
      (PriorityCut.cut G k hk (η / 8) S n
        (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n ω) : ℝ)) ≤
      η * Fintype.card ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)) * S.card

theorem spec {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) {η : ℝ} (hη : 0 < η) :
    ∃ k b n : ℕ, ∃ hk : 0 < k, ∀ S : Finset V,
      (∑ ω : (Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b),
        (PriorityCut.cut G k hk (η / 8) S n
          (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n ω) : ℝ)) ≤
        η * Fintype.card ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)) * S.card := by
  letI : DecidableEq V := Classical.decEq V
  obtain ⟨k, b, n, hk, hfull⟩ := FinitePartitionDistribution.spec G hC hprofile Δ hdeg hη
  refine ⟨k, b, n, hk, fun S => ?_⟩
  have hf : (∑ ω : FiniteIteration.Seeds (Finset V → Fin (2 ^ b)) n,
      (PriorityCut.cut G k hk (η / 8) S n ω : ℝ)) ≤
      (Fintype.card (Finset V → Fin (2 ^ b)) : ℝ) ^ n * (η * S.card) := by
    calc
      _ ≤ η * (Fintype.card (Finset V → Fin (2 ^ b)) : ℝ) ^ n * S.card := by
        with_reducible exact hfull S
      _ = _ := by ring
  have hb := LocalSourceDistribution.transfer G Δ hdeg k hk (η / 8) (2 ^ b) (by positivity) S n (η * S.card) hf
  nlinarith

theorem bound_of_profile {C : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) {η : ℝ} (hη : 0 < η) : Bound G Δ η :=
  spec G hC hprofile Δ hdeg hη

theorem source_card (Δ k b n : ℕ) :
    Fintype.card ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)) =
      2 ^ ((n * b * 2 ^ ((Δ + 1) ^ k)) * Fintype.card V) := by
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, PriorityNormalization.Coordinate,
    Fintype.card_bool]
  rw [← pow_mul]
  congr 1
  ring
end
end Paper.LocalPartitionDistribution
