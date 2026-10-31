import Paper.Partitions.Local.LocalPartitionDistribution
import Paper.Owners.Construction.BoundaryOwners

/-! Package the actual bounded local source and its output partitions as
finite data with the proved boundary budget. This is constructed data. -/
namespace Paper.FinitePartitionLaw
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
local instance vertexEq : DecidableEq V := Classical.decEq _

structure Data (η : ℝ) where
  Ω : Type u
  [fintype : Fintype Ω]
  [nonempty : Nonempty Ω]
  k : ℕ
  hk : 0 < k
  partition : Ω → SmallParts.Data G Finset.univ k
  boundary : (∑ ω : Ω, ((BoundaryOwners.vertices G Finset.univ (partition ω).parts).card : ℝ)) ≤
    Fintype.card Ω * (2 * η * Fintype.card V)

attribute [instance] Data.fintype Data.nonempty

set_option maxHeartbeats 1000000 in
theorem of_bound (Δ : ℕ) {η : ℝ} (hbound : LocalPartitionDistribution.Bound G Δ η) : Nonempty (Data G η) := by
  letI : DecidableEq V := Classical.decEq V
  obtain ⟨k, b, n, hk, hcut⟩ := hbound
  let Ω := (Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)
  letI : Fintype Ω := inferInstanceAs (Fintype ((Fin n × PriorityNormalization.Coordinate V Δ k) → Fin (2 ^ b)))
  letI : Nonempty Ω := ⟨fun _ => ⟨0, by positivity⟩⟩
  let P : Ω → SmallParts.Data G Finset.univ k := fun ω => PriorityPartition.partition G k hk (η / 8) Finset.univ n
    (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n ω)
  refine ⟨{ Ω := Ω, k := k, hk := hk, partition := P, boundary := ?_ }⟩
  have hb : ∀ ω : Ω, ((BoundaryOwners.vertices G Finset.univ (P ω).parts).card : ℝ) ≤
      2 * (PriorityCut.cut G k hk (η / 8) Finset.univ n
        (PriorityNormalization.localSeed G Δ k (2 ^ b) (by positivity) n ω) : ℝ) := by
    intro ω
    exact_mod_cast BoundaryOwners.count G Finset.univ (P ω).parts
  have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => hb ω)
  rw [← Finset.mul_sum] at hs
  have hc := hcut (Finset.univ : Finset V)
  simp only [Finset.card_univ] at hc
  have hm := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
  nlinarith
end
end Paper.FinitePartitionLaw
