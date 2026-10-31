import Paper.Partitions.Local.BoundedBall
import Paper.Preliminaries.EligibleSets
import Paper.Partitions.Local.PriorityAcceptance

/-! The number of competitors of an eligible set is bounded using actual
bounded-degree balls, independently of the order of the graph. -/
namespace Paper.EligibleConflicts
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem bound (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (S U : Finset V) (k : ℕ) (ε : ℝ)
    (hU : U ∈ EligibleSets.family G S k ε) :
    (PriorityAcceptance.conflicts (EligibleSets.family G S k ε) U).card ≤ k * 2 ^ ((Δ + 1) ^ k) := by
  have hsub : PriorityAcceptance.conflicts (EligibleSets.family G S k ε) U ⊆
      U.biUnion (fun v => BoundedBall.smallContaining G v k) := by
    intro T hT
    have hh := Finset.mem_filter.mp hT
    obtain ⟨v, hvU, hvT⟩ := Finset.not_disjoint_iff.mp hh.2.2
    have hTF := (EligibleSets.mem_family G S T k ε).mp hh.1
    exact Finset.mem_biUnion.mpr ⟨v, hvU, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hvT, hTF.2.1, hTF.2.2.1⟩⟩
  calc
    _ ≤ (U.biUnion (fun v => BoundedBall.smallContaining G v k)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ U, (BoundedBall.smallContaining G v k).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ U, 2 ^ ((Δ + 1) ^ k) :=
      Finset.sum_le_sum (fun v _ => BoundedBall.small_count G Δ hdeg v k)
    _ = U.card * 2 ^ ((Δ + 1) ^ k) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ ((EligibleSets.mem_family G S U k ε).mp hU).2.2.1
end Paper.EligibleConflicts
