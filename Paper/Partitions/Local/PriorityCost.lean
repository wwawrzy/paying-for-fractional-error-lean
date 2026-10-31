import Paper.Partitions.Local.PriorityStage
import Paper.Preliminaries.FiniteIteration

/-! Every outcome of the finite priority process has a telescoping boundary
budget. The only remaining cut budget comes from the final residual. -/
namespace Paper.PriorityCost
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def stage (S : Finset V) (k : ℕ) (ε : ℝ) {Q : ℕ} (ω : Finset V → Fin Q) : ℝ :=
  ∑ U ∈ SparsePriority.accepted (EligibleSets.family G S k ε) ω, (PartBoundaries.boundary G S U : ℝ)

theorem stage_bound (S : Finset V) (k : ℕ) (ε : ℝ) {Q : ℕ} (ω : Finset V → Fin Q) :
    stage G S k ε ω ≤ 4 * ε * ((SparsePriority.removed (EligibleSets.family G S k ε) ω).card : ℝ) := by
  have hcard := SparsePriority.removed_card (EligibleSets.family G S k ε) ω
  have hreal : ((SparsePriority.removed (EligibleSets.family G S k ε) ω).card : ℝ) =
      ∑ U ∈ SparsePriority.accepted (EligibleSets.family G S k ε) ω, (U.card : ℝ) := by exact_mod_cast hcard
  rw [hreal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U hU
  exact ((EligibleSets.mem_family G S U k ε).mp (Finset.mem_filter.mp hU).1).2.2.2

noncomputable def total (k : ℕ) (ε : ℝ) {Q : ℕ} (S : Finset V) :
    (n : ℕ) → FiniteIteration.Seeds (Finset V → Fin Q) n → ℝ
  | 0, _ => 0
  | n + 1, ω => stage G S k ε ω.1 + total k ε (PriorityStage.next G S k ε ω.1) n ω.2

theorem telescoping (k : ℕ) (ε : ℝ) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) :
    total G k ε S n ω ≤ 4 * ε * ((S.card : ℝ) -
      (FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω) S n ω).card) := by
  induction n generalizing S with
  | zero => simp [total, FiniteIteration.run]
  | succ n ih =>
    have hb := stage_bound G S k ε ω.1
    have hs := PriorityStage.card_split G S k ε ω.1
    have hsreal : ((PriorityStage.next G S k ε ω.1).card : ℝ) +
        (SparsePriority.removed (EligibleSets.family G S k ε) ω.1).card = S.card := by exact_mod_cast hs
    have hr := ih (PriorityStage.next G S k ε ω.1) ω.2
    have hsreal' := congrArg (fun x : ℝ => 4 * ε * x) hsreal
    change stage G S k ε ω.1 + total G k ε (PriorityStage.next G S k ε ω.1) n ω.2 ≤ _
    change _ ≤ 4 * ε * ((S.card : ℝ) -
      (FiniteIteration.run (fun T ω => PriorityStage.next G T k ε ω)
        (PriorityStage.next G S k ε ω.1) n ω.2).card)
    nlinarith

theorem bound (k : ℕ) {ε : ℝ} (hε : 0 ≤ ε) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) : total G k ε S n ω ≤ 4 * ε * S.card := by
  apply (telescoping G k ε S n ω).trans
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) (by positivity)
end Paper.PriorityCost
