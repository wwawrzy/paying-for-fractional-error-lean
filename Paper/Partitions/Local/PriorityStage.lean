import Paper.Preliminaries.EligibleConflicts
import Paper.Partitions.Local.PriorityProgress

/-! One actual local finite-priority stage contracts the expected remaining
region by a fixed factor. All expectations are finite exact sums. -/
namespace Paper.PriorityStage
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def next (S : Finset V) (k : ℕ) (ε : ℝ) {Q : ℕ} (ω : Finset V → Fin Q) : Finset V :=
  S \ SparsePriority.removed (EligibleSets.family G S k ε) ω

theorem removed_subset (S : Finset V) (k : ℕ) (ε : ℝ) {Q : ℕ} (ω : Finset V → Fin Q) :
    SparsePriority.removed (EligibleSets.family G S k ε) ω ⊆ S :=
  SparsePriority.subset _ ω S (fun U hU => ((EligibleSets.mem_family G S U k ε).mp hU).1)

theorem card_split (S : Finset V) (k : ℕ) (ε : ℝ) {Q : ℕ} (ω : Finset V → Fin Q) :
    (next G S k ε ω).card + (SparsePriority.removed (EligibleSets.family G S k ε) ω).card = S.card :=
  Finset.card_sdiff_add_card_eq_card (removed_subset G S k ε ω)

theorem remaining_bound {C ε : ℝ} (hC : 0 ≤ C) (hprofile : SeparatorProfile.Bound G C)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (k : ℕ) (hk : 0 < k) (hε : 0 < ε)
    (hparam : 4 * (Δ : ℝ) * C / Real.sqrt k ≤ ε)
    (Q : ℕ) (hQ : 0 < Q) (hsize : 2 * (k * 2 ^ ((Δ + 1) ^ k)) ≤ Q) (S : Finset V) :
    4 * Q * (∑ ω : Finset V → Fin Q, (next G S k ε ω).card) ≤
      (4 * Q - 1) * Fintype.card (Finset V → Fin Q) * S.card := by
  have hconf : ∀ U ∈ EligibleSets.family G S k ε,
      2 * (PriorityAcceptance.conflicts (EligibleSets.family G S k ε) U).card ≤ Q :=
    fun U hU => (Nat.mul_le_mul_left 2 (EligibleConflicts.bound G Δ hdeg S U k ε hU)).trans hsize
  have hhalf := EligibleSets.half_covered G hC hprofile Δ hdeg k hk hε hparam S
  have hhalfNat : S.card ≤ 2 * (EligibleSets.covered G S k ε).card := by
    have hh : (S.card : ℝ) ≤ 2 * (EligibleSets.covered G S k ε).card := by linarith
    exact_mod_cast hh
  have hp := PriorityProgress.half_progress (EligibleSets.family G S k ε) Q hQ hconf S hhalfNat
  have hsplit : (∑ ω : Finset V → Fin Q, (next G S k ε ω).card) +
      (∑ ω : Finset V → Fin Q, (SparsePriority.removed (EligibleSets.family G S k ε) ω).card) =
      Fintype.card (Finset V → Fin Q) * S.card := by
    rw [← Finset.sum_add_distrib]
    simp only [card_split, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id]
  have hsub : 4 * Q - 1 + 1 = 4 * Q := by omega
  have hsplit' := congrArg (fun x => 4 * Q * x) hsplit
  have hsub' := congrArg (fun x => x * Fintype.card (Finset V → Fin Q) * S.card) hsub
  nlinarith
end Paper.PriorityStage
