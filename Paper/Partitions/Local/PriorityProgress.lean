import Paper.Partitions.Local.PriorityAcceptance
import Paper.Averaging.Tasks.FiniteIncidenceAverage

/-! Exact finite expected progress of the local disjoint-set selection.
Every vertex covered by an eligible set inherits its acceptance frequency. -/
namespace Paper.PriorityProgress
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem vertex_frequency (F : Finset (Finset V)) (Q : ℕ) (hQ : 0 < Q)
    (hconf : ∀ U ∈ F, 2 * (PriorityAcceptance.conflicts F U).card ≤ Q)
    (v : V) (hv : v ∈ F.biUnion id) :
    Fintype.card (Finset V → Fin Q) ≤ 2 * Q *
      (Finset.univ.filter (fun ω : Finset V → Fin Q => v ∈ SparsePriority.removed F ω)).card := by
  obtain ⟨U, hU, hvU⟩ := Finset.mem_biUnion.mp hv
  have hf := PriorityAcceptance.frequency F U hU Q hQ (hconf U hU)
  apply hf.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro ω hω
  have hacc := (Finset.mem_filter.mp hω).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨U, Finset.mem_filter.mpr ⟨hU, hacc⟩, hvU⟩⟩

theorem covered_progress (F : Finset (Finset V)) (Q : ℕ) (hQ : 0 < Q)
    (hconf : ∀ U ∈ F, 2 * (PriorityAcceptance.conflicts F U).card ≤ Q) :
    Fintype.card (Finset V → Fin Q) * (F.biUnion id).card ≤
      2 * Q * (∑ ω : Finset V → Fin Q, (SparsePriority.removed F ω).card) := by
  let E := F.biUnion id
  let W : Finset (Finset V → Fin Q) := Finset.univ
  have hsum : E.card * W.card ≤ 2 * Q *
      (∑ v ∈ E, (W.filter (fun ω => v ∈ SparsePriority.removed F ω)).card) := by
    calc
      _ = ∑ _v ∈ E, W.card := by simp
      _ ≤ ∑ v ∈ E, 2 * Q * (W.filter (fun ω => v ∈ SparsePriority.removed F ω)).card :=
        Finset.sum_le_sum (fun v hv => by simpa only [W, Finset.card_univ] using vertex_frequency F Q hQ hconf v hv)
      _ = _ := by rw [Finset.mul_sum]
  have he : (∑ v ∈ E, (W.filter (fun ω => v ∈ SparsePriority.removed F ω)).card) =
      ∑ ω ∈ W, (E.filter (fun v => v ∈ SparsePriority.removed F ω)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [he] at hsum
  have hupper : (∑ ω ∈ W, (E.filter (fun v => v ∈ SparsePriority.removed F ω)).card) ≤
      ∑ ω : Finset V → Fin Q, (SparsePriority.removed F ω).card := by
    apply Finset.sum_le_sum
    intro ω _
    exact Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
  have h := hsum.trans (Nat.mul_le_mul_left _ hupper)
  simpa only [E, W, Finset.card_univ, Nat.mul_comm] using h

theorem half_progress (F : Finset (Finset V)) (Q : ℕ) (hQ : 0 < Q)
    (hconf : ∀ U ∈ F, 2 * (PriorityAcceptance.conflicts F U).card ≤ Q)
    (S : Finset V) (hhalf : S.card ≤ 2 * (F.biUnion id).card) :
    Fintype.card (Finset V → Fin Q) * S.card ≤
      4 * Q * (∑ ω : Finset V → Fin Q, (SparsePriority.removed F ω).card) := by
  have h := covered_progress F Q hQ hconf
  have hs := Nat.mul_le_mul_left (Fintype.card (Finset V → Fin Q)) hhalf
  nlinarith
end Paper.PriorityProgress
