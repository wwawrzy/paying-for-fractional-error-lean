import Paper.Solver.LocalSearch.GeneralCoveringSpec

/-! Pure decision consequences of the bounded-search specification.
The actual optional word is retained. Positive costs turn a cost budget into
a copy budget and make any returned word of cost at most m globally optimal
among supported feasible competitors. No runtime constructor is asserted. -/

namespace Paper.SmallComponentSearchDecision

open BroadcastModel
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem copies_le_cost {B : ℕ} (c : V → Fin (B + 1))
    (hc : ∀ u, 1 ≤ (c u).val) (p : V → ℕ) :
    (∑ u, p u) ≤ IntegralTable.cost (fun u => (c u).val) p := by
  unfold IntegralTable.cost
  apply Finset.sum_le_sum
  intro u _
  simpa only [one_mul] using Nat.mul_le_mul_right (p u) (hc u)

/-- Solved means that the raw optional output contains a word within budget. -/
def Solved {B : ℕ} (result : Option (SolutionWord.Word V B)) (m : ℕ) : Prop :=
  ∃ w, result = some w ∧ SolutionWord.cost w ≤ m

variable (cover : V → Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
  {B q : ℕ}
  (P : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
  (H : Finset V) (c : V → Fin (B + 1)) (b : V → Fin (q + 1)) (m : ℕ)
  (s : V → GeneralCoveringResidual.Input V B q)
  (h : GeneralCoveringSpec.Spec cover G P H c b m s)

include h

/-- A returned word within the cost budget is no more expensive than any
supported feasible multicover, even one with no supplied copy budget. -/
theorem returned_optimal (hc : ∀ u, 1 ≤ (c u).val)
    (v : V) (hv : v ∈ H) (w : SolutionWord.Word V B)
    (hw : P.run G s v = some w) (hcost : SolutionWord.cost w ≤ m)
    (p : V → ℕ) (hsupport : ∀ u, u ∉ H → p u = 0)
    (hcover : ∀ r, (b r).val ≤ ∑ u ∈ cover r, p u) :
    SolutionWord.cost w ≤ IntegralTable.cost (fun u => (c u).val) p := by
  by_cases hp : IntegralTable.cost (fun u => (c u).val) p ≤ m
  · have hsize := (copies_le_cost c hc p).trans hp
    obtain ⟨w', hw', hle⟩ := h.complete p hsize hsupport hcover v hv
    have heq : w' = w := Option.some.inj (hw'.symm.trans hw)
    simpa only [heq] using hle
  · omega

/-- Successful affordable output is equivalent to an actual affordable
supported feasible multicover; no optimum or budget witness is assumed. -/
theorem solved_iff (hc : ∀ u, 1 ≤ (c u).val) (v : V) (hv : v ∈ H) :
    Solved (P.run G s v) m ↔
      ∃ p : V → ℕ, (∀ u, u ∉ H → p u = 0) ∧
        (∀ r, (b r).val ≤ ∑ u ∈ cover r, p u) ∧
        IntegralTable.cost (fun u => (c u).val) p ≤ m := by
  constructor
  · rintro ⟨w, hw, hcost⟩
    have hvalid := h.sound v hv w hw
    refine ⟨SolutionWord.copies w,
      GeneralCoveringSpec.copies_support cover H c b m w hvalid, hvalid.2.2.2, ?_⟩
    rw [GeneralCoveringSpec.exact_cost cover H c b m w hvalid]
    exact hcost
  · rintro ⟨p, hsupport, hcover, hcost⟩
    have hsize := (copies_le_cost c hc p).trans hcost
    obtain ⟨w, hw, hle⟩ := h.complete p hsize hsupport hcover v hv
    exact ⟨w, hw, hle.trans hcost⟩

/-- Uniformity of the actual optional outputs implies uniform solved decisions. -/
theorem solved_uniform (v u : V) (hv : v ∈ H) (hu : u ∈ H) :
    Solved (P.run G s v) m ↔ Solved (P.run G s u) m := by
  rw [h.uniform v u hv hu]

end Paper.SmallComponentSearchDecision

#print axioms Paper.SmallComponentSearchDecision.copies_le_cost
#print axioms Paper.SmallComponentSearchDecision.returned_optimal
#print axioms Paper.SmallComponentSearchDecision.solved_iff
#print axioms Paper.SmallComponentSearchDecision.solved_uniform
