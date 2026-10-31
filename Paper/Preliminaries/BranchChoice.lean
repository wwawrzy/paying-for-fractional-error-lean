import Paper.Preliminaries.BranchChild

/-! Inductive semantic bridge for real child calls. The only hypothesis
about the child is its lower-budget correctness, later discharged by Nat
induction for RecursiveSearch.program itself. -/
namespace Paper.BranchChoice
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {B q m : ℕ} (H : Finset V) (c : V → Fin (B + 1))
variable (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
variable (ih : ∀ (b : V → Fin (q + 1)) (s : V → TerminalProtocol.Input V B q),
  (∀ r, (s r).active = decide (r ∈ H)) → (∀ r, (s r).cost = c r) →
  (∀ r, (s r).value = b r) → (∀ r, r ∉ H → (b r).val = 0) →
    SearchSpec.Spec G P H c b m s)
variable (s : V → BranchLoop.State V B q) (b : V → Fin (q + 1))
variable (ha : ∀ r, (s r).input.active = decide (r ∈ H))
variable (hc : ∀ r, (s r).input.cost = c r) (hb : ∀ r, (s r).input.value = b r)
variable (hz : ∀ r, r ∉ H → (b r).val = 0)
variable (hi : ∀ v w, v ∈ H → w ∈ H → (s v).info = (s w).info)
include ih ha hc hb hz hi

theorem child_spec (j : ℕ) (v : V) (hv : v ∈ H) (t : CostTag.Tag V B)
    (ht : (s v).info.candidates[j]? = some t) :
    SearchSpec.Spec G P H c (SearchResidual.values G (SolutionWord.id t) b) m
      (BranchLoop.childState G j s) := by
  apply ih (SearchResidual.values G (SolutionWord.id t) b) (BranchLoop.childState G j s)
  · intro r
    exact (BranchChild.metadata G j s r).1.trans (ha r)
  · intro r
    exact (BranchChild.metadata G j s r).2.trans (hc r)
  · exact BranchChild.values_some G H j s b hb hz hi v hv t ht
  · exact SearchResidual.zero_outside G (SolutionWord.id t) b H hz

theorem sound
    (hs : ∀ v ∈ H, ∀ t ∈ (s v).info.candidates, SolutionWord.id t ∈ H)
    (htc : ∀ v ∈ H, SolutionWord.Consistent c (s v).info.candidates)
    (j : ℕ) (v : V) (hv : v ∈ H) (w : SolutionWord.Word V B)
    (hw : BranchLoop.choice G P j s v = some w) : SearchSpec.Valid G H c b (m + 1) w := by
  cases ht : (s v).info.candidates[j]? with
  | none => rw [BranchChild.choice_none G P j s v ht] at hw; contradiction
  | some t =>
    have hchild := child_spec G H c P ih s b ha hc hb hz hi j v hv t ht
    rw [BranchChild.choice_some G P j s v t ht] at hw
    cases hr : P.run G (BranchLoop.childState G j s) v with
    | none => simp [hr] at hw
    | some x =>
      simp only [hr, Option.map_some, Option.some.injEq] at hw
      subst w
      have hmem : t ∈ (s v).info.candidates := List.mem_of_getElem? ht
      exact SearchSpec.valid_cons G H c b m t x (hs v hv t hmem) (htc v hv t hmem)
        (hchild.sound v hv x hr)

theorem uniform (j : ℕ) (v w : V) (hv : v ∈ H) (hw : w ∈ H) :
    BranchLoop.choice G P j s v = BranchLoop.choice G P j s w := by
  have he : (s w).info = (s v).info := hi w v hw hv
  cases ht : (s v).info.candidates[j]? with
  | none =>
    rw [BranchChild.choice_none G P j s v ht,
      BranchChild.choice_none G P j s w (by rw [he, ht])]
  | some t =>
    have hchild := child_spec G H c P ih s b ha hc hb hz hi j v hv t ht
    rw [BranchChild.choice_some G P j s v t ht,
      BranchChild.choice_some G P j s w t (by rw [he, ht]), hchild.uniform v w hv hw]

theorem complete_tag (K : ℕ) (v : V) (hv : v ∈ H) (t : CostTag.Tag V B)
    (ht : t ∈ (s v).info.candidates) (hlen : (s v).info.candidates.length ≤ K)
    (htc : (ofLex t).1 = c (SolutionWord.id t))
    (p : V → ℕ) (hsize : ∑ u, p u ≤ m + 1)
    (hp : ∀ u, u ∉ H → p u = 0)
    (hcover : ∀ r, (b r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u)
    (hpos : 0 < p (SolutionWord.id t)) :
    ∃ w, some w ∈ (List.range K).map (fun j => BranchLoop.choice G P j s v) ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (c u).val) p := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp ht
  have hget' : (s v).info.candidates[j]? = some t := by
    rw [List.getElem?_eq_getElem hj, hget]
  have hchild := child_spec G H c P ih s b ha hc hb hz hi j v hv t hget'
  obtain ⟨herase, hred⟩ := SearchResidual.erase_feasible G (SolutionWord.id t) b m p hsize hcover hpos
  obtain ⟨x, hx, hcost⟩ := hchild.complete (IntegralTable.erase p (SolutionWord.id t)) herase
    (SearchSpec.erase_support H p (SolutionWord.id t) hp) hred v hv
  refine ⟨t :: x, ?_, SearchResidual.cons_cost_bound c t x htc p hpos hcost⟩
  apply List.mem_map.mpr
  refine ⟨j, List.mem_range.mpr (lt_of_lt_of_le hj hlen), ?_⟩
  rw [BranchChild.choice_some G P j s v t hget', hx]
  rfl
end Paper.BranchChoice
