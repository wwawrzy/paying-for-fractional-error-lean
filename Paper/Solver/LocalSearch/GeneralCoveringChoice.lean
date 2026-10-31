import Paper.Solver.LocalSearch.GeneralCoveringChild

/-! Inductive semantic bridge for real child calls. The only hypothesis
about the child is its lower-budget correctness, later discharged by Nat
induction for RecursiveSearch.program itself. -/
namespace Paper.GeneralCoveringChoice
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (cover targets : V → Finset V)
variable {B q m : ℕ} (H : Finset V) (c : V → Fin (B + 1))
variable (P : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
variable (ih : ∀ (b : V → Fin (q + 1)) (s : V → GeneralCoveringResidual.Input V B q),
  (∀ r, (s r).base.active = decide (r ∈ H)) → (∀ r, (s r).base.cost = c r) →
  (∀ r, (s r).base.value = b r) → (∀ r, r ∉ H → (b r).val = 0) →
  (∀ r, (s r).candidates = cover r) → (∀ r, (s r).targets = targets r) →
    GeneralCoveringSpec.Spec cover G P H c b m s)
variable (s : V → GeneralCoveringLoop.State V B q) (b : V → Fin (q + 1))
variable (ha : ∀ r, (s r).input.base.active = decide (r ∈ H))
variable (hc : ∀ r, (s r).input.base.cost = c r) (hb : ∀ r, (s r).input.base.value = b r)
variable (hz : ∀ r, r ∉ H → (b r).val = 0)
variable (hC : ∀ r, (s r).input.candidates = cover r)
variable (htarget : ∀ r, (s r).input.targets = targets r)
variable (hi : ∀ v w, v ∈ H → w ∈ H → (s v).info = (s w).info)
include ih ha hc hb hz hi hC htarget

theorem child_spec (j : ℕ) (v : V) (hv : v ∈ H) (t : CostTag.Tag V B)
    (ht : (s v).info.candidates[j]? = some t) :
    GeneralCoveringSpec.Spec cover G P H c (GeneralCoveringResidual.values cover (SolutionWord.id t) b) m
      (GeneralCoveringLoop.childState G j s) := by
  apply ih (GeneralCoveringResidual.values cover (SolutionWord.id t) b) (GeneralCoveringLoop.childState G j s)
  · intro r
    exact (GeneralCoveringChild.metadata G j s r).1.trans (ha r)
  · intro r
    exact (GeneralCoveringChild.metadata G j s r).2.1.trans (hc r)
  · exact GeneralCoveringChild.values_some G cover H j s b hb hC hz hi v hv t ht
  · exact GeneralCoveringResidual.zero_outside cover (SolutionWord.id t) b H hz
  · intro r
    exact (GeneralCoveringChild.metadata G j s r).2.2.1.trans (hC r)
  · intro r
    exact (GeneralCoveringChild.metadata G j s r).2.2.2.trans (htarget r)

theorem sound
    (hs : ∀ v ∈ H, ∀ t ∈ (s v).info.candidates, SolutionWord.id t ∈ H)
    (htc : ∀ v ∈ H, SolutionWord.Consistent c (s v).info.candidates)
    (j : ℕ) (v : V) (hv : v ∈ H) (w : SolutionWord.Word V B)
    (hw : GeneralCoveringLoop.choice G P j s v = some w) : GeneralCoveringSpec.Valid cover H c b (m + 1) w := by
  cases ht : (s v).info.candidates[j]? with
  | none => rw [GeneralCoveringChild.choice_none G P j s v ht] at hw; contradiction
  | some t =>
    have hchild := child_spec G cover targets H c P ih s b ha hc hb hz hC htarget hi j v hv t ht
    rw [GeneralCoveringChild.choice_some G P j s v t ht] at hw
    cases hr : P.run G (GeneralCoveringLoop.childState G j s) v with
    | none => simp [hr] at hw
    | some x =>
      simp only [hr, Option.map_some, Option.some.injEq] at hw
      subst w
      have hmem : t ∈ (s v).info.candidates := List.mem_of_getElem? ht
      exact GeneralCoveringSpec.valid_cons cover H c b m t x (hs v hv t hmem) (htc v hv t hmem)
        (hchild.sound v hv x hr)

theorem uniform (j : ℕ) (v w : V) (hv : v ∈ H) (hw : w ∈ H) :
    GeneralCoveringLoop.choice G P j s v = GeneralCoveringLoop.choice G P j s w := by
  have he : (s w).info = (s v).info := hi w v hw hv
  cases ht : (s v).info.candidates[j]? with
  | none =>
    rw [GeneralCoveringChild.choice_none G P j s v ht,
      GeneralCoveringChild.choice_none G P j s w (by rw [he, ht])]
  | some t =>
    have hchild := child_spec G cover targets H c P ih s b ha hc hb hz hC htarget hi j v hv t ht
    rw [GeneralCoveringChild.choice_some G P j s v t ht,
      GeneralCoveringChild.choice_some G P j s w t (by rw [he, ht]), hchild.uniform v w hv hw]

theorem complete_tag (K : ℕ) (v : V) (hv : v ∈ H) (t : CostTag.Tag V B)
    (ht : t ∈ (s v).info.candidates) (hlen : (s v).info.candidates.length ≤ K)
    (htc : (ofLex t).1 = c (SolutionWord.id t))
    (p : V → ℕ) (hsize : ∑ u, p u ≤ m + 1)
    (hp : ∀ u, u ∉ H → p u = 0)
    (hcover : ∀ r, (b r).val ≤ ∑ u ∈ cover r, p u)
    (hpos : 0 < p (SolutionWord.id t)) :
    ∃ w, some w ∈ (List.range K).map (fun j => GeneralCoveringLoop.choice G P j s v) ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (c u).val) p := by
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp ht
  have hget' : (s v).info.candidates[j]? = some t := by
    rw [List.getElem?_eq_getElem hj, hget]
  have hchild := child_spec G cover targets H c P ih s b ha hc hb hz hC htarget hi j v hv t hget'
  obtain ⟨herase, hred⟩ := GeneralCoveringResidual.erase_feasible cover (SolutionWord.id t) b m p hsize hcover hpos
  obtain ⟨x, hx, hcost⟩ := hchild.complete (IntegralTable.erase p (SolutionWord.id t)) herase
    (GeneralCoveringSpec.erase_support H p (SolutionWord.id t) hp) hred v hv
  refine ⟨t :: x, ?_, SearchResidual.cons_cost_bound c t x htc p hpos hcost⟩
  apply List.mem_map.mpr
  refine ⟨j, List.mem_range.mpr (lt_of_lt_of_le hj hlen), ?_⟩
  rw [GeneralCoveringChild.choice_some G P j s v t hget', hx]
  rfl
end Paper.GeneralCoveringChoice
