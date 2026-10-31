import Paper.Endpoints.Components.SmallComponentSearchDecision
import Paper.Solver.LocalSearch.GeneralCoveringIntegral

/-! Semantic conversion of a returned search word into a feasible set.
Positive copies determine the support, while the raw optional word remains
the solved witness. No component algorithm or runtime graph is constructed. -/

namespace Paper.SmallComponentSetDecision

open BroadcastModel GeneralCoveringIntegral
open scoped BigOperators

variable {V : Type} [Fintype V] [LinearOrder V]

def support {B : ℕ} (w : SolutionWord.Word V B) : Finset V :=
  Finset.univ.filter (fun u => 0 < SolutionWord.copies w u)

theorem mem_support {B : ℕ} (w : SolutionWord.Word V B) (u : V) :
    u ∈ support w ↔ 0 < SolutionWord.copies w u := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]

def indicator (O : Finset V) (u : V) : ℕ := if u ∈ O then 1 else 0

theorem indicator_cost {B : ℕ} (c : V → Fin (B + 1)) (O : Finset V) :
    IntegralTable.cost (fun u => (c u).val) (indicator O) = ∑ u ∈ O, (c u).val := by
  simp [IntegralTable.cost, indicator, Finset.sum_filter]

theorem indicator_covers (cover : V → Finset V) (R O : Finset V)
    (hO : Covers cover R O) :
    ∀ r, (TaskBenchmark.demand (q := 1) R r).val ≤ ∑ u ∈ cover r, indicator O u := by
  intro r
  change (if r ∈ R then 1 else 0) ≤ ∑ u ∈ cover r, indicator O u
  by_cases hr : r ∈ R
  · obtain ⟨u, huO, hur⟩ := hO r hr
    have hh := Finset.single_le_sum (fun z _ => Nat.zero_le (indicator O z)) hur
    simpa only [if_pos hr, indicator, if_pos huO] using hh
  · simp only [if_neg hr, Nat.zero_le]

variable (cover : V → Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] {B : ℕ}
  (P : Program V (GeneralCoveringResidual.Input V B 1) (Option (SolutionWord.Word V B)))
  (H R : Finset V) (c : V → Fin (B + 1)) (m : ℕ)
  (s : V → GeneralCoveringResidual.Input V B 1)
  (h : GeneralCoveringSpec.Spec cover G P H c (TaskBenchmark.demand (q := 1) R) m s)

include h

/-- Every returned word yields supported, admissible coverage. Its set cost
can only decrease when repeated copies are replaced by one chosen vertex. -/
theorem support_properties (hc : ∀ u, 1 ≤ (c u).val) (v : V) (hv : v ∈ H)
    (w : SolutionWord.Word V B) (hw : P.run G s v = some w) :
    support w ⊆ H ∧ support w ⊆ CoveringSupport.admissible cover R ∧
      Covers cover R (support w) ∧ (∑ u ∈ support w, (c u).val) ≤ SolutionWord.cost w := by
  have hvalid := h.sound v hv w hw
  have hs : support w ⊆ H := by
    intro u hu
    by_contra hn
    have hz := GeneralCoveringSpec.copies_support cover H c _ m w hvalid u hn
    have hp := (mem_support w u).mp hu
    omega
  have ha : support w ⊆ CoveringSupport.admissible cover R := by
    intro u hu
    obtain ⟨r, hr, hur⟩ := GeneralCoveringSpec.used_is_admissible cover G P H c _ m s h
      (fun z => lt_of_lt_of_le Nat.zero_lt_one (hc z)) v hv w hw u ((mem_support w u).mp hu)
    have hrR : r ∈ R := by
      by_contra hn
      change 0 < (if r ∈ R then 1 else 0) at hr
      rw [if_neg hn] at hr
      omega
    exact Finset.mem_biUnion.mpr ⟨r, hrR, hur⟩
  refine ⟨hs, ha, ?_, ?_⟩
  · intro r hr
    have hh := hvalid.2.2.2 r
    change (if r ∈ R then 1 else 0) ≤ ∑ u ∈ cover r, SolutionWord.copies w u at hh
    rw [if_pos hr] at hh
    obtain ⟨u, hur, hp⟩ := Finset.sum_pos_iff.mp
      (show 0 < ∑ u ∈ cover r, SolutionWord.copies w u by omega)
    exact ⟨u, (mem_support w u).mpr hp, hur⟩
  · calc
      _ ≤ ∑ u ∈ support w, (c u).val * SolutionWord.copies w u := by
        apply Finset.sum_le_sum
        intro u hu
        exact Nat.le_mul_of_pos_right _ ((mem_support w u).mp hu)
      _ ≤ ∑ u, (c u).val * SolutionWord.copies w u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
      _ = SolutionWord.cost w := GeneralCoveringSpec.exact_cost cover H c _ m w hvalid

/-- An arbitrary feasible set supported in H supplies an indicator competitor;
there is no cost or cardinality restriction on that competitor. -/
theorem word_optimal_supported (hc : ∀ u, 1 ≤ (c u).val) (v : V) (hv : v ∈ H)
    (w : SolutionWord.Word V B) (hw : P.run G s v = some w)
    (hcost : SolutionWord.cost w ≤ m) (O : Finset V) (hOH : O ⊆ H)
    (hO : Covers cover R O) : SolutionWord.cost w ≤ ∑ u ∈ O, (c u).val := by
  have hsupport : ∀ u, u ∉ H → indicator O u = 0 := by
    intro u hu
    exact if_neg (fun ho => hu (hOH ho))
  have hle := SmallComponentSearchDecision.returned_optimal cover G P H c
    (TaskBenchmark.demand (q := 1) R) m s h hc v hv w hw hcost
    (indicator O) hsupport (indicator_covers cover R O hO)
  simpa only [indicator_cost] using hle

/-- The set decision is equivalent to a supported admissible feasible set. -/
theorem solved_iff_supported_set (hc : ∀ u, 1 ≤ (c u).val) (v : V) (hv : v ∈ H) :
    SmallComponentSearchDecision.Solved (P.run G s v) m ↔
      ∃ O : Finset V, O ⊆ H ∧ O ⊆ CoveringSupport.admissible cover R ∧
        Covers cover R O ∧ (∑ u ∈ O, (c u).val) ≤ m := by
  constructor
  · rintro ⟨w, hw, hcost⟩
    obtain ⟨hs, ha, hcover, hle⟩ := support_properties cover G P H R c m s h hc v hv w hw
    exact ⟨support w, hs, ha, hcover, hle.trans hcost⟩
  · rintro ⟨O, hOH, _, hO, hcost⟩
    apply (SmallComponentSearchDecision.solved_iff cover G P H c
      (TaskBenchmark.demand (q := 1) R) m s h hc v hv).mpr
    refine ⟨indicator O, ?_, indicator_covers cover R O hO, ?_⟩
    · intro u hu
      exact if_neg (fun ho => hu (hOH ho))
    · simpa only [indicator_cost] using hcost

/-- Incidence containment makes every admissible competitor supported in H.
Both the word and its support compare with every such feasible set. -/
theorem optimal_against_set (hc : ∀ u, 1 ≤ (c u).val)
    (htask : ∀ r ∈ R, cover r ⊆ H) (v : V) (hv : v ∈ H)
    (w : SolutionWord.Word V B) (hw : P.run G s v = some w)
    (hcost : SolutionWord.cost w ≤ m) (O : Finset V)
    (hOadm : O ⊆ CoveringSupport.admissible cover R) (hO : Covers cover R O) :
    SolutionWord.cost w ≤ ∑ u ∈ O, (c u).val ∧
      (∑ u ∈ support w, (c u).val) ≤ ∑ u ∈ O, (c u).val := by
  have hOH := hOadm.trans (GeneralCoveringIntegral.admissible_subset cover R H htask)
  have hword := word_optimal_supported cover G P H R c m s h hc v hv w hw hcost O hOH hO
  have hs := support_properties cover G P H R c m s h hc v hv w hw
  exact ⟨hword, hs.2.2.2.trans hword⟩

/-- Under incidence containment, the raw solved predicate decides existence
of an affordable admissible feasible set, without a copy budget premise. -/
theorem solved_iff_set (hc : ∀ u, 1 ≤ (c u).val)
    (htask : ∀ r ∈ R, cover r ⊆ H) (v : V) (hv : v ∈ H) :
    SmallComponentSearchDecision.Solved (P.run G s v) m ↔
      ∃ O : Finset V, O ⊆ CoveringSupport.admissible cover R ∧
        Covers cover R O ∧ (∑ u ∈ O, (c u).val) ≤ m := by
  rw [solved_iff_supported_set cover G P H R c m s h hc v hv]
  constructor
  · rintro ⟨O, _, ha, hO, hcost⟩
    exact ⟨O, ha, hO, hcost⟩
  · rintro ⟨O, ha, hO, hcost⟩
    exact ⟨O, ha.trans (GeneralCoveringIntegral.admissible_subset cover R H htask), ha, hO, hcost⟩

end Paper.SmallComponentSetDecision

#print axioms Paper.SmallComponentSetDecision.support_properties
#print axioms Paper.SmallComponentSetDecision.word_optimal_supported
#print axioms Paper.SmallComponentSetDecision.solved_iff_supported_set
#print axioms Paper.SmallComponentSetDecision.optimal_against_set
#print axioms Paper.SmallComponentSetDecision.solved_iff_set
