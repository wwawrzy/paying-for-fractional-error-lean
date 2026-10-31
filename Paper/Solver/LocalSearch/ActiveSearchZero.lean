import Paper.Solver.LocalSearch.SearchZero
import Paper.Solver.LocalSearch.ActiveSearchCount

/-! Physical soundness/completeness of actual zero-budget branch on general tasks. -/
namespace Paper.ActiveSearchZero
open BroadcastModel SearchZero
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B q : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hb : ∀ v, (s v).value = multiplicity v)
include ha hb

theorem result_iff (v : V) (hv : v ∈ K.vertices) (w : SolutionWord.Word V B)
    (hw : (SearchCount.zero C K.diameter B q).run G s v = some w) :
    w = [] ∧ (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card = 0 := by
  rw [ActiveSearchCount.zero_correct G K B q multiplicity C s ha hb v hv] at hw
  split_ifs at hw with he
  · exact ⟨(Option.some.inj hw).symm, he⟩

theorem sound (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0)
    (v : V) (hv : v ∈ K.vertices) (w : SolutionWord.Word V B)
    (hw : (SearchCount.zero C K.diameter B q).run G s v = some w) :
    w.length ≤ 0 ∧ (∀ t ∈ w, SolutionWord.id t ∈ K.vertices) ∧
      SolutionWord.Consistent cost w ∧
      ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, SolutionWord.copies w u := by
  obtain ⟨rfl, hcard⟩ := result_iff G K B q multiplicity C s ha hb v hv w hw
  have hzero := all_zero (K.vertices) multiplicity hz hcard
  refine ⟨by simp, by simp, by simp [SolutionWord.Consistent], ?_⟩
  intro r
  rw [hzero r]
  exact Nat.zero_le _

theorem complete (v : V) (hv : v ∈ K.vertices)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (SearchCount.zero C K.diameter B q).run G s v = some w ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  have hp0 : ∀ u, p u = 0 := by
    intro u
    have hh : p u ≤ ∑ r, p r :=
      Finset.single_le_sum (fun r _ => Nat.zero_le (p r)) (Finset.mem_univ u)
    omega
  have hb0 : ∀ r, (multiplicity r).val = 0 := by
    intro r
    have hh := hcover r
    simpa only [hp0, Finset.sum_const_zero, Nat.le_zero_eq] using hh
  have hcard : (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card = 0 := by
    simp [TerminalProtocolCorrect.demands, hb0]
  refine ⟨[], ?_, Nat.zero_le _⟩
  rw [ActiveSearchCount.zero_correct G K B q multiplicity C s ha hb v hv, if_pos hcard]

theorem uniform (v w : V) (hv : v ∈ K.vertices)
    (hw : w ∈ K.vertices) :
    (SearchCount.zero C K.diameter B q).run G s v = (SearchCount.zero C K.diameter B q).run G s w := by
  rw [ActiveSearchCount.zero_correct G K B q multiplicity C s ha hb v hv,
    ActiveSearchCount.zero_correct G K B q multiplicity C s ha hb w hw]

end Paper.ActiveSearchZero
