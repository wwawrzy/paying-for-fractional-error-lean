import Paper.Solver.LocalSearch.GeneralCoveringTerminalData

import Paper.Preliminaries.ActiveDemandValues

/-! Full correctness of the actual terminal data protocol: exact execution,
physical soundness, and cost completeness against any bounded competitor. -/
namespace Paper.GeneralCoveringTerminalDataCorrect
open BroadcastModel GeneralCoveringTerminalData
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B q T : ℕ) (l : List V) (cover targets : V → Finset V)
variable (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
variable (hl : ∀ v ∈ K.vertices, (s v).demands = l)
variable (hlist : ∀ r ∈ l, r ∈ K.vertices)
variable (htarget : ∀ v ∈ K.vertices, (s v).targets = targets v)
include ha hc hb hl hlist htarget

theorem run_correct (m : ℕ) (v : V) (hv : v ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = TabularSearch.choose
      (GeneralCoveringTable.table G C K.diameter B T (fun u => maskInput (s u)) v) m
      (DemandValues.values T l multiplicity) := by
  have hvalues := ActiveDemandValues.correct G K C q T l multiplicity
    (fun u => valueInput (s u)) ha hb hl hlist v hv
  rw [run_program]
  dsimp only
  rw [hvalues]
  rfl

include hinc in
theorem complete (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ K.vertices → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ cover r, p u) :
    ∃ w, (program C K.diameter B q T m).run G s v = some w ∧
      TabularSearch.price w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  let row := fun u => GeneralCoveringMask.mask T l (targets u)
  let A := GeneralCoveringTable.table G C K.diameter B T (fun u => maskInput (s u)) v
  have hrows : ∀ i, DemandValues.values T l multiplicity i ≤ IntegralTable.mass row p i := by
    intro i
    cases hi : l[i.val]? with
    | none => simp [DemandValues.values, hi]
    | some r =>
      simp only [DemandValues.values, hi]
      change (multiplicity r).val ≤ IntegralTable.mass
        (fun u => GeneralCoveringMask.mask T l (targets u)) p i
      rw [GeneralCoveringMask.mass cover targets hinc l p i r hi]
      exact hcover r
  have hrep : ∀ u, 0 < p u → ∃ e ∈ A, e.row = row u ∧ e.price ≤ (cost u).val := by
    intro u hu
    have huH : u ∈ K.vertices := by
      by_cases huH : u ∈ K.vertices
      · exact huH
      · have hh := hsupport u huH
        omega
    exact GeneralCoveringTable.representative G K B T l targets cost C
      (fun u => maskInput (s u)) ha hc hl htarget v hv u huH
  obtain ⟨w, hw, hcost⟩ := IntegralTable.choose_complete A row (fun u => (cost u).val) m
    (DemandValues.values T l multiplicity) p hsizep hrows hrep
  exact ⟨w, (run_correct G K B q T l targets cost multiplicity C s
    ha hc hb hl hlist htarget m v hv).trans hw, hcost⟩

include hinc in
theorem sound (hlen : l.length ≤ T) (hz : ∀ r, r ∉ l → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (w : List (TabularSearch.Entry V T)) (hw : (program C K.diameter B q T m).run G s v = some w) :
    (∑ u, TableInterpretation.multiplicity w u) ≤ m ∧
      (∀ u, u ∉ K.vertices → TableInterpretation.multiplicity w u = 0) ∧
      (∀ r, (multiplicity r).val ≤ ∑ u ∈ cover r, TableInterpretation.multiplicity w u) ∧
      IntegralTable.cost (fun u => (cost u).val) (TableInterpretation.multiplicity w) = TabularSearch.price w := by
  rw [run_correct G K B q T l targets cost multiplicity C s ha hc hb hl hlist htarget m v hv] at hw
  obtain ⟨hwlen, hwalphabet, hwrows⟩ := TabularSearch.choose_sound _ m _ hw
  have he (e : TabularSearch.Entry V T) (hem : e ∈ w) :=
    GeneralCoveringTable.wellformed G K B T l targets cost C
      (fun u => maskInput (s u)) ha hc hl htarget v hv e (hwalphabet e hem)
  have hrows : ∀ e ∈ w, e.row = GeneralCoveringMask.mask T l (targets e.id) :=
    fun e hem => (he e hem).2.1
  have hprices : ∀ e ∈ w, e.price = (cost e.id).val := fun e hem => (he e hem).2.2
  refine ⟨?_, ?_, ?_, TableInterpretation.cost_eq _ w hprices⟩
  · rw [TableInterpretation.total_size]
    exact hwlen
  · exact fun u hu => TableInterpretation.support w _ (fun e hem => (he e hem).1) hu
  · apply GeneralCoveringMask.covers cover targets hinc l hlen (DemandValues.values T l multiplicity)
      (fun r => (multiplicity r).val) (TableInterpretation.multiplicity w) hz
    · intro i r hi
      simp [DemandValues.values, hi]
    · intro i
      rw [TableInterpretation.mass_eq _ w hrows i]
      exact hwrows i

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ K.vertices)
    (hw : w ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = (program C K.diameter B q T m).run G s w := by
  have ht : GeneralCoveringTable.table G C K.diameter B T (fun u => maskInput (s u)) v =
      GeneralCoveringTable.table G C K.diameter B T (fun u => maskInput (s u)) w :=
    (GeneralCoveringTable.alphabet_correct G K C B T l targets cost
      (fun u => maskInput (s u)) ha hc hl htarget v hv).trans
      (GeneralCoveringTable.alphabet_correct G K C B T l targets cost
        (fun u => maskInput (s u)) ha hc hl htarget w hw).symm
  rw [run_correct G K B q T l targets cost multiplicity C s ha hc hb hl hlist htarget m v hv,
    run_correct G K B q T l targets cost multiplicity C s ha hc hb hl hlist htarget m w hw, ht]
end Paper.GeneralCoveringTerminalDataCorrect
