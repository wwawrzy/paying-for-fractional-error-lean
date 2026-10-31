import Paper.Preliminaries.TerminalData
import Paper.Preliminaries.ActiveActualTable
import Paper.Preliminaries.ActiveDemandValues

/-! Full correctness of the actual terminal data protocol: exact execution,
physical soundness, and cost completeness against any bounded competitor. -/
namespace Paper.ActiveTerminalData
open BroadcastModel TerminalData
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B q T : ℕ) (l : List V)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
variable (hl : ∀ v ∈ K.vertices, (s v).demands = l)
variable (hlist : ∀ r ∈ l, r ∈ K.vertices)
include ha hc hb hl hlist

theorem run_correct (m : ℕ) (v : V) (hv : v ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = TabularSearch.choose
      (ActiveActualTable.table G C K.diameter B T (fun u => maskInput (s u)) v) m
      (DemandValues.values T l multiplicity) := by
  have hvalues := ActiveDemandValues.correct G K C q T l multiplicity
    (fun u => valueInput (s u)) ha hb hl hlist v hv
  rw [run_program]
  dsimp only
  rw [hvalues]
  rfl

theorem complete (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ K.vertices → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (program C K.diameter B q T m).run G s v = some w ∧
      TabularSearch.price w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  let row := fun u => LocalDemandMask.mask T l u (G.neighborFinset u)
  let A := ActiveActualTable.table G C K.diameter B T (fun u => maskInput (s u)) v
  have hrows : ∀ i, DemandValues.values T l multiplicity i ≤ IntegralTable.mass row p i := by
    intro i
    cases hi : l[i.val]? with
    | none => simp [DemandValues.values, hi]
    | some r =>
      simp only [DemandValues.values, hi]
      change (multiplicity r).val ≤ IntegralTable.mass
        (fun u => LocalDemandMask.mask T l u (G.neighborFinset u)) p i
      rw [TableInterpretation.graph_mass G l p i r hi]
      exact hcover r
  have hrep : ∀ u, 0 < p u → ∃ e ∈ A, e.row = row u ∧ e.price ≤ (cost u).val := by
    intro u hu
    have huH : u ∈ K.vertices := by
      by_cases huH : u ∈ K.vertices
      · exact huH
      · have hh := hsupport u huH
        omega
    exact ActiveActualTable.representative G K B T l cost C
      (fun u => maskInput (s u)) ha hc hl v hv u huH
  obtain ⟨w, hw, hcost⟩ := IntegralTable.choose_complete A row (fun u => (cost u).val) m
    (DemandValues.values T l multiplicity) p hsizep hrows hrep
  exact ⟨w, (run_correct G K B q T l cost multiplicity C s
    ha hc hb hl hlist m v hv).trans hw, hcost⟩

theorem sound (hlen : l.length ≤ T) (hz : ∀ r, r ∉ l → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (w : List (TabularSearch.Entry V T)) (hw : (program C K.diameter B q T m).run G s v = some w) :
    (∑ u, TableInterpretation.multiplicity w u) ≤ m ∧
      (∀ u, u ∉ K.vertices → TableInterpretation.multiplicity w u = 0) ∧
      (∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, TableInterpretation.multiplicity w u) ∧
      IntegralTable.cost (fun u => (cost u).val) (TableInterpretation.multiplicity w) = TabularSearch.price w := by
  rw [run_correct G K B q T l cost multiplicity C s ha hc hb hl hlist m v hv] at hw
  obtain ⟨hwlen, hwalphabet, hwrows⟩ := TabularSearch.choose_sound _ m _ hw
  have he (e : TabularSearch.Entry V T) (hem : e ∈ w) :=
    ActiveActualTable.wellformed G K B T l cost C
      (fun u => maskInput (s u)) ha hc hl v hv e (hwalphabet e hem)
  have hrows : ∀ e ∈ w, e.row = LocalDemandMask.mask T l e.id (G.neighborFinset e.id) :=
    fun e hem => (he e hem).2.1
  have hprices : ∀ e ∈ w, e.price = (cost e.id).val := fun e hem => (he e hem).2.2
  refine ⟨?_, ?_, ?_, TableInterpretation.cost_eq _ w hprices⟩
  · rw [TableInterpretation.total_size]
    exact hwlen
  · exact fun u hu => TableInterpretation.support w _ (fun e hem => (he e hem).1) hu
  · apply TableInterpretation.graph_covers G l hlen (DemandValues.values T l multiplicity)
      (fun r => (multiplicity r).val) (TableInterpretation.multiplicity w) hz
    · intro i r hi
      simp [DemandValues.values, hi]
    · intro i
      rw [TableInterpretation.mass_eq _ w hrows i]
      exact hwrows i

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ K.vertices)
    (hw : w ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = (program C K.diameter B q T m).run G s w := by
  have ht : ActiveActualTable.table G C K.diameter B T (fun u => maskInput (s u)) v =
      ActiveActualTable.table G C K.diameter B T (fun u => maskInput (s u)) w :=
    (ActiveActualTable.alphabet_correct G K C B T l cost
      (fun u => maskInput (s u)) ha hc hl v hv).trans
      (ActiveActualTable.alphabet_correct G K C B T l cost
        (fun u => maskInput (s u)) ha hc hl w hw).symm
  rw [run_correct G K B q T l cost multiplicity C s ha hc hb hl hlist m v hv,
    run_correct G K B q T l cost multiplicity C s ha hc hb hl hlist m w hw, ht]
end Paper.ActiveTerminalData
