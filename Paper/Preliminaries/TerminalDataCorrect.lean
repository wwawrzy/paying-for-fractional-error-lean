import Paper.Preliminaries.TerminalData

/-! Full correctness of the actual terminal data protocol: exact execution,
physical soundness, and cost completeness against any bounded competitor. -/
namespace Paper.TerminalDataCorrect
open BroadcastModel TerminalData
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
variable (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
variable (k : ℕ) (hsize : I.card ≤ k) (B q T : ℕ) (l : List V)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
variable (hl : ∀ v ∈ PhysicalTasks.vertices G D R L Q I, (s v).demands = l)
variable (hlist : ∀ r ∈ l, r ∈ PhysicalTasks.vertices G D R L Q I)
include hI hsize ha hc hb hl hlist

theorem run_correct (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) :
    (program C (4 * k) B q T m).run G s v = TabularSearch.choose
      (ActualTable.table G C (4 * k) B T (fun u => maskInput (s u)) v) m
      (DemandValues.values T l multiplicity) := by
  have hvalues := DemandValues.physical_task G C D R L Q I hI k hsize q T l multiplicity
    (fun u => valueInput (s u)) ha hb hl hlist v hv
  rw [run_program]
  dsimp only
  rw [hvalues]
  rfl

theorem complete (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ PhysicalTasks.vertices G D R L Q I → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (program C (4 * k) B q T m).run G s v = some w ∧
      TabularSearch.price w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  let row := fun u => LocalDemandMask.mask T l u (G.neighborFinset u)
  let A := ActualTable.table G C (4 * k) B T (fun u => maskInput (s u)) v
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
    have huH : u ∈ PhysicalTasks.vertices G D R L Q I := by
      by_cases huH : u ∈ PhysicalTasks.vertices G D R L Q I
      · exact huH
      · have hh := hsupport u huH
        omega
    exact ActualTable.representative G D R L Q I hI k hsize B T l cost C
      (fun u => maskInput (s u)) ha hc hl v hv u huH
  obtain ⟨w, hw, hcost⟩ := IntegralTable.choose_complete A row (fun u => (cost u).val) m
    (DemandValues.values T l multiplicity) p hsizep hrows hrep
  exact ⟨w, (run_correct G D R L Q I hI k hsize B q T l cost multiplicity C s
    ha hc hb hl hlist m v hv).trans hw, hcost⟩

theorem sound (hlen : l.length ≤ T) (hz : ∀ r, r ∉ l → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (w : List (TabularSearch.Entry V T)) (hw : (program C (4 * k) B q T m).run G s v = some w) :
    (∑ u, TableInterpretation.multiplicity w u) ≤ m ∧
      (∀ u, u ∉ PhysicalTasks.vertices G D R L Q I → TableInterpretation.multiplicity w u = 0) ∧
      (∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, TableInterpretation.multiplicity w u) ∧
      IntegralTable.cost (fun u => (cost u).val) (TableInterpretation.multiplicity w) = TabularSearch.price w := by
  rw [run_correct G D R L Q I hI k hsize B q T l cost multiplicity C s ha hc hb hl hlist m v hv] at hw
  obtain ⟨hwlen, hwalphabet, hwrows⟩ := TabularSearch.choose_sound _ m _ hw
  have he (e : TabularSearch.Entry V T) (hem : e ∈ w) :=
    ActualTable.wellformed G D R L Q I hI k hsize B T l cost C
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

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (hw : w ∈ PhysicalTasks.vertices G D R L Q I) :
    (program C (4 * k) B q T m).run G s v = (program C (4 * k) B q T m).run G s w := by
  have ht : ActualTable.table G C (4 * k) B T (fun u => maskInput (s u)) v =
      ActualTable.table G C (4 * k) B T (fun u => maskInput (s u)) w :=
    (TerminalAlphabet.physical_alphabet G C D R L Q I hI k hsize B T l cost
      (fun u => maskInput (s u)) ha hc hl v hv).trans
      (TerminalAlphabet.physical_alphabet G C D R L Q I hI k hsize B T l cost
        (fun u => maskInput (s u)) ha hc hl w hw).symm
  rw [run_correct G D R L Q I hI k hsize B q T l cost multiplicity C s ha hc hb hl hlist m v hv,
    run_correct G D R L Q I hI k hsize B q T l cost multiplicity C s ha hc hb hl hlist m w hw, ht]
end Paper.TerminalDataCorrect
