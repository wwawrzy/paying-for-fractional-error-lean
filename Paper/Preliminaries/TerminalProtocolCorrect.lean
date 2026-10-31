import Paper.Preliminaries.TerminalProtocol

/-! The complete terminal program computes its demand list itself. Its
small-demand soundness and cost completeness have no list/table oracle. -/
namespace Paper.TerminalProtocolCorrect
open BroadcastModel TerminalProtocol
variable {V : Type} [Fintype V] [LinearOrder V]

def demands (H : Finset V) {q : ℕ} (multiplicity : V → Fin (q + 1)) : Finset V :=
  H.filter (fun v => 0 < (multiplicity v).val)

def demandList (H : Finset V) {q : ℕ} (multiplicity : V → Fin (q + 1)) (T : ℕ) :=
  MinimumList.run (demands H multiplicity) T

theorem list_inside (H : Finset V) {q : ℕ} (multiplicity : V → Fin (q + 1)) (T : ℕ)
    {r : V} (hr : r ∈ demandList H multiplicity T) : r ∈ H := by
  have hm := MinimumList.run_subset (demands H multiplicity) T (List.mem_toFinset.mpr hr)
  exact (Finset.mem_filter.mp hm).1

theorem zero_outside (H : Finset V) {q : ℕ} (multiplicity : V → Fin (q + 1)) (T : ℕ)
    (hsmall : (demands H multiplicity).card ≤ T)
    (hz : ∀ r, r ∉ H → (multiplicity r).val = 0) {r : V}
    (hr : r ∉ demandList H multiplicity T) : (multiplicity r).val = 0 := by
  by_cases hrH : r ∈ H
  · apply Nat.eq_zero_of_not_pos
    intro hp
    have hm : r ∈ (demandList H multiplicity T).toFinset := by
      rw [demandList, MinimumList.complete _ T hsmall]
      exact Finset.mem_filter.mpr ⟨hrH, hp⟩
    exact hr (List.mem_toFinset.mp hm)
  · exact hz r hrH

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
variable (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
variable (k : ℕ) (hsize : I.card ≤ k) (B q T : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
include hI hsize ha hc hb

theorem chosen (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) :
    (dataState G C (4 * k) B q T s v).demands =
      demandList (PhysicalTasks.vertices G D R L Q I) multiplicity T := by
  let H := PhysicalTasks.vertices G D R L Q I
  let active : V → Bool := fun u => decide (u ∈ H)
  let eligible : V → Bool := fun u => decide (0 < (multiplicity u).val)
  have hi : (fun u => selectionInput (s u)) = fun u => (active u, eligible u) := by
    funext u
    dsimp only [selectionInput]
    rw [ha u, hb u]
  have he : SelectStep.candidates active eligible = demands H multiplicity := by
    ext u
    simp [SelectStep.candidates, active, eligible, demands]
  obtain ⟨hne, hs, _, _⟩ := TaskTree.spec G C D R L Q I hI k hsize
  have har : active (H.min' hne) = true := decide_eq_true (Finset.min'_mem _ hne)
  have hh := (SelectCorrect.invariant G C (4 * k) active eligible (H.min' hne) hs har T).2
    v (decide_eq_true hv)
  change ((SelectProtocol.program C (4 * k) T).run G (fun u => selectionInput (s u)) v).chosen = _
  rw [hi]
  simpa only [he] using hh

theorem complete (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ PhysicalTasks.vertices G D R L Q I → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (program C (4 * k) B q T m).run G s v = some w ∧
      TabularSearch.price w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  rw [run_program]
  exact TerminalDataCorrect.complete G D R L Q I hI k hsize B q T
    (demandList (PhysicalTasks.vertices G D R L Q I) multiplicity T) cost multiplicity C
    (dataState G C (4 * k) B q T s) ha hc hb
    (chosen G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb)
    (fun r hr => list_inside _ multiplicity T hr) m v hv p hsizep hsupport hcover

theorem sound (hsmall : (demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card ≤ T)
    (hz : ∀ r, r ∉ PhysicalTasks.vertices G D R L Q I → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (w : List (TabularSearch.Entry V T)) (hw : (program C (4 * k) B q T m).run G s v = some w) :
    (∑ u, TableInterpretation.multiplicity w u) ≤ m ∧
      (∀ u, u ∉ PhysicalTasks.vertices G D R L Q I → TableInterpretation.multiplicity w u = 0) ∧
      (∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, TableInterpretation.multiplicity w u) ∧
      IntegralTable.cost (fun u => (cost u).val) (TableInterpretation.multiplicity w) = TabularSearch.price w := by
  rw [run_program] at hw
  exact TerminalDataCorrect.sound G D R L Q I hI k hsize B q T
    (demandList (PhysicalTasks.vertices G D R L Q I) multiplicity T) cost multiplicity C
    (dataState G C (4 * k) B q T s) ha hc hb
    (chosen G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb)
    (fun r hr => list_inside _ multiplicity T hr)
    (MinimumList.run_length _ T) (fun r hr => zero_outside _ multiplicity T hsmall hz hr) m v hv w hw

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (hw : w ∈ PhysicalTasks.vertices G D R L Q I) :
    (program C (4 * k) B q T m).run G s v = (program C (4 * k) B q T m).run G s w := by
  rw [run_program]
  exact TerminalDataCorrect.uniform G D R L Q I hI k hsize B q T
    (demandList (PhysicalTasks.vertices G D R L Q I) multiplicity T) cost multiplicity C
    (dataState G C (4 * k) B q T s) ha hc hb
    (chosen G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb)
    (fun r hr => list_inside _ multiplicity T hr) m v w hv hw
end Paper.TerminalProtocolCorrect
