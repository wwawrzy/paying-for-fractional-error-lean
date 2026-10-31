import Paper.Preliminaries.TerminalProtocolCorrect
import Paper.Preliminaries.ActiveTerminalData

/-! Complete actual small-demand terminal on arbitrary active task geometry. -/
namespace Paper.ActiveTerminalProtocol
open BroadcastModel TerminalProtocol TerminalProtocolCorrect
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B q T : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
include ha hc hb

theorem chosen (v : V) (hv : v ∈ K.vertices) :
    (dataState G C K.diameter B q T s v).demands =
      demandList (K.vertices) multiplicity T := by
  let H := K.vertices
  let active : V → Bool := fun u => decide (u ∈ H)
  let eligible : V → Bool := fun u => decide (0 < (multiplicity u).val)
  have hi : (fun u => selectionInput (s u)) = fun u => (active u, eligible u) := by
    funext u
    dsimp only [selectionInput]
    rw [ha u, hb u]
  have he : SelectStep.candidates active eligible = demands H multiplicity := by
    ext u
    simp [SelectStep.candidates, active, eligible, demands]
  have hne := K.nonempty
  have hs := ActiveTask.tree G K C
  have har : active (H.min' hne) = true := decide_eq_true (Finset.min'_mem _ hne)
  have hh := (SelectCorrect.invariant G C K.diameter active eligible (H.min' hne) hs har T).2
    v (decide_eq_true hv)
  change ((SelectProtocol.program C K.diameter T).run G (fun u => selectionInput (s u)) v).chosen = _
  rw [hi]
  simpa only [he] using hh

theorem complete (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ K.vertices → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (program C K.diameter B q T m).run G s v = some w ∧
      TabularSearch.price w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  rw [run_program]
  exact ActiveTerminalData.complete G K B q T
    (demandList (K.vertices) multiplicity T) cost multiplicity C
    (dataState G C K.diameter B q T s) ha hc hb
    (chosen G K B q T cost multiplicity C s ha hc hb)
    (fun r hr => list_inside _ multiplicity T hr) m v hv p hsizep hsupport hcover

theorem sound (hsmall : (demands (K.vertices) multiplicity).card ≤ T)
    (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (w : List (TabularSearch.Entry V T)) (hw : (program C K.diameter B q T m).run G s v = some w) :
    (∑ u, TableInterpretation.multiplicity w u) ≤ m ∧
      (∀ u, u ∉ K.vertices → TableInterpretation.multiplicity w u = 0) ∧
      (∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, TableInterpretation.multiplicity w u) ∧
      IntegralTable.cost (fun u => (cost u).val) (TableInterpretation.multiplicity w) = TabularSearch.price w := by
  rw [run_program] at hw
  exact ActiveTerminalData.sound G K B q T
    (demandList (K.vertices) multiplicity T) cost multiplicity C
    (dataState G C K.diameter B q T s) ha hc hb
    (chosen G K B q T cost multiplicity C s ha hc hb)
    (fun r hr => list_inside _ multiplicity T hr)
    (MinimumList.run_length _ T) (fun r hr => zero_outside _ multiplicity T hsmall hz hr) m v hv w hw

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ K.vertices)
    (hw : w ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = (program C K.diameter B q T m).run G s w := by
  rw [run_program]
  exact ActiveTerminalData.uniform G K B q T
    (demandList (K.vertices) multiplicity T) cost multiplicity C
    (dataState G C K.diameter B q T s) ha hc hb
    (chosen G K B q T cost multiplicity C s ha hc hb)
    (fun r hr => list_inside _ multiplicity T hr) m v w hv hw
end Paper.ActiveTerminalProtocol
