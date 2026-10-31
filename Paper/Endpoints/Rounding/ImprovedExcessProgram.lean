import Paper.Endpoints.Rounding.NoncriticalSelectionProgram
import Paper.Endpoints.Rounding.ImprovedExcessGeometry

/-! Three one-bit broadcasts implement the exact unfiltered improved rounding.
Each vertex compares only its own private real input with the public threshold.
As in the broadcast model, local maps permit exact comparisons; no real value
is transmitted and no effective representation of arbitrary reals is assumed. -/
namespace Paper.ImprovedExcessProgram
open BroadcastModel SevenFoundation
open NoncriticalSelectionProgram (State removeFirst selectHigh removeHigh)
variable {V : Type} [DecidableEq V]

noncomputable def start (threshold : ℝ) : Program V ℝ State := by
  classical
  exact .local fun _ _ x => ⟨true, true, decide (threshold < x), false, false, false⟩

noncomputable def program (k : ℕ) (threshold : ℝ) : Program V ℝ Bool :=
  .seq (start threshold) (.seq removeFirst (.seq (selectHigh k) (.seq removeHigh
    (.local fun _ _ st => st.first || st.high || st.last))))

theorem rounds (k : ℕ) (threshold : ℝ) :
    (program (V := V) k threshold).rounds = 3 := rfl

theorem maxBits (k : ℕ) (threshold : ℝ) :
    (program (V := V) k threshold).maxBits = 1 := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def expected (k : ℕ) (threshold : ℝ) (x : V → ℝ)
    (phase : ℕ) (v : V) : State :=
  ⟨true, true,
    decide (v ∈ ImprovedExcess.first G k threshold x),
    if 1 ≤ phase then decide (v ∈ ImprovedExcess.residual G k threshold x) else false,
    if 2 ≤ phase then decide (v ∈ ImprovedExcess.high G k threshold x) else false,
    if 3 ≤ phase then decide (v ∈ ImprovedExcess.last G k threshold x) else false⟩

theorem start_correct (k : ℕ) (threshold : ℝ) (x : V → ℝ) :
    (start threshold).run G x = expected G k threshold x 0 := by
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [start, Program.run, expected, ImprovedExcess.first]

theorem removeFirst_correct (k : ℕ) (threshold : ℝ) (x : V → ℝ) :
    removeFirst.run G (expected G k threshold x 0) = expected G k threshold x 1 := by
  rw [removeFirst, ObserveProgram.run G _ _ _ (ImprovedExcess.first G k threshold x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, ImprovedExcess.residual, ClosedBitProgram.covered_iff]

theorem selectHigh_correct (k : ℕ) (threshold : ℝ) (x : V → ℝ) :
    (selectHigh k).run G (expected G k threshold x 1) = expected G k threshold x 2 := by
  rw [selectHigh, ObserveProgram.run G _ _ _ (ImprovedExcess.residual G k threshold x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, ImprovedExcess.high, ImprovedExcess.hits]

theorem removeHigh_correct (k : ℕ) (threshold : ℝ) (x : V → ℝ) :
    removeHigh.run G (expected G k threshold x 2) = expected G k threshold x 3 := by
  rw [removeHigh, ObserveProgram.run G _ _ _ (ImprovedExcess.high G k threshold x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, ImprovedExcess.last, ClosedBitProgram.covered_iff]

theorem correct (k : ℕ) (threshold : ℝ) (x : V → ℝ) :
    (program k threshold).run G x =
      fun v => decide (v ∈ ImprovedExcess.output G k threshold x) := by
  change (fun v => let st := removeHigh.run G ((selectHigh k).run G
    (removeFirst.run G ((start threshold).run G x))) v;
      st.first || st.high || st.last) = _
  rw [start_correct G k threshold x, removeFirst_correct, selectHigh_correct, removeHigh_correct]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [expected, ImprovedExcess.output, or_assoc]

end Paper.ImprovedExcessProgram

#print axioms Paper.ImprovedExcessProgram.correct
#print axioms Paper.ImprovedExcessProgram.rounds
#print axioms Paper.ImprovedExcessProgram.maxBits
