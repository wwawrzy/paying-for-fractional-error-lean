import Paper.Communication.ObserveProgram
import Paper.Communication.ZoneProgram
import Paper.Endpoints.Rounding.NoncriticalGeometry

/-! Original-graph rounding uses only an own integer numerator, the public
denominator, original local degree, and three physical one-bit broadcasts. -/
namespace Paper.NoncriticalSelectionProgram
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

@[ext] structure State where
  zone : Bool
  demand : Bool
  first : Bool
  residual : Bool
  high : Bool
  last : Bool

def start (d m h D N : ℕ) : Program V (Fin N) State :=
  .local fun _ neighbors st => ⟨true, true,
    decide (d + 1 ≤ neighbors.card ∧ h * D < m * st.val), false, false, false⟩

def removeFirst : Program V State State := ObserveProgram.program State.first
  (fun _ st h => {st with residual := st.demand && !decide h.Nonempty})

def selectHigh (d : ℕ) : Program V State State := ObserveProgram.program State.residual
  (fun _ st h => {st with high := st.zone && !st.first && decide (d + 2 ≤ h.card)})

def removeHigh : Program V State State := ObserveProgram.program State.high
  (fun _ st h => {st with last := st.residual && !decide h.Nonempty})

def program (d m h D N : ℕ) : Program V (Fin N) Bool :=
  .seq (start d m h D N) (.seq removeFirst (.seq (selectHigh d) (.seq removeHigh
    (.local fun _ _ st => !st.zone || st.first || st.high || st.last))))

theorem rounds (d m h D N : ℕ) : (program (V := V) d m h D N).rounds = 3 := rfl
theorem maxBits (d m h D N : ℕ) : (program (V := V) d m h D N).maxBits = 1 := rfl

theorem threshold (m h p D : ℕ) (hm : 0 < m) (hD : 0 < D) :
    h * D < m * p ↔ (h : ℝ) / m < (p : ℝ) / D := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hd' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_lt_div_iff₀ hm' hd']
  norm_cast
  rw [Nat.mul_comm p m]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def expected (d : ℕ) (σ : ℝ) (x : V → ℝ) (phase : ℕ) (v : V) : State :=
  ⟨true, true,
    decide (v ∈ NoncriticalGeometry.first G d σ x),
    if 1 ≤ phase then decide (v ∈ NoncriticalGeometry.residual G d σ x) else false,
    if 2 ≤ phase then decide (v ∈ NoncriticalGeometry.high G d σ x) else false,
    if 3 ≤ phase then decide (v ∈ NoncriticalGeometry.last G d σ x) else false⟩

theorem start_correct (d m h D N : ℕ) (hm : 0 < m) (hD : 0 < D) (σ : ℝ)
    (hratio : (h : ℝ) / m = σ) (p : V → Fin N) :
    (start d m h D N).run G p =
      expected G d σ (fun v => ((p v).val : ℝ) / D) 0 := by
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp only [start, Program.run, expected, Bool.and_eq_true,
    decide_eq_true_eq, NoncriticalGeometry.first, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.card_neighborFinset_eq_degree, ← hratio, threshold m h _ D hm hD]

theorem removeFirst_correct (d : ℕ) (σ : ℝ) (x : V → ℝ) :
    removeFirst.run G (expected G d σ x 0) = expected G d σ x 1 := by
  rw [removeFirst, ObserveProgram.run G _ _ _ (NoncriticalGeometry.first G d σ x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, NoncriticalGeometry.residual, ClosedBitProgram.covered_iff]

theorem selectHigh_correct (d : ℕ) (σ : ℝ) (x : V → ℝ) :
    (selectHigh d).run G (expected G d σ x 1) = expected G d σ x 2 := by
  rw [selectHigh, ObserveProgram.run G _ _ _ (NoncriticalGeometry.residual G d σ x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, NoncriticalGeometry.high, NoncriticalGeometry.hits]

theorem removeHigh_correct (d : ℕ) (σ : ℝ) (x : V → ℝ) :
    removeHigh.run G (expected G d σ x 2) = expected G d σ x 3 := by
  rw [removeHigh, ObserveProgram.run G _ _ _ (NoncriticalGeometry.high G d σ x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, NoncriticalGeometry.last, ClosedBitProgram.covered_iff]

theorem correct (d m h D N : ℕ) (hm : 0 < m) (hD : 0 < D) (σ : ℝ)
    (hratio : (h : ℝ) / m = σ) (p : V → Fin N) :
    (program d m h D N).run G p =
      fun v => decide (v ∈ NoncriticalGeometry.output G d σ (fun u => ((p u).val : ℝ) / D)) := by
  change (fun v => let st := removeHigh.run G ((selectHigh d).run G
    (removeFirst.run G ((start d m h D N).run G p))) v;
      !st.zone || st.first || st.high || st.last) = _
  rw [start_correct G d m h D N hm hD σ hratio p, removeFirst_correct, selectHigh_correct, removeHigh_correct]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [expected, NoncriticalGeometry.output, or_assoc]

end Paper.NoncriticalSelectionProgram
