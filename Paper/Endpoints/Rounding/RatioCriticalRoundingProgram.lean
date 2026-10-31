import Paper.Communication.ObserveProgram
import Paper.Communication.ZoneProgram
import Paper.Endpoints.Rounding.SelectionGeometry

/-! Original-graph rounding uses only an own integer numerator, the public
denominator, original local degree, and three physical one-bit broadcasts. -/
namespace Paper.RatioCriticalRoundingProgram
open BroadcastModel SevenFoundation
variable {V : Type} [DecidableEq V]

@[ext] structure State where
  zone : Bool
  demand : Bool
  first : Bool
  residual : Bool
  high : Bool
  last : Bool

def start (d m h D N : ℕ) : Program V (Fin N × ZoneProgram.Env d) State :=
  .local fun _ neighbors st => ⟨st.2.zone, st.2.demand,
    st.2.zone && decide (d + 1 ≤ neighbors.card ∧ h * D < m * st.1.val), false, false, false⟩

def removeFirst : Program V State State := ObserveProgram.program State.first
  (fun _ st h => {st with residual := st.demand && !decide h.Nonempty})

def selectHigh (d : ℕ) : Program V State State := ObserveProgram.program State.residual
  (fun _ st h => {st with high := st.zone && !st.first && decide (d + 1 ≤ h.card)})

def removeHigh : Program V State State := ObserveProgram.program State.high
  (fun _ st h => {st with last := st.residual && !decide h.Nonempty})

def program (d m h D N : ℕ) : Program V (Fin N × ZoneProgram.Env d) Bool :=
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

noncomputable def expected (d : ℕ) (a : ℝ) (x : V → ℝ) (phase : ℕ) (v : V) : State :=
  ⟨decide (v ∈ WeightedBudget.zone G d), decide (v ∈ WeightedBudget.initialDemands G d),
    decide (v ∈ SelectionGeometry.first G d a x),
    if 1 ≤ phase then decide (v ∈ SelectionGeometry.residual G d a x) else false,
    if 2 ≤ phase then decide (v ∈ SelectionGeometry.high G d a x) else false,
    if 3 ≤ phase then decide (v ∈ SelectionGeometry.last G d a x) else false⟩

theorem start_correct (d m h D N : ℕ) (hm : 0 < m) (hD : 0 < D) (a : ℝ)
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (p : V → Fin N) :
    (start d m h D N).run G (fun v => (p v, ZoneProgram.expected G d v)) =
      expected G d a (fun v => ((p v).val : ℝ) / D) 0 := by
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp only [start, Program.run, ZoneProgram.expected, expected, Bool.and_eq_true,
    decide_eq_true_eq, SelectionGeometry.first, Finset.mem_filter,
    SimpleGraph.card_neighborFinset_eq_degree, ← hratio, threshold m h _ D hm hD]

theorem removeFirst_correct (d : ℕ) (a : ℝ) (x : V → ℝ) :
    removeFirst.run G (expected G d a x 0) = expected G d a x 1 := by
  rw [removeFirst, ObserveProgram.run G _ _ _ (SelectionGeometry.first G d a x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, SelectionGeometry.residual, ClosedBitProgram.covered_iff]

theorem selectHigh_correct (d : ℕ) (a : ℝ) (x : V → ℝ) :
    (selectHigh d).run G (expected G d a x 1) = expected G d a x 2 := by
  rw [selectHigh, ObserveProgram.run G _ _ _ (SelectionGeometry.residual G d a x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, SelectionGeometry.high, SelectionGeometry.hits]

theorem removeHigh_correct (d : ℕ) (a : ℝ) (x : V → ℝ) :
    removeHigh.run G (expected G d a x 2) = expected G d a x 3 := by
  rw [removeHigh, ObserveProgram.run G _ _ _ (SelectionGeometry.high G d a x) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, SelectionGeometry.last, ClosedBitProgram.covered_iff]

theorem correct (d m h D N : ℕ) (hm : 0 < m) (hD : 0 < D) (a : ℝ)
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (p : V → Fin N) :
    (program d m h D N).run G (fun v => (p v, ZoneProgram.expected G d v)) =
      fun v => decide (v ∈ SelectionGeometry.output G d a (fun u => ((p u).val : ℝ) / D)) := by
  change (fun v => let st := removeHigh.run G ((selectHigh d).run G
    (removeFirst.run G ((start d m h D N).run G (fun v => (p v, ZoneProgram.expected G d v))))) v;
      !st.zone || st.first || st.high || st.last) = _
  rw [start_correct G d m h D N hm hD a hratio p, removeFirst_correct, selectHigh_correct, removeHigh_correct]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [expected, SelectionGeometry.output, SelectionGeometry.localOutput, WeightedBudget.far,
    or_assoc]

end Paper.RatioCriticalRoundingProgram
