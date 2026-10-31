import Paper.Communication.CurrentZoneProgram
import Paper.Endpoints.Rounding.RatioCriticalRoundingProgram
import Paper.Endpoints.Rounding.CurrentCounting

/-!
The current common rounding is an actual three-round one-bit program.
Unlike the older degree-based start, the current start selects precisely
full-cost candidates exceeding the threshold. For integral d=2a the test
2D < (d+2)p is the exact test p/D > 1/(a+1).

The three communication steps are reused unchanged. Their semantics are
first proved for arbitrary CurrentRounding.Input data, then specialized to
the current F=V\N[B] preprocessing and the actual integer numerators.
-/

namespace Paper.CurrentThresholdProgram

open BroadcastModel SevenFoundation
open RatioCriticalRoundingProgram (State removeFirst selectHigh removeHigh)
variable {V : Type} [DecidableEq V]

def start (d D N : ℕ) : Program V (Fin N × CurrentZoneProgram.Env d) State :=
  .local fun _ _ st => ⟨st.2.candidate, st.2.demand,
    st.2.candidate && decide (st.2.cost.val = d + 1 ∧ 2 * D < (d + 2) * st.1.val),
    false, false, false⟩

def program (d D N : ℕ) : Program V (Fin N × CurrentZoneProgram.Env d) Bool :=
  .seq (start d D N)
    (.seq removeFirst (.seq (selectHigh d) (.seq removeHigh
      (.local fun _ _ st => !st.zone || st.first || st.high || st.last))))

theorem rounds (d D N : ℕ) : (program (V := V) d D N).rounds = 3 := rfl

theorem maxBits (d D N : ℕ) : (program (V := V) d D N).maxBits = 1 := rfl

theorem threshold_ratio (d : ℕ) (a : ℝ) (hd : (d : ℝ) = 2 * a) :
    (2 : ℝ) / (d + 2 : ℕ) = 1 / (a + 1) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : 0 < a + 1 := by linarith
  have hm : (0 : ℝ) < (d + 2 : ℕ) := by positivity
  field_simp [ne_of_gt ha, ne_of_gt hm]
  push_cast
  nlinarith

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def expected (a : ℝ) (I : CurrentRounding.Input G a)
    (phase : ℕ) (v : V) : State :=
  ⟨decide (v ∈ I.candidates), decide (v ∈ I.demands),
    decide (v ∈ CurrentRounding.first G a I),
    if 1 ≤ phase then decide (v ∈ CurrentRounding.residual G a I) else false,
    if 2 ≤ phase then decide (v ∈ CurrentRounding.high G a I) else false,
    if 3 ≤ phase then decide (v ∈ CurrentRounding.last G a I) else false⟩

theorem removeFirst_correct (a : ℝ) (I : CurrentRounding.Input G a) :
    removeFirst.run G (expected G a I 0) = expected G a I 1 := by
  rw [RatioCriticalRoundingProgram.removeFirst,
    ObserveProgram.run G _ _ _ (CurrentRounding.first G a I) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, CurrentRounding.residual, ClosedBitProgram.covered_iff]

theorem selectHigh_correct (d : ℕ) (a : ℝ) (hd : (d : ℝ) = 2 * a)
    (I : CurrentRounding.Input G a) :
    (selectHigh d).run G (expected G a I 1) = expected G a I 2 := by
  rw [RatioCriticalRoundingProgram.selectHigh,
    ObserveProgram.run G _ _ _ (CurrentRounding.residual G a I) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  have hb : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
  have hn : d + 1 ≤ (closed G v ∩ CurrentRounding.residual G a I).card ↔
      2 * a + 1 ≤ ((closed G v ∩ CurrentRounding.residual G a I).card : ℝ) := by
    rw [← hb]
    norm_cast
  apply Bool.eq_iff_iff.mpr
  simp [expected, CurrentRounding.high, CurrentRounding.hits, hn]

theorem removeHigh_correct (a : ℝ) (I : CurrentRounding.Input G a) :
    removeHigh.run G (expected G a I 2) = expected G a I 3 := by
  rw [RatioCriticalRoundingProgram.removeHigh,
    ObserveProgram.run G _ _ _ (CurrentRounding.high G a I) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [expected, CurrentRounding.last, ClosedBitProgram.covered_iff]

theorem start_correct (d D N : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (p : V → Fin N)
    (hx : feasible (CurrentBudget.auxiliary G d) (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d, ((p v).val : ℝ) / D ≤ 1) :
    (start d D N).run G (fun v => (p v, CurrentZoneProgram.expected G d v)) =
      expected G a (CurrentCounting.input G a d hd
        (fun v => ((p v).val : ℝ) / D) hx hcap) 0 := by
  funext v
  apply State.ext <;> try rfl
  change (decide (v ∈ CurrentBudget.candidates G d) &&
      decide ((CurrentZoneProgram.expected G d v).cost.val = d + 1 ∧
        2 * D < (d + 2) * (p v).val)) = _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq, expected,
    CurrentRounding.first, Finset.mem_filter]
  change (v ∈ CurrentBudget.candidates G d ∧
      ((CurrentZoneProgram.expected G d v).cost.val = d + 1 ∧
        2 * D < (d + 2) * (p v).val)) ↔
    (v ∈ CurrentBudget.candidates G d ∧
      (CurrentBudget.boundaryCost G d v = 2 * a + 1 ∧
        1 / (a + 1) < ((p v).val : ℝ) / D))
  have ht : 2 * D < (d + 2) * (p v).val ↔
      1 / (a + 1) < ((p v).val : ℝ) / D := by
    rw [RatioCriticalRoundingProgram.threshold (d + 2) 2 _ D (by omega) hD]
    norm_num only [Nat.cast_ofNat]
    rw [threshold_ratio d a hd]
  by_cases hv : v ∈ CurrentBudget.candidates G d
  · have hc := CurrentZoneProgram.cost_correct G d hv
    have hb : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
    have hf : (CurrentZoneProgram.expected G d v).cost.val = d + 1 ↔
        CurrentBudget.boundaryCost G d v = 2 * a + 1 := by
      constructor
      · intro he
        rw [he] at hc
        exact hc.symm.trans hb
      · intro he
        have hreal : (((CurrentZoneProgram.expected G d v).cost).val : ℝ) = (d + 1 : ℕ) :=
          hc.trans (he.trans hb.symm)
        exact_mod_cast hreal
    simp only [hv, true_and, hf, ht]
  · simp only [hv, false_and]

theorem correct (d D N : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (p : V → Fin N)
    (hx : feasible (CurrentBudget.auxiliary G d) (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d, ((p v).val : ℝ) / D ≤ 1) :
    (program d D N).run G (fun v => (p v, CurrentZoneProgram.expected G d v)) =
      fun v => decide (v ∈ CurrentBudget.selected G d ∪
        CurrentRounding.output G a (CurrentCounting.input G a d hd
          (fun v => ((p v).val : ℝ) / D) hx hcap)) := by
  change (fun v => let st := removeHigh.run G ((selectHigh d).run G
    (removeFirst.run G ((start d D N).run G (fun v => (p v, CurrentZoneProgram.expected G d v))))) v;
      !st.zone || st.first || st.high || st.last) = _
  rw [start_correct G d D N hD a hd p hx hcap,
    removeFirst_correct, selectHigh_correct G d a hd, removeHigh_correct]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [expected, CurrentRounding.output, CurrentCounting.input, CurrentBudget.selected, or_assoc]

theorem encoded_correct (d D N : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (p : V → Fin N)
    (hx : feasible (CurrentBudget.auxiliary G d) (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d, ((p v).val : ℝ) / D ≤ 1) :
    (program d D N).runEncoded G (fun v => (p v, CurrentZoneProgram.expected G d v)) =
      fun v => decide (v ∈ CurrentBudget.selected G d ∪
        CurrentRounding.output G a (CurrentCounting.input G a d hd
          (fun v => ((p v).val : ℝ) / D) hx hcap)) := by
  rw [Program.runEncoded_eq_run]
  exact correct G d D N hD a hd p hx hcap

def output (d D N : ℕ) (p : V → Fin N) : Finset V :=
  Finset.univ.filter (fun v =>
    (program d D N).runEncoded G (fun u => (p u, CurrentZoneProgram.expected G d u)) v)

theorem output_eq (d D N : ℕ) (hD : 0 < D) (a : ℝ)
    (hd : (d : ℝ) = 2 * a) (p : V → Fin N)
    (hx : feasible (CurrentBudget.auxiliary G d) (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v ∈ CurrentBudget.candidates G d, ((p v).val : ℝ) / D ≤ 1) :
    output G d D N p = CurrentBudget.selected G d ∪
      CurrentRounding.output G a (CurrentCounting.input G a d hd
        (fun v => ((p v).val : ℝ) / D) hx hcap) := by
  unfold output
  rw [encoded_correct G d D N hD a hd p hx hcap]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

end Paper.CurrentThresholdProgram
