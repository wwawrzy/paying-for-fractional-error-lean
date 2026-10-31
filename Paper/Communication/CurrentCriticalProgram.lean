import Paper.Communication.CurrentThresholdProgram
import Paper.Communication.CappedWholeProgram
import Paper.Communication.ProgramMemory
import Paper.Endpoints.Rounding.CurrentCountBound
import Paper.Preliminaries.MaskedLPOptimum

/-!
Current integer-density endpoint, using the current two-round preprocessing.
The weighted partial solver runs on the original physical graph. Every closed
neighborhood of a current demand is contained in the candidate set, so a local
zero guard and integer cap suffice; no masked-graph simulation is necessary.
The preprocessing state is carried privately through the actual solver.
-/

namespace Paper.CurrentCriticalProgram

open BroadcastModel SevenFoundation
open scoped BigOperators

section Programs

variable {V : Type} [DecidableEq V] {N : ℕ}

/-- Local integer projection: cap at the public denominator, then zero
coordinates outside the candidates. Neither step communicates. -/
def project (d D : ℕ) (st : Fin N × CurrentZoneProgram.Env d) : Fin (D + 1) :=
  if st.2.candidate then CappedWholeProgram.cap D st.1 else 0

/-- Run current preprocessing, preserve its private output through the
weighted partial solver, and return the capped, guarded numerator. -/
def auxiliaryProgram (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    Program V Unit (Fin (D + 1) × CurrentZoneProgram.Env d) :=
  .seq (CurrentZoneProgram.program d)
    (.seq (.local fun _ _ e => ((e.demand, e.cost), e))
      (.seq (ProgramMemory.carry P)
        (.local fun _ _ st => (project d D st, st.2))))

/-- The actual complete current program; the last three broadcasts are
exactly the common rounding, on the preserved current environment. -/
def program (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) : Program V Unit Bool :=
  .seq (auxiliaryProgram d D P) (CurrentThresholdProgram.program d D (D + 1))

theorem auxiliary_rounds (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (auxiliaryProgram d D P).rounds = P.rounds + 2 := by
  simp only [auxiliaryProgram, Program.rounds, ProgramMemory.rounds,
    CurrentZoneProgram.rounds]
  omega

theorem rounds (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program d D P).rounds = P.rounds + 5 := by
  rw [program, Program.rounds, auxiliary_rounds, CurrentThresholdProgram.rounds]

theorem auxiliary_maxBits (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (auxiliaryProgram d D P).maxBits = max 1 P.maxBits := by
  simp only [auxiliaryProgram, Program.maxBits, ProgramMemory.maxBits,
    CurrentZoneProgram.maxBits]
  rw [max_eq_left (Nat.zero_le P.maxBits), max_eq_right (Nat.zero_le P.maxBits)]

theorem maxBits (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program d D P).maxBits = max 1 P.maxBits := by
  rw [program, Program.maxBits, auxiliary_maxBits, CurrentThresholdProgram.maxBits]
  exact max_eq_left (le_max_left 1 P.maxBits)

end Programs

section Mathematics

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def weights (d : ℕ) (v : V) : ℝ :=
  ((CurrentZoneProgram.expected G d v).cost.val : ℝ)

theorem weights_nonneg (d : ℕ) (v : V) : 0 ≤ weights G d v := Nat.cast_nonneg _

theorem weights_eq (d : ℕ) {v : V} (hv : v ∈ CurrentBudget.candidates G d) :
    weights G d v = CurrentBudget.boundaryCost G d v :=
  CurrentZoneProgram.cost_correct G d hv

/-- An auxiliary cover is a partial dominating vector on the original G;
for each demand the candidate restriction removes no closed neighbor. -/
theorem auxiliary_to_partial (d : ℕ) (x : V → ℝ)
    (hx : feasible (CurrentBudget.auxiliary G d) x) :
    PartialOptimum.Feasible G (CurrentBudget.demands G d) x := by
  refine ⟨hx.1, ?_⟩
  intro r hr
  have h := hx.2.2 r hr
  change 1 ≤ ∑ v ∈ closed G r ∩ CurrentBudget.candidates G d, x v at h
  rwa [Finset.inter_eq_left.mpr
    (CurrentBudget.demand_closed_subset_candidates G d hr)] at h

theorem auxiliary_objective_eq (d : ℕ) (x : V → ℝ)
    (hx : feasible (CurrentBudget.auxiliary G d) x) :
    PartialOptimum.objective (weights G d) x =
      cost (CurrentBudget.auxiliary G d) x := by
  classical
  unfold PartialOptimum.objective cost
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ CurrentBudget.candidates G d
  · simp only [CurrentBudget.auxiliary, if_pos hv, weights_eq G d hv]
  · have hz : x v = 0 := hx.2.1 v hv
    simp only [hz, mul_zero]

/-- Restriction needs only the current partial constraints, not a feasible
dominating vector for all vertices. -/
theorem partial_restrict_feasible (d : ℕ) (x : V → ℝ)
    (hx : PartialOptimum.Feasible G (CurrentBudget.demands G d) x) :
    feasible (CurrentBudget.auxiliary G d) (CurrentBudget.restrict G d x) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp [CurrentBudget.restrict]
    split_ifs <;> first | exact hx.1 v | exact le_rfl
  · intro v hv
    change v ∉ CurrentBudget.candidates G d at hv
    simp [CurrentBudget.restrict, hv]
  · intro r hr
    change r ∈ CurrentBudget.demands G d at hr
    have hsub := CurrentBudget.demand_closed_subset_candidates G d hr
    change 1 ≤ ∑ v ∈ closed G r ∩ CurrentBudget.candidates G d,
      CurrentBudget.restrict G d x v
    rw [Finset.inter_eq_left.mpr hsub]
    have he : (∑ v ∈ closed G r, CurrentBudget.restrict G d x v) =
        ∑ v ∈ closed G r, x v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [CurrentBudget.restrict, if_pos (hsub hv)]
    rw [he]
    exact hx.2 r hr

theorem restrict_cost_le (d : ℕ) (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    cost (CurrentBudget.auxiliary G d) (CurrentBudget.restrict G d x) ≤
      PartialOptimum.objective (weights G d) x := by
  classical
  unfold cost PartialOptimum.objective
  apply Finset.sum_le_sum
  intro v _
  by_cases hv : v ∈ CurrentBudget.candidates G d
  · simp only [CurrentBudget.auxiliary, CurrentBudget.restrict, if_pos hv,
      weights_eq G d hv, le_refl]
  · simp only [CurrentBudget.auxiliary, CurrentBudget.restrict, if_neg hv, zero_mul]
    exact mul_nonneg (weights_nonneg G d v) (hx v)

theorem original_number_le_auxiliary (d : ℕ) :
    PartialOptimum.number G (CurrentBudget.demands G d) (weights G d) ≤
      CurrentBudget.auxiliaryNumber G d := by
  unfold CurrentBudget.auxiliaryNumber
  apply le_csInf (CurrentBudget.auxiliaryFeasibleCosts_nonempty G d)
  rintro t ⟨x, hx, rfl⟩
  rw [← auxiliary_objective_eq G d x hx]
  exact MaskedLPOptimum.number_le_feasible G (CurrentBudget.demands G d)
    (weights G d) (weights_nonneg G d) x (auxiliary_to_partial G d x hx)

/-- The full optimum bridge, including the reverse inequality. Positive
dummy costs outside C do not change the optimum because those coordinates
can be zeroed without affecting any constraint. -/
theorem optimum_eq (d : ℕ) :
    PartialOptimum.number G (CurrentBudget.demands G d) (weights G d) =
      CurrentBudget.auxiliaryNumber G d := by
  apply le_antisymm (original_number_le_auxiliary G d)
  obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number G
    (CurrentBudget.demands G d) (weights G d) (weights_nonneg G d)
  calc
    _ ≤ cost (CurrentBudget.auxiliary G d) (CurrentBudget.restrict G d x) :=
      csInf_le (CurrentBudget.auxiliaryFeasibleCosts_bddBelow G d)
        ⟨CurrentBudget.restrict G d x, partial_restrict_feasible G d x hx, rfl⟩
    _ ≤ PartialOptimum.objective (weights G d) x := restrict_cost_le G d x hx.1
    _ = _ := he

/-- Capping and guarding preserve feasibility and the solver's relative
guarantee against the actual current auxiliary optimum. -/
theorem cap_restrict_spec (d : ℕ) (x : V → ℝ)
    (hx : PartialOptimum.Feasible G (CurrentBudget.demands G d) x)
    (δ : ℝ)
    (hc : PartialOptimum.objective (weights G d) x ≤
      (1 + δ) * PartialOptimum.number G (CurrentBudget.demands G d) (weights G d)) :
    feasible (CurrentBudget.auxiliary G d)
        (CurrentBudget.restrict G d (PartialOptimum.cap x)) ∧
      (∀ v, CurrentBudget.restrict G d (PartialOptimum.cap x) v ≤ 1) ∧
      cost (CurrentBudget.auxiliary G d)
        (CurrentBudget.restrict G d (PartialOptimum.cap x)) ≤
        (1 + δ) * CurrentBudget.auxiliaryNumber G d := by
  have hcap := PartialOptimum.cap_feasible G (CurrentBudget.demands G d) x hx
  refine ⟨partial_restrict_feasible G d _ hcap, ?_, ?_⟩
  · intro v
    unfold CurrentBudget.restrict
    split_ifs
    · exact min_le_left 1 (x v)
    · exact zero_le_one
  · calc
      _ ≤ PartialOptimum.objective (weights G d) (PartialOptimum.cap x) :=
        restrict_cost_le G d _ hcap.1
      _ ≤ PartialOptimum.objective (weights G d) x :=
        PartialOptimum.cap_cost_le _ _ (weights_nonneg G d)
      _ ≤ (1 + δ) * CurrentBudget.auxiliaryNumber G d := by
        simpa only [optimum_eq G d] using hc

theorem project_value (d D : ℕ) (hD : 0 < D) {N : ℕ} (p : V → Fin N) :
    (fun v => ((project d D (p v, CurrentZoneProgram.expected G d v)).val : ℝ) / D) =
      CurrentBudget.restrict G d
        (PartialOptimum.cap (fun v => ((p v).val : ℝ) / D)) := by
  classical
  funext v
  by_cases hv : v ∈ CurrentBudget.candidates G d
  · change ((if decide (v ∈ CurrentBudget.candidates G d) then
        CappedWholeProgram.cap D (p v) else 0).val : ℝ) / D = _
    simp only [hv, decide_true, if_true, CurrentBudget.restrict]
    exact CappedWholeProgram.cap_value D hD (p v)
  · change ((if decide (v ∈ CurrentBudget.candidates G d) then
        CappedWholeProgram.cap D (p v) else 0).val : ℝ) / D = _
    simp only [hv, decide_false, Bool.false_eq_true, if_false, Fin.val_zero,
      Nat.cast_zero, zero_div, CurrentBudget.restrict]

end Mathematics

section Semantics

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {N : ℕ}

def raw (d : ℕ) (P : Program V (Bool × Fin (d + 2)) (Fin N)) : V → Fin N :=
  P.run G (fun v => ((CurrentZoneProgram.expected G d v).demand,
    (CurrentZoneProgram.expected G d v).cost))

def numerators (d D : ℕ) (P : Program V (Bool × Fin (d + 2)) (Fin N))
    (v : V) : Fin (D + 1) :=
  project d D (raw G d P v, CurrentZoneProgram.expected G d v)

theorem auxiliary_run (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    (auxiliaryProgram d D P).run G (fun _ => ()) =
      fun v => (numerators G d D P v, CurrentZoneProgram.expected G d v) := by
  change (fun v =>
    let st := (ProgramMemory.carry P).run G
      (fun u =>
        let e := (CurrentZoneProgram.program d).run G (fun _ => ()) u
        ((e.demand, e.cost), e)) v
    (project d D st, st.2)) = _
  rw [CurrentZoneProgram.correct G d, ProgramMemory.run G P]
  rfl

def output (d D : ℕ) (P : Program V (Bool × Fin (d + 2)) (Fin N)) : Finset V :=
  Finset.univ.filter (fun v => (program d D P).runEncoded G (fun _ => ()) v)

theorem output_eq_threshold (d D : ℕ)
    (P : Program V (Bool × Fin (d + 2)) (Fin N)) :
    output G d D P =
      CurrentThresholdProgram.output G d D (D + 1) (numerators G d D P) := by
  unfold output CurrentThresholdProgram.output
  simp only [Program.runEncoded_eq_run]
  change Finset.univ.filter (fun v => (CurrentThresholdProgram.program d D (D + 1)).run G
      ((auxiliaryProgram d D P).run G (fun _ => ())) v) = _
  rw [auxiliary_run G d D P]

/-- Generic composition theorem. Its only solver premise is the ordinary
weighted partial-LP guarantee on the physical graph; no current-rounding
inequality or auxiliary optimum is postulated. -/
theorem correct (a : ℝ) (ha : 1 ≤ a) (d D : ℕ) (hd : (d : ℝ) = 2 * a)
    (hD : 0 < D) (P : Program V (Bool × Fin (d + 2)) (Fin N))
    (hden : MinorDensity.Bound G a)
    (hraw : PartialOptimum.Feasible G (CurrentBudget.demands G d)
        (fun v => ((raw G d P v).val : ℝ) / D) ∧
      PartialOptimum.objective (weights G d) (fun v => ((raw G d P v).val : ℝ) / D) ≤
        (1 + CurrentCountBound.accuracy d) *
          PartialOptimum.number G (CurrentBudget.demands G d) (weights G d)) :
    dominates G (output G d D P) ∧
      ((output G d D P).card : ℝ) ≤ (2 * a + 1) * fractionalNumber G := by
  let x := fun v => ((numerators G d D P v).val : ℝ) / D
  have he : x = CurrentBudget.restrict G d
      (PartialOptimum.cap (fun v => ((raw G d P v).val : ℝ) / D)) :=
    project_value G d D hD (raw G d P)
  have hs := cap_restrict_spec G d _ hraw.1 (CurrentCountBound.accuracy d) hraw.2
  rw [← he] at hs
  have hc : ∀ v ∈ CurrentBudget.candidates G d, x v ≤ 1 := fun v _ => hs.2.1 v
  have ho := CurrentThresholdProgram.output_eq G d D (D + 1) hD a hd
    (numerators G d D P) hs.1 hc
  have hb := CurrentCountBound.rounded_output_bound G a d hd x hs.1 hc ha hden hs.2.2
  have hout : output G d D P = CurrentBudget.selected G d ∪
      CurrentRounding.output G a (CurrentCounting.input G a d hd x hs.1 hc) := by
    rw [output_eq_threshold G d D P]
    exact ho
  rw [hout]
  have hcoeff : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
  simpa only [hcoeff] using hb

end Semantics

section SolverEndpoint

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Fixed public message constant. The extra one accounts for the five
current preprocessing/rounding broadcasts, each of width one. -/
def messageConstant (d A L Δ r k Q T s q M c : ℕ) : ℕ :=
  max 1 (max (1 + GeneralInitBroadcast.rank A * (c + 1))
    (PartialFractionalBudget.constant L Δ r k Q T s A (d + 1) q M c))

theorem logarithmic_bits {b : ℕ} (C : BitCode V b)
    (d A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) (n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program d (PartialFractionalProgram.denominator Δ k Q T s q)
      (GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ)).maxBits ≤
      messageConstant d A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  rw [maxBits]
  have hp := GeneralFractionalBroadcast.logarithmic_bits C A L Δ r k t Q T s
    (d + 1) q M hQ n c hids
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hc : 1 ≤ messageConstant d A L Δ r k Q T s q M c := le_max_left _ _
  have hm : max (1 + GeneralInitBroadcast.rank A * (c + 1))
      (PartialFractionalBudget.constant L Δ r k Q T s A (d + 1) q M c) ≤
      messageConstant d A L Δ r k Q T s q M c := le_max_right _ _
  apply max_le
  · exact (by simpa only [Nat.one_mul] using Nat.mul_le_mul hc hl)
  · exact hp.trans (Nat.mul_le_mul_right _ hm)

set_option maxHeartbeats 1500000 in
/-- Public integer parameters are chosen before the graph, identifier code
and any execution. This is the current exact (2a+1) fractional endpoint,
with an actual encoded program, solver rounds plus five, and a logarithmic
broadcast-message bound. -/
theorem parameters (a : ℝ) (ha : 1 ≤ a) (d : ℕ) (hd : (d : ℝ) = 2 * a) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        dominates G (output G d D P) ∧
          ((output G d D P).card : ℝ) ≤ (2 * a + 1) * fractionalNumber G ∧
          (program d D P).rounds = P.rounds + 5 ∧
          (program d D P).maxBits = max 1 P.maxBits ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program d D P).maxBits ≤
              messageConstant d A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  have hδ := CurrentCountBound.accuracy_pos a d hd ha
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
    GeneralFractionalBroadcast.parameters a ha (d + 1) (CurrentCountBound.accuracy d) hδ
  refine ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden b C
  let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ
  let D := PartialFractionalProgram.denominator Δ k Q T s q
  have hD : 0 < D := PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq
  have hr := hrun G hden C (CurrentBudget.demands G d)
    (fun v => (CurrentZoneProgram.expected G d v).cost)
    (CurrentZoneProgram.cost_positive G d)
  dsimp only at hr ⊢
  simp only [Program.runEncoded_eq_run] at hr
  have hraw : PartialOptimum.Feasible G (CurrentBudget.demands G d)
      (fun v => ((raw G d P v).val : ℝ) / D) ∧
      PartialOptimum.objective (weights G d) (fun v => ((raw G d P v).val : ℝ) / D) ≤
        (1 + CurrentCountBound.accuracy d) *
          PartialOptimum.number G (CurrentBudget.demands G d) (weights G d) := by
    exact hr
  have hgood := correct G a ha d D hd hD P hden hraw
  refine ⟨hgood.1, hgood.2, rounds d D P, maxBits d D P, ?_⟩
  intro n c hids
  exact logarithmic_bits C d A L Δ r k t Q T s q M hQ n c hids

end SolverEndpoint

end Paper.CurrentCriticalProgram
