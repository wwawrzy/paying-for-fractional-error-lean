import Paper.Communication.CurrentCriticalProgram
import Paper.Averaging.Tasks.KT0Compiler

/-!
KT0 startup for the current integer-density endpoint. The first broadcast
exchanges identifiers; the subsequent execution is exactly the current KT1
program, for every port numbering. The startup adds one round and changes
the maximum width from max 1 solverBits to max idBits (max 1 solverBits).

The source is staged outside Paper; its import names the intended installed
location of CurrentCriticalProgram. No older distance-two preprocessing is
used. The final certificate also exposes the universal integer-case slack
and the transformed-optimum budget of Theorem B.
-/

namespace Paper.CurrentCriticalKT0

open BroadcastModel (BitCode)
open SevenFoundation

section Programs

variable {V : Type} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Standalone instance transformation with no initial neighbor IDs. -/
def preprocess {b : ℕ} (C : BitCode V b) (d : ℕ) :
    PortBroadcastModel.Program V Unit (CurrentZoneProgram.Env d) :=
  KT0Compiler.program C (CurrentZoneProgram.program d)

theorem preprocess_rounds {b : ℕ} (C : BitCode V b) (d : ℕ) :
    (preprocess C d).rounds = 3 := by
  rw [preprocess, KT0Compiler.program_rounds, CurrentZoneProgram.rounds]

theorem preprocess_maxBits {b : ℕ} (C : BitCode V b) (d : ℕ) :
    (preprocess C d).maxBits = max b 1 := by
  rw [preprocess, KT0Compiler.program_maxBits, CurrentZoneProgram.maxBits]

def program {b : ℕ} (C : BitCode V b) (d D : ℕ)
    (P : BroadcastModel.Program V (Bool × Fin (d + 2)) (Fin N)) :
    PortBroadcastModel.Program V Unit Bool :=
  KT0Compiler.program C (CurrentCriticalProgram.program d D P)

theorem rounds {b : ℕ} (C : BitCode V b) (d D : ℕ)
    (P : BroadcastModel.Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program C d D P).rounds = P.rounds + 6 := by
  rw [program, KT0Compiler.program_rounds, CurrentCriticalProgram.rounds]
  omega

theorem maxBits {b : ℕ} (C : BitCode V b) (d D : ℕ)
    (P : BroadcastModel.Program V (Bool × Fin (d + 2)) (Fin N)) :
    (program C d D P).maxBits = max b (max 1 P.maxBits) := by
  rw [program, KT0Compiler.program_maxBits, CurrentCriticalProgram.maxBits]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem preprocess_correct (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (C : BitCode V b) (d : ℕ) :
    (preprocess C d).runEncoded G ports (fun _ => ()) = CurrentZoneProgram.expected G d := by
  rw [preprocess, KT0Compiler.program_encoded_correct, CurrentZoneProgram.encoded_correct]

def output (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b)
    (d D : ℕ) (P : BroadcastModel.Program V (Bool × Fin (d + 2)) (Fin N)) : Finset V :=
  Finset.univ.filter (fun v => (program C d D P).runEncoded G ports (fun _ => ()) v)

/-- This equality concerns the encoded physical port execution, uniformly
over all local port numberings, rather than an abstract simulator output. -/
theorem output_eq (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b)
    (d D : ℕ) (P : BroadcastModel.Program V (Bool × Fin (d + 2)) (Fin N)) :
    output G ports C d D P = CurrentCriticalProgram.output G d D P := by
  unfold output program
  rw [KT0Compiler.program_encoded_correct]
  rfl

end Programs

/-- Expanded fixed round bound: one identifier broadcast, two current
preprocessing broadcasts, the actual weighted solver, and three rounding
broadcasts. It depends only on the chosen public integer parameters. -/
def roundBound (A r k T M : ℕ) : ℕ :=
  (2 * A) * (4 + 2 * GeneralInitBroadcast.rank A) +
    (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r +
      RecursiveSearch.roundBound (4 * k) A M) + 6

def messageConstant (d A L Δ r k Q T s q M c : ℕ) : ℕ :=
  max c (CurrentCriticalProgram.messageConstant d A L Δ r k Q T s q M c)

section SolverEndpoint

variable {V : Type} [Fintype V] [LinearOrder V]

theorem solver_rounds {b : ℕ} (C : BitCode V b)
    (d A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C d (PartialFractionalProgram.denominator Δ k Q T s q)
      (GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ)).rounds =
      roundBound A r k T M := by
  rw [rounds, GeneralFractionalBroadcast.rounds]
  rfl

theorem logarithmic_bits {b : ℕ} (C : BitCode V b)
    (d A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) (n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C d (PartialFractionalProgram.denominator Δ k Q T s q)
      (GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ)).maxBits ≤
      messageConstant d A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) :=
  KT0Compiler.logarithmic_bits C _ n c _ hids
    (CurrentCriticalProgram.logarithmic_bits C d A L Δ r k t Q T s q M hQ n c hids)

set_option maxHeartbeats 1000000 in
/-- Exact current integer-density endpoint in KT0, with all public solver
parameters fixed before the graph, ports, and identifier representation. -/
theorem parameters (a : ℝ) (ha : 1 ≤ a) (d : ℕ) (hd : (d : ℝ) = 2 * a) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ (ports : PortBroadcastModel.Numbering G)
          {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        dominates G (output G ports C d D P) ∧
          ((output G ports C d D P).card : ℝ) ≤ (2 * a + 1) * fractionalNumber G ∧
          (program C d D P).rounds = P.rounds + 6 ∧
          (program C d D P).rounds = roundBound A r k T M ∧
          (program C d D P).maxBits = max b (max 1 P.maxBits) ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C d D P).maxBits ≤
              messageConstant d A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hp⟩ :=
    CurrentCriticalProgram.parameters a ha d hd
  refine ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden ports b C
  have h := hp G hden C
  dsimp only at h ⊢
  rw [output_eq G ports C]
  refine ⟨h.1, h.2.1, rounds C _ _ _,
    solver_rounds C d A L Δ r k t Q T s q M hQ, maxBits C _ _ _, ?_⟩
  intro n c hids
  exact logarithmic_bits C d A L Δ r k t Q T s q M hQ n c hids

end SolverEndpoint

section IntegerTheoremB

theorem accuracy_eq (a : ℝ) (d : ℕ) (hd : (d : ℝ) = 2 * a) :
    CurrentCountBound.accuracy d = 1 / (2 * a * (2 * a + 1) ^ 2) := by
  unfold CurrentCountBound.accuracy
  push_cast
  rw [hd]

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A local preprocessing of arbitrary nonnegative feasible weights. It
does not assume that the covering LP itself contains upper bounds. -/
noncomputable def capped (d : ℕ) (x : V → ℝ) : V → ℝ :=
  CurrentBudget.restrict G d (PartialOptimum.cap x)

theorem capped_spec (d : ℕ) (x : V → ℝ)
    (hx : feasible (CurrentBudget.auxiliary G d) x) :
    feasible (CurrentBudget.auxiliary G d) (capped G d x) ∧
      (∀ v ∈ CurrentBudget.candidates G d, capped G d x v ≤ 1) ∧
      cost (CurrentBudget.auxiliary G d) (capped G d x) ≤
        cost (CurrentBudget.auxiliary G d) x := by
  have hp := CurrentCriticalProgram.auxiliary_to_partial G d x hx
  have hc := PartialOptimum.cap_feasible G (CurrentBudget.demands G d) x hp
  refine ⟨CurrentCriticalProgram.partial_restrict_feasible G d _ hc, ?_, ?_⟩
  · intro v hv
    change (if v ∈ CurrentBudget.candidates G d then min 1 (x v) else 0) ≤ 1
    rw [if_pos hv]
    exact min_le_left _ _
  · calc
      _ ≤ PartialOptimum.objective (CurrentCriticalProgram.weights G d) (PartialOptimum.cap x) :=
        CurrentCriticalProgram.restrict_cost_le G d _ hc.1
      _ ≤ PartialOptimum.objective (CurrentCriticalProgram.weights G d) x :=
        PartialOptimum.cap_cost_le _ _ (CurrentCriticalProgram.weights_nonneg G d)
      _ = _ := CurrentCriticalProgram.auxiliary_objective_eq G d x hx

noncomputable def cappedInput (a : ℝ) (d : ℕ) (hd : (d : ℝ) = 2 * a)
    (x : V → ℝ) (hx : feasible (CurrentBudget.auxiliary G d) x) :
    CurrentRounding.Input G a :=
  CurrentCounting.input G a d hd (capped G d x)
    (capped_spec G d x hx).1 (capped_spec G d x hx).2.1

/-- The integer branch of Theorem B itself, including its quantifier over
every feasible capped auxiliary vector, not only the selected solver run.
The transformation is the actual two-round CurrentZoneProgram; its output
costs are exact on C by CurrentZoneProgram.cost_correct. -/
theorem integer_transformation (a : ℝ) (ha : 1 ≤ a) (d : ℕ)
    (hd : (d : ℝ) = 2 * a) (hden : MinorDensity.Bound G a) :
    let δ := 1 / (2 * a * (2 * a + 1) ^ 2)
    0 < δ ∧
      CurrentBudget.auxiliaryNumber G d ≤
        (2 * a + 1) * fractionalNumber G - (CurrentBudget.selected G d).card ∧
      (CurrentZoneProgram.program (V := V) d).rounds = 2 ∧
      (CurrentZoneProgram.program (V := V) d).maxBits = 1 ∧
      ∀ (x : V → ℝ) (hx : feasible (CurrentBudget.auxiliary G d) x)
        (hc : ∀ v ∈ CurrentBudget.candidates G d, x v ≤ 1),
        (1 + δ) *
          (CurrentRounding.output G a (CurrentCounting.input G a d hd x hx hc)).card ≤
          cost (CurrentBudget.auxiliary G d) x := by
  dsimp only
  have he := accuracy_eq a d hd
  have hpos : 0 < 1 / (2 * a * (2 * a + 1) ^ 2) := by
    rw [← he]
    exact CurrentCountBound.accuracy_pos a d hd ha
  have hb := CurrentBudget.fractional_budget G d
  have hcoeff : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
  rw [hcoeff] at hb
  refine ⟨hpos, by linarith, CurrentZoneProgram.rounds d,
    CurrentZoneProgram.maxBits d, ?_⟩
  intro x hx hc
  have hs := CurrentCountBound.output_slack G a d hd x hx hc ha hden
  rw [CurrentCountBound.objective_eq_auxiliary G a d hd x hx hc, he] at hs
  exact hs

/-- The universal slack statement in Theorem B, for every feasible vector
of the unbounded nonnegative covering LP used in the preliminaries.
The rounding map includes the harmless local cap, and its slack is paid
by the original input cost, rather than by an assumed solver bound. -/
theorem integer_transformation_all_feasible (a : ℝ) (ha : 1 ≤ a) (d : ℕ)
    (hd : (d : ℝ) = 2 * a) (hden : MinorDensity.Bound G a) :
    let δ := 1 / (2 * a * (2 * a + 1) ^ 2)
    0 < δ ∧
      CurrentBudget.auxiliaryNumber G d ≤
        (2 * a + 1) * fractionalNumber G - (CurrentBudget.selected G d).card ∧
      (CurrentZoneProgram.program (V := V) d).rounds = 2 ∧
      (CurrentZoneProgram.program (V := V) d).maxBits = 1 ∧
      ∀ (x : V → ℝ) (hx : feasible (CurrentBudget.auxiliary G d) x),
        (1 + δ) * (CurrentRounding.output G a (cappedInput G a d hd x hx)).card ≤
          cost (CurrentBudget.auxiliary G d) x := by
  obtain ⟨hpos, hbudget, hrounds, hbits, hslack⟩ :=
    integer_transformation G a ha d hd hden
  refine ⟨hpos, hbudget, hrounds, hbits, ?_⟩
  intro x hx
  have hc := capped_spec G d x hx
  exact (hslack (capped G d x) hc.1 hc.2.1).trans hc.2.2

end IntegerTheoremB

end Paper.CurrentCriticalKT0
