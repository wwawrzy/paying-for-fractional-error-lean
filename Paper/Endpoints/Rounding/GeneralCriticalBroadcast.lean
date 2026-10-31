import Paper.Endpoints.Rounding.GeneralAuxiliaryProgram
import Paper.Endpoints.Rounding.RatioCriticalRoundingProgram
import Paper.Endpoints.Rounding.ExactRounding
import Paper.Communication.EncodedProgram
import Paper.Solver.LocalSearch.GeneralFractionalBroadcast

/-! Exact (2a+1)*gamma_f at integer critical degree for one actual graph-independent CONGEST_BC
program. Initialization, task discovery, fractional search, finite-source
averaging, zone masking and final rounding are all implemented programs. -/
namespace Paper.GeneralCriticalBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    Program V Unit Bool :=
  .seq (GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ)
    (RatioCriticalRoundingProgram.program d (d + 2) 2 (PartialFractionalProgram.denominator Δ k Q T s q)
      (PartialFractionalProgram.bound L Δ k Q T s q M + 1))

def roundBound (A r k T M : ℕ) : ℕ := 7 +
  ((2 * A) * (4 + 2 * (GeneralInitBroadcast.rank A)) +
    (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) A M))

def messageConstant (A d L Δ r k Q T s q M c : ℕ) : ℕ :=
  max (1 + (GeneralInitBroadcast.rank A) * (c + 1))
    (PartialFractionalBudget.constant L Δ r k Q T s A (d + 1) q M c) + 2

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) : Finset V :=
  Finset.univ.filter (fun v => (program C A d L Δ r k t Q T s q M hQ).runEncoded G (fun _ => ()) v)

theorem rounds {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C A d L Δ r k t Q T s q M hQ).rounds = roundBound A r k T M := by
  change (GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ).rounds +
    (RatioCriticalRoundingProgram.program d (d + 2) 2 (PartialFractionalProgram.denominator Δ k Q T s q)
      (PartialFractionalProgram.bound L Δ k Q T s q M + 1)).rounds = _
  rw [GeneralAuxiliaryProgram.rounds, RatioCriticalRoundingProgram.rounds]
  unfold roundBound
  omega

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ)
    (hQ : 0 < Q) (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C A d L Δ r k t Q T s q M hQ).maxBits ≤
      messageConstant A d L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  have hp := GeneralAuxiliaryProgram.logarithmic_bits C A d L Δ r k t Q T s q M hQ n c hids
  change max (GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ).maxBits
    (RatioCriticalRoundingProgram.program d (d + 2) 2 (PartialFractionalProgram.denominator Δ k Q T s q)
      (PartialFractionalProgram.bound L Δ k Q T s q M + 1)).maxBits ≤ _
  rw [RatioCriticalRoundingProgram.maxBits]
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  unfold messageConstant
  apply max_le <;> nlinarith

theorem output_eq {b : ℕ} (C : BitCode V b) (A d L Δ r k t Q T s q M : ℕ)
    (hQ : 0 < Q) (hq : 0 < q) (a : ℝ) (hd : (d : ℝ) = 2 * a) :
    output G C A d L Δ r k t Q T s q M hQ = SelectionGeometry.output G d a
      (fun v => ((((GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ).run G
        (fun _ => ()) v).1).val : ℝ) / PartialFractionalProgram.denominator Δ k Q T s q) := by
  have hratio : (2 : ℝ) / (d + 2 : ℕ) = 1 / (a + 1) := by
    have hh : ((d + 2 : ℕ) : ℝ) = 2 * (a + 1) := by push_cast; linarith
    have ha1 : a + 1 ≠ 0 := by have hn : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
    rw [hh]
    field_simp
  have he : (GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ).run G (fun _ => ()) =
      fun v => (((GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ).run G
        (fun _ => ()) v).1, ZoneProgram.expected G d v) := by
    funext v
    exact Prod.ext rfl (GeneralAuxiliaryProgram.environment G C A d L Δ r k t Q T s q M hQ v)
  unfold output
  rw [Program.runEncoded_eq_run]
  change Finset.univ.filter (fun v => (RatioCriticalRoundingProgram.program d (d + 2) 2
    (PartialFractionalProgram.denominator Δ k Q T s q)
    (PartialFractionalProgram.bound L Δ k Q T s q M + 1)).run G
      ((GeneralAuxiliaryProgram.program C A d L Δ r k t Q T s q M hQ).run G (fun _ => ())) v) = _
  rw [he, RatioCriticalRoundingProgram.correct G _ _ _ _ _ (by omega)
    (PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq) a hratio]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

set_option maxHeartbeats 1000000 in
theorem exact_critical (a : ℝ) (ha : 1 ≤ a) (d : ℕ) (hd : (d : ℝ) = 2 * a) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ {b : ℕ} (C : BitCode V b),
        dominates G (output G C A d L Δ r k t Q T s q M hQ) ∧
          ((output G C A d L Δ r k t Q T s q M hQ).card : ℝ) ≤ (2 * a + 1) * fractionalNumber G ∧
          (program C A d L Δ r k t Q T s q M hQ).rounds = roundBound A r k T M ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C A d L Δ r k t Q T s q M hQ).maxBits ≤
              messageConstant A d L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  let A := ⌈a⌉₊
  have hA : 1 ≤ A := Nat.one_le_ceil_iff.mpr (by linarith)
  obtain ⟨L, Δ, t, k, b, T, hk, hQ, ξ, hξ, hrun⟩ :=
    GeneralAuxiliaryProgram.parameters A hA d (ExactRounding.accuracy d a) (ExactRounding.accuracy_pos d ha)
  let s := T * (3 * k + 1) + k + 2
  let r := k + s
  let q := LocalSolverMath.denominator A ξ
  let M := ⌈(q + 2 * (A : ℝ)) * (((d + 1 : ℕ) : ℝ) * k)⌉₊
  have hq : 0 < q := by have h := LocalSolverMath.denominator_pos A ξ; omega
  refine ⟨A, L, Δ, r, k, t, 2 ^ b, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden idBits C
  obtain ⟨hy, hcost⟩ := hrun G (GeneralFractionalBroadcast.density_mono G hden (Nat.le_ceil a)) C
  have hs := ExactRounding.output_bound G d a _ ha hd hden hy hcost
  rw [← output_eq G C A d L Δ r k t (2 ^ b) T s q M hQ hq a hd] at hs
  have hcoef : ((d + 1 : ℕ) : ℝ) = 2 * a + 1 := by push_cast; linarith
  rw [hcoef] at hs
  exact ⟨hs.1, hs.2, rounds C A d L Δ r k t (2 ^ b) T s q M hQ,
    fun n c hids => logarithmic_bits C A d L Δ r k t (2 ^ b) T s q M hQ n c hids⟩

end Paper.GeneralCriticalBroadcast
