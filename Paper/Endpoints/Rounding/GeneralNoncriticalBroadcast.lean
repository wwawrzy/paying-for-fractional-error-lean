import Paper.Communication.CappedWholeProgram
import Paper.Endpoints.Rounding.NoncriticalSelectionProgram
import Paper.Endpoints.Rounding.NoncriticalRationalParameters

/-! Actual encoded KT1 broadcast algorithm for noninteger 2a. Initial
neighbor identifiers are supplied by the model. A KT0 startup bridge is
a separate obligation and is not hidden in the exact round count. -/
namespace Paper.GeneralNoncriticalBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (κ m h A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    Program V Unit Bool :=
  .seq (CappedWholeProgram.program C A L Δ r k t Q T s q M hQ)
    (NoncriticalSelectionProgram.program κ m h (PartialFractionalProgram.denominator Δ k Q T s q)
      (PartialFractionalProgram.denominator Δ k Q T s q + 1))

def roundBound (A r k T M : ℕ) : ℕ := 3 +
  ((2 * A) * (4 + 2 * GeneralInitBroadcast.rank A) +
    (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) A M))

def messageConstant (A L Δ r k Q T s q M c : ℕ) : ℕ :=
  max (1 + GeneralInitBroadcast.rank A * (c + 1))
    (PartialFractionalBudget.constant L Δ r k Q T s A 1 q M c) + 1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b : ℕ} (C : BitCode V b) (κ m h A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) : Finset V :=
  Finset.univ.filter (fun v => (program C κ m h A L Δ r k t Q T s q M hQ).runEncoded G (fun _ => ()) v)

theorem rounds {b : ℕ} (C : BitCode V b) (κ m h A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C κ m h A L Δ r k t Q T s q M hQ).rounds = roundBound A r k T M := by
  change (CappedWholeProgram.program C A L Δ r k t Q T s q M hQ).rounds +
    (NoncriticalSelectionProgram.program κ m h (PartialFractionalProgram.denominator Δ k Q T s q)
      (PartialFractionalProgram.denominator Δ k Q T s q + 1)).rounds = _
  rw [CappedWholeProgram.rounds, NoncriticalSelectionProgram.rounds]
  unfold roundBound
  omega

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (κ m h A L Δ r k t Q T s q M : ℕ)
    (hQ : 0 < Q) (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C κ m h A L Δ r k t Q T s q M hQ).maxBits ≤
      messageConstant A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  have hp := GeneralFractionalBroadcast.logarithmic_bits C A L Δ r k t Q T s 1 q M hQ n c hids
  change max (CappedWholeProgram.program C A L Δ r k t Q T s q M hQ).maxBits
    (NoncriticalSelectionProgram.program κ m h (PartialFractionalProgram.denominator Δ k Q T s q)
      (PartialFractionalProgram.denominator Δ k Q T s q + 1)).maxBits ≤ _
  rw [CappedWholeProgram.maxBits, NoncriticalSelectionProgram.maxBits]
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  unfold messageConstant
  apply max_le <;> nlinarith

theorem output_eq {b : ℕ} (C : BitCode V b) (κ m h A L Δ r k t Q T s q M : ℕ)
    (hm : 0 < m) (hQ : 0 < Q) (hq : 0 < q) (σ : ℝ) (hratio : (h : ℝ) / m = σ) :
    output G C κ m h A L Δ r k t Q T s q M hQ = NoncriticalGeometry.output G κ σ
      (fun v => (((CappedWholeProgram.program C A L Δ r k t Q T s q M hQ).run G
        (fun _ => ()) v).val : ℝ) / PartialFractionalProgram.denominator Δ k Q T s q) := by
  unfold output
  rw [Program.runEncoded_eq_run]
  change Finset.univ.filter (fun v => (NoncriticalSelectionProgram.program κ m h
    (PartialFractionalProgram.denominator Δ k Q T s q)
    (PartialFractionalProgram.denominator Δ k Q T s q + 1)).run G
      ((CappedWholeProgram.program C A L Δ r k t Q T s q M hQ).run G (fun _ => ())) v) = _
  rw [NoncriticalSelectionProgram.correct G _ _ _ _ _ hm
    (PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq) σ hratio]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

set_option maxHeartbeats 1000000 in
theorem exact_noncritical (a : ℚ) (ha : 1 ≤ a) (κ : ℕ) (hκ : (κ : ℚ) < 2 * a)
    (hκ1 : 2 * a < (κ + 1 : ℕ)) :
    ∃ m h A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ {b : ℕ} (C : BitCode V b),
        dominates G (output G C κ m h A L Δ r k t Q T s q M hQ) ∧
          ((output G C κ m h A L Δ r k t Q T s q M hQ).card : ℝ) ≤ (2 * (a : ℝ) + 1) * fractionalNumber G ∧
          (program C κ m h A L Δ r k t Q T s q M hQ).rounds = roundBound A r k T M ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C κ m h A L Δ r k t Q T s q M hQ).maxBits ≤
              messageConstant A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  let θ : ℚ := 2 * a - κ
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hθ : (0 : ℝ) < θ := by
    have hh : (0 : ℚ) < θ := by dsimp only [θ]; linarith
    exact_mod_cast hh
  have hθ1 : (θ : ℝ) < 1 := by
    have hh : θ < 1 := by dsimp only [θ]; push_cast at hκ1; linarith
    exact_mod_cast hh
  have heq : 2 * (a : ℝ) = κ + (θ : ℝ) := by dsimp only [θ]; push_cast; ring
  let σ := NoncriticalRationalParameters.threshold a θ
  have hσR : (0 : ℝ) ≤ (σ : ℝ) := by
    rw [NoncriticalRationalParameters.threshold_cast]
    exact (NoncriticalParameters.threshold_bounds haR hθ hθ1).1
  have hσ : 0 ≤ σ := by exact_mod_cast hσR
  obtain ⟨m, h, hm, hr⟩ := NoncriticalRationalParameters.natural_ratio σ hσ
  have hratio : (h : ℝ) / m = NoncriticalParameters.threshold (a : ℝ) (θ : ℝ) :=
    hr.trans (NoncriticalRationalParameters.threshold_cast a θ)
  let δ := NoncriticalParameters.gain (θ : ℝ) / (2 * (a : ℝ) + 1 - NoncriticalParameters.gain (θ : ℝ))
  have hδ : 0 < δ := (NoncriticalRounding.error_cancellation (a : ℝ) (θ : ℝ) haR hθ hθ1).1
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ := CappedWholeProgram.parameters (a : ℝ) haR δ hδ
  refine ⟨m, h, A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden b C
  obtain ⟨hy, hcap, hmass⟩ := hrun G hden C
  have hs := NoncriticalOptimum.output_bound G (a : ℝ) (θ : ℝ) haR hθ hθ1 κ heq
    (MinorDensity.induced_bound G hden) _ hy hcap hmass
  rw [← output_eq G C κ m h A L Δ r k t Q T s q M hm hQ hq _ hratio] at hs
  exact ⟨hs.1, hs.2, rounds C κ m h A L Δ r k t Q T s q M hQ,
    fun n c hids => logarithmic_bits C κ m h A L Δ r k t Q T s q M hQ n c hids⟩

end Paper.GeneralNoncriticalBroadcast
