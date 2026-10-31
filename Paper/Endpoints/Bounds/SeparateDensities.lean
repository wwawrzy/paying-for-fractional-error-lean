import Paper.Endpoints.Rounding.MinorDensityKT0

/-!
The noninteger endpoint with separate densities: minor density `rho` is
used by the fractional solver, while subgraph density `a` determines the
exact coefficient `2*a+1`. The selected set is the output of the actual
encoded broadcast program, with the existing one-round KT0 startup.

This file does not require `MinorDensity.Bound G a`: the rounding receives
only `Incidence.InducedDensityBound G a`, independently of the solver's
minor bound at `rho`.
-/

namespace Paper.SeparateDensities

open BroadcastModel SevenFoundation

set_option maxHeartbeats 1000000 in
theorem exact_noncritical (a rho : ℚ) (ha : 1 ≤ a) (harho : a ≤ rho)
    (κ : ℕ) (hκ : (κ : ℚ) < 2 * a) (hκ1 : 2 * a < (κ + 1 : ℕ)) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (rho : ℝ) → Incidence.InducedDensityBound G (a : ℝ) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
          dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤
            (2 * (a : ℝ) + 1) * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  let θ : ℚ := 2 * a - κ
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hrhoR : (1 : ℝ) ≤ rho := by exact_mod_cast (ha.trans harho)
  have hθ : (0 : ℝ) < θ := by
    have hh : (0 : ℚ) < θ := by dsimp only [θ]; linarith
    exact_mod_cast hh
  have hθ1 : (θ : ℝ) < 1 := by
    have hh : θ < 1 := by dsimp only [θ]; push_cast at hκ1; linarith
    exact_mod_cast hh
  have heq : 2 * (a : ℝ) = κ + (θ : ℝ) := by
    dsimp only [θ]
    push_cast
    ring
  let σ := NoncriticalRationalParameters.threshold a θ
  have hσR : (0 : ℝ) ≤ (σ : ℝ) := by
    rw [NoncriticalRationalParameters.threshold_cast]
    exact (NoncriticalParameters.threshold_bounds haR hθ hθ1).1
  have hσ : 0 ≤ σ := by exact_mod_cast hσR
  obtain ⟨m, h, hm, hr⟩ := NoncriticalRationalParameters.natural_ratio σ hσ
  have hratio : (h : ℝ) / m = NoncriticalParameters.threshold (a : ℝ) (θ : ℝ) :=
    hr.trans (NoncriticalRationalParameters.threshold_cast a θ)
  let δ := NoncriticalParameters.gain (θ : ℝ) /
    (2 * (a : ℝ) + 1 - NoncriticalParameters.gain (θ : ℝ))
  have hδ : 0 < δ :=
    (NoncriticalRounding.error_cancellation (a : ℝ) (θ : ℝ) haR hθ hθ1).1
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
    CappedWholeProgram.parameters (rho : ℝ) hrhoR δ hδ
  let p : MinorDensityBroadcast.Config :=
    ⟨false, κ, m, h, A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq⟩
  refine ⟨p, ?_⟩
  intro V _ _ G _ hminor hsub ports b C
  obtain ⟨hy, hcap, hmass⟩ := hrun G hminor C
  have hs := NoncriticalOptimum.output_bound G (a : ℝ) (θ : ℝ) haR hθ hθ1 κ heq
    hsub _ hy hcap hmass
  rw [← GeneralNoncriticalBroadcast.output_eq G C κ m h A L Δ r k t Q T s q M
    hm hQ hq _ hratio] at hs
  have hspec : dominates G (MinorDensityBroadcast.output G C p) ∧
      ((MinorDensityBroadcast.output G C p).card : ℝ) ≤
        (2 * (a : ℝ) + 1) * fractionalNumber G := by
    rw [MinorDensityBroadcast.output_noncritical G C p rfl]
    exact hs
  rw [MinorDensityKT0.output_eq]
  exact ⟨hspec.1, hspec.2, MinorDensityKT0.rounds C p,
    fun n c hids => MinorDensityKT0.logarithmic_bits C p n c hids⟩

/-- Theorem C(ii): the density controlling the approximation coefficient
may be smaller than the minor density used for communication and solving. -/
theorem exact_separate_densities (a rho : ℚ) (ha : 1 ≤ a) (harho : a ≤ rho)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (rho : ℝ) → Incidence.InducedDensityBound G (a : ℝ) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
          dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤
            (2 * (a : ℝ) + 1) * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  let κ := ⌊2 * a⌋₊
  have hκ : (κ : ℚ) ≤ 2 * a := Nat.floor_le (by linarith)
  have hκ1 : 2 * a < (κ + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one (2 * a)
  have hκne : (κ : ℚ) ≠ 2 * a := by
    intro heq
    apply hnoninteger
    refine ⟨(κ : ℤ), ?_⟩
    exact_mod_cast heq
  exact exact_noncritical a rho ha harho κ (lt_of_le_of_ne hκ hκne) hκ1

end Paper.SeparateDensities
