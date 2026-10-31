import Paper.Solver.Density.RationalDensityRounding

/-! Exact noninteger-density domination with a public maximum degree.
The supplied public parameter is explicitly required to equal the physical
graph's maximum degree. This is not the unspecified-input paper endpoint. -/
namespace Paper.Density.RationalDensityEndpoint
open BroadcastModel SevenFoundation RationalParameters RationalDensityRounding
open scoped BigOperators

theorem public_parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ k t h m : ℕ, 0 < t ∧ 1 ≤ m ∧
      ∀ (W : Type) (hWf : Fintype W) (hWeq : DecidableEq W) (Δ : ℕ)
        (G : SimpleGraph W) (hG : DecidableRel G.Adj),
        letI := hWf
        letI := hWeq
        letI := hG
        Δ = G.maxDegree → Incidence.InducedDensityBound G (a : ℝ) →
          dominates G (output G k t h m Δ) ∧
            ((output G k t h m Δ).card : ℝ) ≤ (2 * (a : ℝ) + 1) * fractionalNumber G ∧
            (program (V := W) k t h m Δ).rounds ≤
              (4 * m * (m + 1) ^ 3 + 3) * (Nat.clog 2 (Δ + 2)) ^ 2 ∧
            (program (V := W) k t h m Δ).maxBits ≤
              ((2 * Nat.clog 2 (m + 2) + 5) * (m + 1) + 1) *
                Nat.clog 2 (Fintype.card W + 2) := by
  let k : ℕ := ⌊2 * a⌋₊
  have hk_le : (k : ℚ) ≤ 2 * a := Nat.floor_le (by linarith)
  have hk_ne : (k : ℚ) ≠ 2 * a := by
    intro he
    apply hnoninteger
    refine ⟨(k : ℤ), ?_⟩
    exact_mod_cast he
  have hk : (k : ℚ) < 2 * a := lt_of_le_of_ne hk_le hk_ne
  have hk1 : 2 * a < (k + 1 : ℕ) := by exact_mod_cast Nat.lt_floor_add_one (2 * a)
  let θ : ℚ := 2 * a - k
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hθ : (0 : ℝ) < θ := by
    have hh : (0 : ℚ) < θ := by dsimp only [θ]; linarith
    exact_mod_cast hh
  have hθ1 : (θ : ℝ) < 1 := by
    have hh : θ < 1 := by dsimp only [θ]; push_cast at hk1; linarith
    exact_mod_cast hh
  have heq : 2 * (a : ℝ) = k + (θ : ℝ) := by dsimp only [θ]; push_cast; ring
  let σ := NoncriticalRationalParameters.threshold a θ
  have hσR : (0 : ℝ) ≤ (σ : ℝ) := by
    rw [NoncriticalRationalParameters.threshold_cast]
    exact (NoncriticalParameters.threshold_bounds haR hθ hθ1).1
  have hσ : 0 ≤ σ := by exact_mod_cast hσR
  obtain ⟨t, h, ht, hratio⟩ := NoncriticalRationalParameters.natural_ratio σ hσ
  have hr : (h : ℝ) / t = NoncriticalParameters.threshold (a : ℝ) (θ : ℝ) :=
    hratio.trans (NoncriticalRationalParameters.threshold_cast a θ)
  let δ := NoncriticalParameters.gain (θ : ℝ) /
    (2 * (a : ℝ) + 1 - NoncriticalParameters.gain (θ : ℝ))
  have hδ : 0 < δ := (NoncriticalRounding.error_cancellation (a : ℝ) (θ : ℝ) haR hθ hθ1).1
  obtain ⟨m, hm, haccuracy⟩ := public_accuracy δ hδ
  refine ⟨k, t, h, m, ht, hm, ?_⟩
  intro W hWf hWeq Δ G hG
  letI := hWf
  letI := hWeq
  letI := hG
  intro hΔ hden
  have hdegree : ∀ v, G.degree v ≤ Δ := by
    intro v
    rw [hΔ]
    exact G.degree_le_maxDegree v
  have hcard : Δ ≤ Fintype.card W := by
    rw [hΔ]
    exact G.maxDegree_le_of_forall_degree_le _ (fun v => (G.degree_lt_card_verts v).le)
  have hout := exact_bound G hm (a : ℝ) (θ : ℝ) haR hθ hθ1 k t h Δ ht heq hr haccuracy hdegree hden
  exact ⟨hout.1, hout.2, rounds_log_squared k t h m Δ, messages_log_vertices k t h m Δ hcard⟩

end Paper.Density.RationalDensityEndpoint

#print axioms Paper.Density.RationalDensityEndpoint.public_parameters
