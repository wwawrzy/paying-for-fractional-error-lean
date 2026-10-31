import Paper.Solver.Density.RationalCappedProgram

/-! Composition endpoint for the executable unit-cost fractional solver.
The shared degree bound remains an explicit public parameter. Neither a
fractional solution nor an optimum vector is supplied as input. -/
namespace Paper.Density.RationalCappedEndpoint
open BroadcastModel RationalRuntime RationalCappedProgram RationalPublicDegree
open RationalParameters SevenFoundation
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cost_fractionalNumber {m Δ : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ)
    (hdegree : ∀ v, G.degree v ≤ Δ) :
    (∑ v, decoded G m (index m Δ) v) ≤ (1 + δ) * fractionalNumber G := by
  have ha : (0 : ℝ) < 1 + δ := by linarith
  have hlow : (∑ v, decoded G m (index m Δ) v) / (1 + δ) ≤ fractionalNumber G := by
    apply le_csInf (feasibleCosts_nonempty G)
    rintro t ⟨z, hz, rfl⟩
    apply (div_le_iff₀ ha).2
    rw [ordinary_cost]
    simpa only [mul_comm] using decoded_near_optimal G hm (index_ge hm Δ)
      haccuracy (closed_bound G hm hdegree) z hz
  simpa only [mul_comm] using (div_le_iff₀ ha).mp hlow

theorem bounded_degree_endpoint {m Δ : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ)
    (hdegree : ∀ v, G.degree v ≤ Δ) :
    0 < commonDenominator m (index m Δ) ∧
      feasible (ordinary G) (decoded G m (index m Δ)) ∧
      (∀ v, decoded G m (index m Δ) v ≤ 1) ∧
      (∑ v, decoded G m (index m Δ) v) ≤ (1 + δ) * fractionalNumber G ∧
      (RationalCappedProgram.program (V := V) m (index m Δ)).rounds ≤
        4 * m * (m + 1) ^ 3 * (Nat.clog 2 (Δ + 2)) ^ 2 ∧
      (RationalCappedProgram.program (V := V) m (index m Δ)).maxBits ≤
        (2 * Nat.clog 2 (m + 2) + 5) * (m + 1) * Nat.clog 2 (Δ + 2) := by
  have hK := index_ge hm Δ
  refine ⟨commonDenominator_pos hm,
    decoded_feasible G hm (by omega) (closed_bound G hm hdegree),
    decoded_le_one G hm, cost_fractionalNumber G hm hδ haccuracy hdegree, ?_, ?_⟩
  · rw [rounds_eq]
    exact rounds_log_squared m Δ
  · rw [bits_eq]
    exact messages_log_degree m Δ

/-- The accuracy choice precedes the vertex type, graph and public degree bound.
The executable program has only `PUnit` vertex input and returns a bounded
integer numerator at `commonDenominator m (index m Δ)`. -/
theorem public_parameters (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∀ (W : Type) (hWf : Fintype W) (hWeq : DecidableEq W) (Δ : ℕ)
        (H : SimpleGraph W) (hH : DecidableRel H.Adj),
        letI := hWf
        letI := hWeq
        letI := hH
        (∀ v, H.degree v ≤ Δ) →
          0 < commonDenominator m (index m Δ) ∧
            feasible (ordinary H) (decoded H m (index m Δ)) ∧
            (∀ v, decoded H m (index m Δ) v ≤ 1) ∧
            (∑ v, decoded H m (index m Δ) v) ≤ (1 + δ) * fractionalNumber H ∧
            (RationalCappedProgram.program (V := W) m (index m Δ)).rounds ≤
              4 * m * (m + 1) ^ 3 * (Nat.clog 2 (Δ + 2)) ^ 2 ∧
            (RationalCappedProgram.program (V := W) m (index m Δ)).maxBits ≤
              (2 * Nat.clog 2 (m + 2) + 5) * (m + 1) * Nat.clog 2 (Δ + 2) := by
  obtain ⟨m, hm, hacc⟩ := public_accuracy δ hδ
  refine ⟨m, hm, ?_⟩
  intro W hWf hWeq Δ H hH
  letI := hWf
  letI := hWeq
  letI := hH
  exact fun hd => bounded_degree_endpoint H hm hδ hacc hd

end Paper.Density.RationalCappedEndpoint

#print axioms Paper.Density.RationalCappedEndpoint.cost_fractionalNumber
#print axioms Paper.Density.RationalCappedEndpoint.bounded_degree_endpoint
#print axioms Paper.Density.RationalCappedEndpoint.public_parameters
