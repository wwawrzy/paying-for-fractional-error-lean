import Paper.Solver.Density.RationalCappedEndpoint
import Paper.Endpoints.Rounding.NoncriticalSelectionProgram
import Paper.Endpoints.Rounding.NoncriticalOptimum
import Paper.Endpoints.Rounding.NoncriticalRationalParameters
import Paper.Communication.EncodedProgram

/-! Actual composition of the public-degree fractional solver and the three
one-bit rounding rounds. Only induced density is used; no excluded minor or
fractional vector is supplied to the executable program. -/
namespace Paper.Density.RationalDensityRounding
open BroadcastModel SevenFoundation RationalCappedProgram RationalPublicDegree
open scoped BigOperators

variable {V : Type} [DecidableEq V]

def program (k t h m Δ : ℕ) : Program V PUnit Bool :=
  .seq (RationalCappedProgram.program m (index m Δ))
    (NoncriticalSelectionProgram.program k t h (commonDenominator m (index m Δ))
      (commonDenominator m (index m Δ) + 1))

theorem rounds (k t h m Δ : ℕ) :
    (program (V := V) k t h m Δ).rounds =
      (RationalCappedProgram.program (V := V) m (index m Δ)).rounds + 3 := rfl

theorem rounds_log_squared (k t h m Δ : ℕ) :
    (program (V := V) k t h m Δ).rounds ≤
      (4 * m * (m + 1) ^ 3 + 3) * (Nat.clog 2 (Δ + 2)) ^ 2 := by
  have hl : 1 ≤ Nat.clog 2 (Δ + 2) := Nat.clog_pos (by omega) (by omega)
  rw [rounds]
  have hr := RationalPublicDegree.rounds_log_squared (V := V) m Δ
  rw [← RationalCappedProgram.rounds_eq] at hr
  nlinarith

theorem messages_log_degree (k t h m Δ : ℕ) :
    (program (V := V) k t h m Δ).maxBits ≤
      ((2 * Nat.clog 2 (m + 2) + 5) * (m + 1) + 1) * Nat.clog 2 (Δ + 2) := by
  have hl : 1 ≤ Nat.clog 2 (Δ + 2) := Nat.clog_pos (by omega) (by omega)
  have hb := RationalPublicDegree.messages_log_degree (V := V) m Δ
  rw [← RationalCappedProgram.bits_eq] at hb
  change max (RationalCappedProgram.program (V := V) m (index m Δ)).maxBits 1 ≤ _
  apply max_le <;> nlinarith

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output (k t h m Δ : ℕ) : Finset V :=
  Finset.univ.filter (fun v => (program k t h m Δ).runEncoded G (fun _ => PUnit.unit) v)

theorem output_eq {m : ℕ} (hm : 1 ≤ m) (k t h Δ : ℕ) (ht : 0 < t)
    (σ : ℝ) (hratio : (h : ℝ) / t = σ) :
    output G k t h m Δ = NoncriticalGeometry.output G k σ (decoded G m (index m Δ)) := by
  unfold output
  rw [Program.runEncoded_eq_run]
  change Finset.univ.filter (fun v => (NoncriticalSelectionProgram.program k t h
    (commonDenominator m (index m Δ)) (commonDenominator m (index m Δ) + 1)).run G
      ((RationalCappedProgram.program m (index m Δ)).run G (fun _ => PUnit.unit)) v) = _
  rw [NoncriticalSelectionProgram.correct G k t h _ _ ht (commonDenominator_pos hm) σ hratio]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  rfl

theorem exact_bound {m : ℕ} (hm : 1 ≤ m) (a θ : ℝ) (ha : 1 ≤ a)
    (hθ : 0 < θ) (hθ1 : θ < 1) (k t h Δ : ℕ) (ht : 0 < t)
    (heq : 2 * a = k + θ)
    (hratio : (h : ℝ) / t = NoncriticalParameters.threshold a θ)
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤
      1 + NoncriticalParameters.gain θ / (2 * a + 1 - NoncriticalParameters.gain θ))
    (hdegree : ∀ v, G.degree v ≤ Δ) (hden : Incidence.InducedDensityBound G a) :
    dominates G (output G k t h m Δ) ∧
      ((output G k t h m Δ).card : ℝ) ≤ (2 * a + 1) * fractionalNumber G := by
  have hδ := (NoncriticalRounding.error_cancellation a θ ha hθ hθ1).1
  have hx := decoded_feasible G hm (by have := index_ge hm Δ; omega)
    (closed_bound G hm hdegree)
  have hmass := RationalCappedEndpoint.cost_fractionalNumber G hm hδ haccuracy hdegree
  rw [output_eq G hm k t h Δ ht _ hratio]
  exact NoncriticalOptimum.output_bound G a θ ha hθ hθ1 k heq hden _
    ((NoncriticalOptimum.feasible_iff G _).mpr hx) (decoded_le_one G hm) hmass

theorem messages_log_vertices (k t h m Δ : ℕ) (hΔ : Δ ≤ Fintype.card V) :
    (program (V := V) k t h m Δ).maxBits ≤
      ((2 * Nat.clog 2 (m + 2) + 5) * (m + 1) + 1) * Nat.clog 2 (Fintype.card V + 2) :=
  (messages_log_degree k t h m Δ).trans (Nat.mul_le_mul_left _
    (Nat.clog_mono_right 2 (by omega : Δ + 2 ≤ Fintype.card V + 2)))

end Paper.Density.RationalDensityRounding

#print axioms Paper.Density.RationalDensityRounding.rounds_log_squared
#print axioms Paper.Density.RationalDensityRounding.messages_log_degree
#print axioms Paper.Density.RationalDensityRounding.output_eq
#print axioms Paper.Density.RationalDensityRounding.exact_bound
#print axioms Paper.Density.RationalDensityRounding.messages_log_vertices
