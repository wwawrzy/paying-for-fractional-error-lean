import Paper.Solver.Density.RationalPublicDegree
import Paper.Certificates.Counting.CoveringOptimum

/-! The executable solver returns a capped integer numerator at a positive
public common denominator. Capping adds no rounds or messages. The public
degree parameter remains explicit. -/
namespace Paper.Density.RationalCappedProgram
open BroadcastModel RationalRuntime RationalEpochDecay RationalTermination RationalFeasibility
open RationalApproximation RationalPublicDegree SevenFoundation
open scoped BigOperators

def commonDenominator (m K : ℕ) : ℕ := denominator m K * target m K

theorem commonDenominator_pos {m K : ℕ} (hm : 1 ≤ m) : 0 < commonDenominator m K :=
  denominator_pos hm

variable {V : Type} [DecidableEq V]

def program (m K : ℕ) : Program V PUnit (Fin (commonDenominator m K + 1)) :=
  .seq (.local fun _ _ _ => initial m K)
    (.seq (outer m K (K + target m K))
      (.local fun _ _ s => ⟨min s.primal (commonDenominator m K),
        Nat.lt_succ_of_le (min_le_right _ _)⟩))

theorem rounds_eq (m K : ℕ) :
    (program (V := V) m K).rounds = (RationalRuntime.program (V := V) m K).rounds := rfl

theorem bits_eq (m K : ℕ) :
    (program (V := V) m K).maxBits = (RationalRuntime.program (V := V) m K).maxBits := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem numerator_eq (m K : ℕ) (v : V) :
    ((program m K).run G (fun _ => PUnit.unit) v).val =
      min (finalState G m K v).primal (commonDenominator m K) := rfl

noncomputable def decoded (m K : ℕ) (v : V) : ℝ :=
  (((program m K).run G (fun _ => PUnit.unit) v).val : ℝ) / commonDenominator m K

theorem decoded_eq_cap {m K : ℕ} (hm : 1 ≤ m) (v : V) :
    decoded G m K v = min 1 (output G m K v) := by
  have hD : (0 : ℝ) < commonDenominator m K := by exact_mod_cast commonDenominator_pos (K := K) hm
  unfold decoded
  rw [numerator_eq, Nat.cast_min, ← min_div_div_right hD.le, div_self hD.ne']
  rw [output_fraction]
  exact min_comm _ _

theorem decoded_le_one {m K : ℕ} (hm : 1 ≤ m) (v : V) : decoded G m K v ≤ 1 := by
  rw [decoded_eq_cap G hm]
  exact min_le_left _ _

theorem decoded_feasible {m K : ℕ} (hm : 1 ≤ m) (hk : 0 < K)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ)) :
    feasible (ordinary G) (decoded G m K) := by
  have hraw := RationalFeasibility.ordinary_feasible G hm hk hdegree
  have hp := (UnitDomination.ordinary_feasible G _).1 hraw
  have hLP : CoveringOptimum.Feasible (closed G) Finset.univ (output G m K) :=
    ⟨hp.1, fun r _ => hp.2 r⟩
  have hcap := CoveringOptimum.cap_feasible (closed G) Finset.univ (output G m K) hLP
  have he : decoded G m K = CoveringOptimum.cap (output G m K) :=
    funext (fun v => decoded_eq_cap G hm v)
  rw [he]
  exact (UnitDomination.ordinary_feasible G _).2 ⟨hcap.1, fun r => hcap.2 r (Finset.mem_univ r)⟩

theorem decoded_near_optimal {m K : ℕ} (hm : 1 ≤ m) (hK : m ≤ K) {δ : ℝ}
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ)
    (hdegree : ∀ v, ((closed G v).card : ℝ) ≤ (threshold m (K : ℤ) : ℝ))
    (z : V → ℝ) (hz : feasible (ordinary G) z) :
    (∑ v, decoded G m K v) ≤ (1 + δ) * ∑ v, z v := by
  have hc : (∑ v, decoded G m K v) ≤ ∑ v, output G m K v := by
    apply Finset.sum_le_sum
    intro v _
    rw [decoded_eq_cap G hm]
    exact min_le_right _ _
  exact hc.trans (near_optimal G hm hK haccuracy hdegree z hz)

theorem messages_log_vertices (m Δ : ℕ) (hΔ : Δ ≤ Fintype.card V) :
    (program (V := V) m (index m Δ)).maxBits ≤
      ((2 * Nat.clog 2 (m + 2) + 5) * (m + 1)) * Nat.clog 2 (Fintype.card V + 2) := by
  rw [bits_eq]
  exact (messages_log_degree m Δ).trans (Nat.mul_le_mul_left _
    (Nat.clog_mono_right 2 (by omega : Δ + 2 ≤ Fintype.card V + 2)))

end Paper.Density.RationalCappedProgram

#print axioms Paper.Density.RationalCappedProgram.decoded_eq_cap
#print axioms Paper.Density.RationalCappedProgram.decoded_feasible
#print axioms Paper.Density.RationalCappedProgram.decoded_near_optimal
#print axioms Paper.Density.RationalCappedProgram.messages_log_vertices
