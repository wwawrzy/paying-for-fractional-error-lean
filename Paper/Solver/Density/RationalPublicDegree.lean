import Paper.Solver.Density.RationalApproximation

/-! Explicit public degree parameters for the bounded-degree solver.
The supplied global degree bound is a genuine extra premise of this
intermediate endpoint and is not inferred as local input knowledge. -/
namespace Paper.Density.RationalPublicDegree
open BroadcastModel RationalRuntime RationalRequirementDecay RationalEpochDecay
open RationalParameters RationalFeasibility RationalApproximation SevenFoundation
open scoped BigOperators

def index (m Δ : ℕ) : ℕ := m * Nat.clog 2 (Δ + 2)

theorem index_ge {m : ℕ} (hm : 1 ≤ m) (Δ : ℕ) : m ≤ index m Δ := by
  have hn : 0 < Nat.clog 2 (Δ + 2) := Nat.clog_pos (by omega) (by omega)
  unfold index
  nlinarith

theorem scale_pow_m {m : ℕ} (hm : 1 ≤ m) : (2 : ℚ) ≤ scale m ^ m := by
  have hp : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
  have he : 1 + 1 / (m : ℚ) = scale m := by unfold scale; push_cast; field_simp
  have hb := one_add_mul_le_pow (by
    have hr : (0 : ℚ) ≤ 1 / (m : ℚ) := by positivity
    linarith : (-2 : ℚ) ≤ 1 / (m : ℚ)) m
  rw [he] at hb
  have hleft : 1 + (m : ℚ) * (1 / (m : ℚ)) = 2 := by field_simp <;> norm_num
  linarith

theorem virtual_bound {m : ℕ} (hm : 1 ≤ m) (Δ : ℕ) :
    ((Δ + 2 : ℕ) : ℚ) ≤ threshold m (index m Δ : ℤ) := by
  change ((Δ + 2 : ℕ) : ℚ) ≤ scale m ^ (index m Δ : ℤ)
  rw [zpow_natCast]
  calc
    _ ≤ (2 : ℚ) ^ Nat.clog 2 (Δ + 2) := by
      exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (Δ + 2)
    _ ≤ (scale m ^ m) ^ Nat.clog 2 (Δ + 2) :=
      pow_le_pow_left₀ (by norm_num) (scale_pow_m hm) _
    _ = _ := by rw [← pow_mul]; rfl

theorem index_add_one (m Δ : ℕ) : index m Δ + 1 ≤ (m + 1) * Nat.clog 2 (Δ + 2) := by
  have hn : 0 < Nat.clog 2 (Δ + 2) := Nat.clog_pos (by omega) (by omega)
  unfold index
  nlinarith

theorem rounds_log_squared {V : Type} [DecidableEq V] (m Δ : ℕ) :
    (program (V := V) m (index m Δ)).rounds ≤
      4 * m * (m + 1) ^ 3 * (Nat.clog 2 (Δ + 2)) ^ 2 := by
  calc
    _ ≤ 4 * m * (m + 1) * (index m Δ + 1) ^ 2 := rounds_quadratic m (index m Δ)
    _ ≤ 4 * m * (m + 1) * ((m + 1) * Nat.clog 2 (Δ + 2)) ^ 2 := by
      gcongr
      exact index_add_one m Δ
    _ = _ := by ring

theorem messages_log_degree {V : Type} [DecidableEq V] (m Δ : ℕ) :
    (program (V := V) m (index m Δ)).maxBits ≤
      (2 * Nat.clog 2 (m + 2) + 5) * (m + 1) * Nat.clog 2 (Δ + 2) := by
  calc
    _ ≤ messageBound m (index m Δ) := maxBits m (index m Δ)
    _ ≤ (2 * Nat.clog 2 (m + 2) + 5) * (index m Δ + 1) := message_linear m (index m Δ)
    _ ≤ (2 * Nat.clog 2 (m + 2) + 5) * ((m + 1) * Nat.clog 2 (Δ + 2)) :=
      Nat.mul_le_mul_left _ (index_add_one m Δ)
    _ = _ := by ring

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed_bound {m Δ : ℕ} (hm : 1 ≤ m) (hdegree : ∀ v, G.degree v ≤ Δ) (v : V) :
    ((closed G v).card : ℝ) ≤ (threshold m (index m Δ : ℤ) : ℝ) := by
  have hc : (closed G v).card ≤ Δ + 2 := by rw [UnitDomination.occurrence_count]; have h := hdegree v; omega
  have hcR : ((closed G v).card : ℝ) ≤ ((Δ + 2 : ℕ) : ℝ) := by exact_mod_cast hc
  have hvR : ((Δ + 2 : ℕ) : ℝ) ≤ (threshold m (index m Δ : ℤ) : ℝ) := by
    exact_mod_cast virtual_bound hm Δ
  exact hcR.trans hvR

theorem bounded_degree_solver {m Δ : ℕ} (hm : 1 ≤ m) {δ : ℝ}
    (haccuracy : (1 + 1 / (m : ℝ)) ^ 5 ≤ 1 + δ) (hdegree : ∀ v, G.degree v ≤ Δ) :
    feasible (ordinary G) (output G m (index m Δ)) ∧
      ∀ z : V → ℝ, feasible (ordinary G) z →
        (∑ v, output G m (index m Δ) v) ≤ (1 + δ) * ∑ v, z v := by
  have hk := index_ge hm Δ
  have hclosed := closed_bound G hm hdegree
  exact ⟨RationalFeasibility.ordinary_feasible G hm (by omega) hclosed,
    fun z hz => near_optimal G hm hk haccuracy hclosed z hz⟩

/-- Accuracy is chosen before the vertex type, degree parameter, and graph.
The remaining global degree knowledge is explicit in the public parameter. -/
theorem public_parameters (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, 1 ≤ m ∧
      ∀ (W : Type) (hWf : Fintype W) (hWeq : DecidableEq W) (Δ : ℕ)
        (H : SimpleGraph W) (hH : DecidableRel H.Adj),
        letI := hWf
        letI := hWeq
        letI := hH
        (∀ v, H.degree v ≤ Δ) →
          feasible (ordinary H) (output H m (index m Δ)) ∧
            ∀ z : W → ℝ, feasible (ordinary H) z →
              (∑ v, output H m (index m Δ) v) ≤ (1 + δ) * ∑ v, z v := by
  obtain ⟨m, hm, haccuracy⟩ := public_accuracy δ hδ
  refine ⟨m, hm, ?_⟩
  intro W hWf hWeq Δ H hH
  letI := hWf
  letI := hWeq
  letI := hH
  intro hd
  exact bounded_degree_solver H hm haccuracy hd

end Paper.Density.RationalPublicDegree

#print axioms Paper.Density.RationalPublicDegree.virtual_bound
#print axioms Paper.Density.RationalPublicDegree.rounds_log_squared
#print axioms Paper.Density.RationalPublicDegree.messages_log_degree
#print axioms Paper.Density.RationalPublicDegree.bounded_degree_solver
#print axioms Paper.Density.RationalPublicDegree.public_parameters
