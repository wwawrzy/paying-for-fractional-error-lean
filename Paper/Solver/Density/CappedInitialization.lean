import Paper.Solver.Density.UnitDomination

/-! A positive initial dual packing from local closed-neighborhood sizes.
No maximum-degree bound is an input to the construction. The parameter Delta
appears only in the uniform lower-bound analysis. -/

namespace Paper.Density.CappedInitialization

open SevenFoundation
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The maximum closed-row size among the vertex's closed neighbors. -/
def denominator (v : V) : ℕ :=
  (closed G v).sup (fun u => (closed G u).card)

noncomputable def initial (cap : ℝ) (v : V) : ℝ :=
  min cap (1 / (denominator G v : ℝ))

theorem closed_card_pos (v : V) : 0 < (closed G v).card :=
  Finset.card_pos.mpr ⟨v, self_mem_closed G v⟩

/-- Symmetry makes every vertex in a row aware of that row's size. -/
theorem row_card_le_denominator {r v : V} (hv : v ∈ closed G r) :
    (closed G r).card ≤ denominator G v := by
  exact Finset.le_sup (s := closed G v) (f := fun u => (closed G u).card)
    ((closed_symm G v r).mp hv)

theorem denominator_pos (v : V) : 0 < denominator G v :=
  (closed_card_pos G v).trans_le (row_card_le_denominator G (self_mem_closed G v))

theorem initial_pos {cap : ℝ} (hcap : 0 < cap) (v : V) : 0 < initial G cap v := by
  have hd : (0 : ℝ) < denominator G v := by exact_mod_cast denominator_pos G v
  exact lt_min hcap (one_div_pos.mpr hd)

theorem initial_le_cap (cap : ℝ) (v : V) : initial G cap v ≤ cap := min_le_left _ _

theorem initial_le_row_reciprocal (cap : ℝ) {r v : V} (hv : v ∈ closed G r) :
    initial G cap v ≤ 1 / ((closed G r).card : ℝ) := by
  have hr : (0 : ℝ) < (closed G r).card := by exact_mod_cast closed_card_pos G r
  have hd : ((closed G r).card : ℝ) ≤ denominator G v := by
    exact_mod_cast row_card_le_denominator G hv
  exact (min_le_right _ _).trans (one_div_le_one_div_of_le hr hd)

/-- Every row has at most its cardinality times its reciprocal. -/
theorem initial_packing (cap : ℝ) (r : V) : UnitDomination.mass G (initial G cap) r ≤ 1 := by
  have hr : (0 : ℝ) < (closed G r).card := by exact_mod_cast closed_card_pos G r
  calc
    _ ≤ ∑ _v ∈ closed G r, 1 / ((closed G r).card : ℝ) :=
      Finset.sum_le_sum (fun _ hv => initial_le_row_reciprocal G cap hv)
    _ = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul, one_div]
      exact mul_inv_cancel₀ hr.ne'

/-- This degree bound is used only to analyze the locally computed denominator. -/
theorem denominator_le {Delta : ℕ} (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    denominator G v ≤ Delta + 1 := by
  apply Finset.sup_le
  intro u _
  rw [UnitDomination.occurrence_count]
  exact Nat.add_le_add_right (hdegree u) 1

/-- A uniform analysis bound for growth time; Delta is absent from initial. -/
theorem initial_lower_bound (cap : ℝ) {Delta : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Delta) (v : V) :
    min cap (1 / ((Delta : ℝ) + 1)) ≤ initial G cap v := by
  have hd : (0 : ℝ) < denominator G v := by exact_mod_cast denominator_pos G v
  have hu : (denominator G v : ℝ) ≤ (Delta : ℝ) + 1 := by
    exact_mod_cast denominator_le G hdegree v
  exact min_le_min le_rfl (one_div_le_one_div_of_le hd hu)

end Paper.Density.CappedInitialization

#print axioms Paper.Density.CappedInitialization.initial_pos
#print axioms Paper.Density.CappedInitialization.initial_le_cap
#print axioms Paper.Density.CappedInitialization.initial_packing
#print axioms Paper.Density.CappedInitialization.initial_lower_bound
