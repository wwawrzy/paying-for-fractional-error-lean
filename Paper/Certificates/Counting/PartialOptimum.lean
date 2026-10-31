import Paper.Solver.LocalSearch.LocalFractional

/-! Attainment of the actual finite partial-domination LP. Capping gives a
compact feasible region; no optimum vector is assumed as an extra input. -/
namespace Paper.PartialOptimum
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Feasible (R : Finset V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v

noncomputable def objective (c x : V → ℝ) : ℝ := ∑ v, c v * x v

noncomputable def cap (x : V → ℝ) (v : V) : ℝ := min 1 (x v)

theorem cap_feasible (R : Finset V) (x : V → ℝ) (hx : Feasible G R x) :
    Feasible G R (cap x) := by
  refine ⟨fun v => le_min zero_le_one (hx.1 v), ?_⟩
  intro r hr
  by_cases hbig : ∃ v ∈ closed G r, 1 ≤ x v
  · obtain ⟨v, hv, hlarge⟩ := hbig
    have hs := Finset.single_le_sum
      (fun u (_ : u ∈ closed G r) => le_min zero_le_one (hx.1 u)) hv
    simpa only [cap, min_eq_left hlarge] using hs
  · have heq : (∑ v ∈ closed G r, cap x v) = ∑ v ∈ closed G r, x v := by
      apply Finset.sum_congr rfl
      intro v hv
      have hle : x v ≤ 1 := by
        by_contra hn
        exact hbig ⟨v, hv, le_of_lt (lt_of_not_ge hn)⟩
      exact min_eq_right hle
    rw [heq]
    exact hx.2 r hr

theorem cap_cost_le (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) : objective c (cap x) ≤ objective c x :=
  Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (min_le_right 1 (x v)) (hc v))

noncomputable def compactFeasible (R : Finset V) : Set (V → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => 1) ∩ {x | ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v}

theorem compactFeasible_isCompact (R : Finset V) : IsCompact (compactFeasible G R) := by
  have hclosed : IsClosed {x : V → ℝ | ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v} := by
    have heq : {x : V → ℝ | ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v} =
        ⋂ r, ⋂ (_ : r ∈ R), {x : V → ℝ | 1 ≤ ∑ v ∈ closed G r, x v} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro r
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const (by fun_prop)
  exact isCompact_Icc.inter_right hclosed

theorem compactFeasible_nonempty (R : Finset V) : (compactFeasible G R).Nonempty := by
  refine ⟨fun _ => 1, ⟨?_, ?_⟩⟩
  · exact ⟨fun _ => zero_le_one, le_rfl⟩
  · intro r _
    simpa using (Finset.single_le_sum (fun _ (_ : _ ∈ closed G r) => (zero_le_one : (0 : ℝ) ≤ 1))
      (self_mem_closed G r))

/-- An optimum exists and is compared against every nonnegative feasible vector. -/
theorem exists_optimum (R : Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ x : V → ℝ, Feasible G R x ∧ (∀ v, x v ≤ 1) ∧
      ∀ y, Feasible G R y → objective c x ≤ objective c y := by
  have hcont : Continuous (objective c) := by unfold objective; fun_prop
  obtain ⟨x, hx, hmin⟩ := (compactFeasible_isCompact G R).exists_isMinOn
    (compactFeasible_nonempty G R) hcont.continuousOn
  refine ⟨x, ⟨(Set.mem_Icc.mp hx.1).1, hx.2⟩, (Set.mem_Icc.mp hx.1).2, ?_⟩
  intro y hy
  have hcap : cap y ∈ compactFeasible G R := by
    exact ⟨⟨(cap_feasible G R y hy).1, fun v => min_le_left 1 (y v)⟩,
      (cap_feasible G R y hy).2⟩
  exact (hmin hcap).trans (cap_cost_le c y hc)

noncomputable def values (R : Finset V) (c : V → ℝ) : Set ℝ :=
  {t | ∃ x, Feasible G R x ∧ objective c x = t}

noncomputable def number (R : Finset V) (c : V → ℝ) : ℝ := sInf (values G R c)

theorem exists_optimum_eq_number (R : Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ x : V → ℝ, Feasible G R x ∧ objective c x = number G R c := by
  obtain ⟨x, hx, _, hmin⟩ := exists_optimum G R c hc
  have hleast : IsLeast (values G R c) (objective c x) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact hmin y hy
  exact ⟨x, hx, hleast.csInf_eq.symm⟩
end Paper.PartialOptimum
