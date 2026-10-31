import Paper.Certificates.Counting.PartialOptimum

/-! Attainment of a finite LP for arbitrary nonempty covering sets. Capping gives a
compact feasible region; no optimum vector is assumed as an extra input. -/
namespace Paper.CoveringOptimum
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (C : V → Finset V)

def Feasible (R : Finset V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v

noncomputable def objective (c x : V → ℝ) : ℝ := ∑ v, c v * x v

noncomputable def cap (x : V → ℝ) (v : V) : ℝ := min 1 (x v)

theorem cap_feasible (R : Finset V) (x : V → ℝ) (hx : Feasible C R x) :
    Feasible C R (cap x) := by
  refine ⟨fun v => le_min zero_le_one (hx.1 v), ?_⟩
  intro r hr
  by_cases hbig : ∃ v ∈ C r, 1 ≤ x v
  · obtain ⟨v, hv, hlarge⟩ := hbig
    have hs := Finset.single_le_sum
      (fun u (_ : u ∈ C r) => le_min zero_le_one (hx.1 u)) hv
    simpa only [cap, min_eq_left hlarge] using hs
  · have heq : (∑ v ∈ C r, cap x v) = ∑ v ∈ C r, x v := by
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
  Set.Icc (fun _ => 0) (fun _ => 1) ∩ {x | ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v}

theorem compactFeasible_isCompact (R : Finset V) : IsCompact (compactFeasible C R) := by
  have hclosed : IsClosed {x : V → ℝ | ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v} := by
    have heq : {x : V → ℝ | ∀ r ∈ R, 1 ≤ ∑ v ∈ C r, x v} =
        ⋂ r, ⋂ (_ : r ∈ R), {x : V → ℝ | 1 ≤ ∑ v ∈ C r, x v} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro r
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const (by fun_prop)
  exact isCompact_Icc.inter_right hclosed

theorem compactFeasible_nonempty (R : Finset V)
    (hC : ∀ r ∈ R, (C r).Nonempty) : (compactFeasible C R).Nonempty := by
  refine ⟨fun _ => 1, ⟨?_, ?_⟩⟩
  · exact ⟨fun _ => zero_le_one, le_rfl⟩
  · intro r hr
    obtain ⟨v, hv⟩ := hC r hr
    simpa using (Finset.single_le_sum (fun _ (_ : _ ∈ C r) => (zero_le_one : (0 : ℝ) ≤ 1))
      hv)

/-- An optimum exists and is compared against every nonnegative feasible vector. -/
theorem exists_optimum (R : Finset V) (c : V → ℝ)
    (hC : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v, 0 ≤ c v) :
    ∃ x : V → ℝ, Feasible C R x ∧ (∀ v, x v ≤ 1) ∧
      ∀ y, Feasible C R y → objective c x ≤ objective c y := by
  have hcont : Continuous (objective c) := by unfold objective; fun_prop
  obtain ⟨x, hx, hmin⟩ := (compactFeasible_isCompact C R).exists_isMinOn
    (compactFeasible_nonempty C R hC) hcont.continuousOn
  refine ⟨x, ⟨(Set.mem_Icc.mp hx.1).1, hx.2⟩, (Set.mem_Icc.mp hx.1).2, ?_⟩
  intro y hy
  have hcap : cap y ∈ compactFeasible C R := by
    exact ⟨⟨(cap_feasible C R y hy).1, fun v => min_le_left 1 (y v)⟩,
      (cap_feasible C R y hy).2⟩
  exact (hmin hcap).trans (cap_cost_le c y hc)

noncomputable def values (R : Finset V) (c : V → ℝ) : Set ℝ :=
  {t | ∃ x, Feasible C R x ∧ objective c x = t}

noncomputable def number (R : Finset V) (c : V → ℝ) : ℝ := sInf (values C R c)

theorem exists_optimum_eq_number (R : Finset V) (c : V → ℝ)
    (hC : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v, 0 ≤ c v) :
    ∃ x : V → ℝ, Feasible C R x ∧ objective c x = number C R c := by
  obtain ⟨x, hx, _, hmin⟩ := exists_optimum C R c hC hc
  have hleast : IsLeast (values C R c) (objective c x) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact hmin y hy
  exact ⟨x, hx, hleast.csInf_eq.symm⟩
end Paper.CoveringOptimum
