import Paper.Preliminaries.SevenFoundation

/-! The zero-one primal/dual pair for unit-cost domination. The primal and
dual copy of a vertex share the physical vertex; diagonal incidences are local. -/
namespace Paper.Density.UnitDomination
open SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def coefficient (r v : V) : ℕ := if v ∈ closed G r then 1 else 0

def mass (x : V → ℝ) (r : V) : ℝ := ∑ v ∈ closed G r, x v

theorem coefficient_self (v : V) : coefficient G v v = 1 := by
  simp only [coefficient, self_mem_closed, if_true]

theorem coefficient_transpose (r v : V) : coefficient G r v = coefficient G v r := by
  unfold coefficient
  simp only [closed_symm G v r]

theorem nonzero_coefficient (r v : V) :
    coefficient G r v ≠ 0 ↔ v = r ∨ G.Adj r v := by
  by_cases h : v = r <;> simp [coefficient, mem_closed, h]

theorem closed_eq_insert (r : V) : closed G r = insert r (G.neighborFinset r) := by
  ext v
  simp only [mem_closed, Finset.mem_insert, SimpleGraph.mem_neighborFinset]

theorem occurrence_count (r : V) : (closed G r).card = G.degree r + 1 := by
  rw [closed_eq_insert, Finset.card_insert_of_notMem]
  · rfl
  · simp

theorem unit_normalization (r : V) :
    (closed G r).Nonempty ∧ ∀ v ∈ closed G r, 1 ≤ coefficient G r v := by
  refine ⟨⟨r, self_mem_closed G r⟩, ?_⟩
  intro v hv
  simp only [coefficient, if_pos hv, le_refl]

/-- The matrix is symmetric, so the primal and dual occurrence bounds agree. -/
theorem transpose_sum (x y : V → ℝ) :
    (∑ r, y r * mass G x r) = ∑ v, x v * mass G y v := by
  calc
    _ = ∑ r, ∑ v, if v ∈ closed G r then y r * x v else 0 := by
      simp only [mass, Finset.mul_sum, ← Finset.sum_filter]
      simp
    _ = ∑ v, ∑ r, if v ∈ closed G r then y r * x v else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      have he (r : V) :
          (if v ∈ closed G r then y r * x v else 0) =
          (if r ∈ closed G v then x v * y r else 0) := by
        simp only [closed_symm G v r]
        split_ifs <;> ring
      simp_rw [he]
      simp only [mass, Finset.mul_sum, ← Finset.sum_filter]
      simp

/-- Weak duality needs no LP attainment or supplied solver. -/
theorem weak_duality (x y : V → ℝ)
    (hx : ∀ v, 0 ≤ x v) (hy : ∀ v, 0 ≤ y v)
    (hcover : ∀ r, 1 ≤ mass G x r) (hpack : ∀ v, mass G y v ≤ 1) :
    (∑ r, y r) ≤ ∑ v, x v := by
  calc
    _ ≤ ∑ r, y r * mass G x r := by
      apply Finset.sum_le_sum
      intro r _
      simpa using mul_le_mul_of_nonneg_left (hcover r) (hy r)
    _ = ∑ v, x v * mass G y v := transpose_sum G x y
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      simpa using mul_le_mul_of_nonneg_left (hpack v) (hx v)

theorem ordinary_feasible (x : V → ℝ) :
    feasible (ordinary G) x ↔ (∀ v, 0 ≤ x v) ∧ ∀ r, 1 ≤ mass G x r := by
  simp only [feasible, ordinary, Finset.mem_univ, not_true_eq_false,
    IsEmpty.forall_iff, implies_true, true_and, forall_true_left, mass]

end Paper.Density.UnitDomination

#print axioms Paper.Density.UnitDomination.occurrence_count
#print axioms Paper.Density.UnitDomination.transpose_sum
#print axioms Paper.Density.UnitDomination.weak_duality
#print axioms Paper.Density.UnitDomination.ordinary_feasible
