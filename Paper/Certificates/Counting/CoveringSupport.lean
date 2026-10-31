import Paper.Certificates.Counting.CoveringOptimum

/-! Removing inadmissible coordinates preserves the general covering LP. -/
namespace Paper.CoveringSupport
open scoped BigOperators
open CoveringOptimum
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (C : V → Finset V) (R : Finset V)

def admissible : Finset V := R.biUnion C

noncomputable def project (x : V → ℝ) (v : V) : ℝ :=
  if v ∈ admissible C R then x v else 0

theorem project_feasible (x : V → ℝ) (hx : Feasible C R x) :
    Feasible C R (project C R x) := by
  refine ⟨?_, ?_⟩
  · intro v
    unfold project
    split_ifs
    · exact hx.1 v
    · exact le_rfl
  · intro r hr
    have he : (∑ v ∈ C r, project C R x v) = ∑ v ∈ C r, x v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact if_pos (Finset.mem_biUnion.mpr ⟨r, hr, hv⟩)
    rw [he]
    exact hx.2 r hr

theorem project_cost_le (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hx : ∀ v, 0 ≤ x v) : objective c (project C R x) ≤ objective c x := by
  apply Finset.sum_le_sum
  intro v _
  unfold project
  split_ifs
  · exact le_rfl
  · simpa using mul_nonneg (hc v) (hx v)

/-- An optimum can be supported exactly on admissible candidates, with all
coordinates at most one. No optimum or feasibility vector is assumed. -/
theorem exists_supported_optimum (c : V → ℝ)
    (hC : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v, 0 ≤ c v) :
    ∃ x : V → ℝ, Feasible C R x ∧ (∀ v, x v ≤ 1) ∧
      (∀ v ∉ admissible C R, x v = 0) ∧
      objective c x = number C R c := by
  obtain ⟨y, hy, hcap, hmin⟩ := exists_optimum C R c hC hc
  let x := project C R y
  have hx := project_feasible C R y hy
  have he : objective c x = objective c y :=
    le_antisymm (project_cost_le C R c y hc hy.1) (hmin x hx)
  have hl : IsLeast (values C R c) (objective c y) := by
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact hmin z hz
  refine ⟨x, hx, ?_, ?_, he.trans hl.csInf_eq.symm⟩
  · intro v
    dsimp [x, project]
    split_ifs
    · exact hcap v
    · exact zero_le_one
  · intro v hv
    exact if_neg hv

end Paper.CoveringSupport
