import Mathlib.Data.Finset.Union
/-! Feasibility of mixing covers along component labels.
This is a helper for `fv:imp:absorb`; exact-search and protocol bounds remain separate. -/

set_option maxHeartbeats 200000
namespace Paper.ComponentReplacement

theorem replacement_covers
    {V I : Type} [DecidableEq V]
    (C : V → Finset V) (R D0 D1 : Finset V)
    (component : V → I) (solved : I → Bool)
    (hlocal : ∀ r ∈ R, ∀ v ∈ C r, component v = component r)
    (hcover0 : ∀ r ∈ R, ∃ v ∈ D0, v ∈ C r)
    (hcover1 : ∀ r ∈ R, solved (component r) = true → ∃ v ∈ D1, v ∈ C r) :
    ∀ r ∈ R, ∃ v ∈ (D0 ∪ D1).filter
      (fun v => if solved (component v) then v ∈ D1 else v ∈ D0), v ∈ C r := by
  intro r hr
  by_cases h : solved (component r) = true
  · have hv := hcover1 r hr h
    rcases hv with ⟨v, hvD1, hvC⟩
    have hmem : v ∈ D0 ∪ D1 := Finset.mem_union_right D0 hvD1
    have hcomp := hlocal r hr v hvC
    have hsolvedv : solved (component v) = true := by rw [hcomp, h]
    refine ⟨v, ?_, hvC⟩
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    simp [hsolvedv, hvD1]
  · have hv := hcover0 r hr
    rcases hv with ⟨v, hvD0, hvC⟩
    have hcomp := hlocal r hr v hvC
    have hmem : v ∈ D0 ∪ D1 := Finset.mem_union_left D1 hvD0
    refine ⟨v, Finset.mem_filter.mpr ⟨hmem, ?_⟩, hvC⟩
    simp [hcomp, h, hvD0]

end Paper.ComponentReplacement

#print axioms Paper.ComponentReplacement.replacement_covers
