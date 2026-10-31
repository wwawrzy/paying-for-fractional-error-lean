import Paper.Preliminaries.Incidence

/-! Whole-graph selection at noninteger critical density. The two integer
degree thresholds are k+1 and k+2; the coordinate threshold is independent. -/
namespace Paper.NoncriticalGeometry
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (σ : ℝ) (x : V → ℝ)

noncomputable def first : Finset V := Finset.univ.filter (fun v => k + 1 ≤ G.degree v ∧ σ < x v)
noncomputable def residual : Finset V := Finset.univ \ covered G (first G k σ x)
noncomputable def hits (v : V) : ℕ := (closed G v ∩ residual G k σ x).card
noncomputable def high : Finset V := (Finset.univ \ first G k σ x).filter (fun v => k + 2 ≤ hits G k σ x v)
noncomputable def low : Finset V := (Finset.univ \ first G k σ x).filter (fun v => hits G k σ x v ≤ k + 1)
noncomputable def last : Finset V := residual G k σ x \ covered G (high G k σ x)
noncomputable def output : Finset V := first G k σ x ∪ high G k σ x ∪ last G k σ x

theorem residual_disjoint_first : Disjoint (residual G k σ x) (first G k σ x) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hw)

theorem high_disjoint_first : Disjoint (high G k σ x) (first G k σ x) := by
  exact Finset.disjoint_left.mpr (fun _ hv hw => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2 hw)

theorem last_subset_residual : last G k σ x ⊆ residual G k σ x := Finset.sdiff_subset

theorem last_disjoint_high : Disjoint (last G k σ x) (high G k σ x) := by
  apply Finset.disjoint_left.mpr
  intro v hv hh
  exact (Finset.mem_sdiff.mp hv).2 (subset_covered G _ hh)

theorem first_hits_zero {v : V} (hv : v ∈ first G k σ x) : hits G k σ x v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hr).2).2
    (Finset.mem_biUnion.mpr ⟨v, hv, (Finset.mem_inter.mp hr).1⟩)

theorem hits_le_degree_succ (v : V) : hits G k σ x v ≤ G.degree v + 1 := by
  have h := Finset.card_le_card (Finset.inter_subset_left :
    closed G v ∩ residual G k σ x ⊆ closed G v)
  have he : (closed G v).card = G.degree v + 1 := by
    have heq : closed G v = insert v (G.neighborFinset v) := by
      ext u
      simp [mem_closed, SimpleGraph.mem_neighborFinset]
    rw [heq, Finset.card_insert_of_notMem (by simp)]
    rfl
  exact h.trans_eq he

theorem high_degree {v : V} (hv : v ∈ high G k σ x) : k + 1 ≤ G.degree v := by
  have hh := (Finset.mem_filter.mp hv).2
  have hn := hits_le_degree_succ G k σ x v
  omega

theorem high_weight {v : V} (hv : v ∈ high G k σ x) : x v ≤ σ := by
  by_contra hn
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv).1).2
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, high_degree G k σ x hv, lt_of_not_ge hn⟩)

theorem first_mass_lower : σ * (first G k σ x).card ≤ ∑ v ∈ first G k σ x, x v := by
  calc
    _ = ∑ _v ∈ first G k σ x, σ := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun _ hv => le_of_lt (Finset.mem_filter.mp hv).2.2)

theorem output_dominates : dominates G (output G k σ x) := by
  have hW : first G k σ x ⊆ output G k σ x := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hH : high G k σ x ⊆ output G k σ x := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  intro v
  by_cases hw : v ∈ covered G (first G k σ x)
  · exact covered_mono G hW hw
  by_cases hh : v ∈ covered G (high G k σ x)
  · exact covered_mono G hH hh
  apply subset_covered G _
  exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, hh⟩)

end Paper.NoncriticalGeometry
