import Mathlib

/-! Actual finite separated centers for fv:hg:dilute. The maximal set is
constructed by maximizing cardinality over all separated finite subsets. -/
namespace Paper.HighGirthCenters
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def Separated (G : SimpleGraph V) (r : Nat) (C : Finset V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, u ≠ v → 2*r < G.dist u v

theorem exists_centers (G : SimpleGraph V) (r : Nat) :
    ∃ C : Finset V, Separated G r C ∧ ∀ v, ∃ c ∈ C, G.dist v c ≤ 2*r := by
  classical
  let family := Finset.univ.powerset.filter (Separated G r)
  have hfamily : family.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [family, Separated]
  obtain ⟨C,hC,hmax⟩ := Finset.exists_max_image family Finset.card hfamily
  have hsep : Separated G r C := (Finset.mem_filter.mp hC).2
  refine ⟨C,hsep,?_⟩
  intro v
  by_contra hnone
  have hfar : ∀ c ∈ C, 2*r < G.dist v c := by
    intro c hc
    exact Nat.lt_of_not_ge (fun h => hnone ⟨c,hc,h⟩)
  have hv : v ∉ C := by
    intro hv
    have h := hfar v hv
    simpa using h
  have hins : Separated G r (insert v C) := by
    intro u hu w hw hne
    rcases Finset.mem_insert.mp hu with heq | huC
    · subst u
      rcases Finset.mem_insert.mp hw with heq | hwC
      · exact False.elim (hne heq.symm)
      · exact hfar w hwC
    · rcases Finset.mem_insert.mp hw with heq | hwC
      · subst w
        simpa only [SimpleGraph.dist_comm] using hfar u huC
      · exact hsep u huC w hwC hne

  have hbig := hmax (insert v C) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hins⟩)
  rw [Finset.card_insert_of_notMem hv] at hbig
  omega

theorem centers_nonempty [Nonempty V] (G : SimpleGraph V) (r : Nat) (C : Finset V)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ 2*r) : C.Nonempty := by
  obtain ⟨c,hc,_⟩ := hcover (Classical.arbitrary V)
  exact ⟨c,hc⟩

end Paper.HighGirthCenters
#print axioms Paper.HighGirthCenters.exists_centers
#print axioms Paper.HighGirthCenters.centers_nonempty
