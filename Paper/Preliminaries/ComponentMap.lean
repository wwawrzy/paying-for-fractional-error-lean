import Paper.Preliminaries.DeletionComponents

/-! The physical component of a vertex in an actual induced region. -/
namespace Paper.ComponentMap
attribute [local instance] Classical.propDecidable Classical.decEq
open DeletionComponents
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def part (S : Finset V) (v : V) : Finset V :=
  if hv : v ∈ S then
    physical G (Finset.univ \ S) ((deleted G (Finset.univ \ S)).connectedComponentMk
      ⟨v, by simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hv⟩)
  else ∅

theorem mem_self (S : Finset V) (v : V) (hv : v ∈ S) : v ∈ part G S v := by
  simp only [part, dif_pos hv]
  exact covers G _ (by simpa using hv)

theorem subset (S : Finset V) (v : V) : part G S v ⊆ S := by
  by_cases hv : v ∈ S
  · simp only [part, dif_pos hv]
    intro u hu
    have h := Finset.disjoint_left.mp (avoids G _ _) hu
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using h
  · simp only [part, dif_neg hv]
    exact Finset.empty_subset _

theorem connected (S : Finset V) (v : V) (hv : v ∈ S) :
    (G.induce (part G S v : Set V)).Connected := by
  have he : part G S v = physical G (Finset.univ \ S)
      ((deleted G (Finset.univ \ S)).connectedComponentMk ⟨v, by simpa using hv⟩) := dif_pos hv
  rw [he]
  exact DeletionComponents.connected G _ _

theorem eq_of_mem (S : Finset V) (u v : V) (hu : u ∈ part G S v) : part G S u = part G S v := by
  have huS := subset G S v hu
  have hvS : v ∈ S := by
    by_contra hn
    simp [part, hn] at hu
  simp only [part, dif_pos huS, dif_pos hvS] at hu ⊢
  obtain ⟨_, hC⟩ := (mem_physical G _ _ u).mp hu
  have he := (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hC
  exact congrArg (physical G _) he

theorem eq_of_adj (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (ha : G.Adj u v) :
    part G S u = part G S v := by
  apply eq_of_mem G S u v
  have hvp := mem_self G S v hv
  simp only [part, dif_pos hv] at hvp ⊢
  exact closed G _ _ hvp (by simpa using hu) ha.symm

theorem disjoint_or_eq (S : Finset V) (u v : V) :
    Disjoint (part G S u) (part G S v) ∨ part G S u = part G S v := by
  by_cases hd : Disjoint (part G S u) (part G S v)
  · exact Or.inl hd
  · right
    obtain ⟨w, hw⟩ := Finset.not_disjoint_iff.mp hd
    exact (eq_of_mem G S w u hw.1).symm.trans (eq_of_mem G S w v hw.2)
end Paper.ComponentMap
