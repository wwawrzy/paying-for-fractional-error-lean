import GraphTheory.SimpleGraph.Minor.Defs

/-! A full minimum-degree condition supplies an actual complete minor on the
same finite vertex set. This is used to discard the smallest neighborhood
in the next excluded-clique density reduction. -/
namespace Paper.CliqueDegree

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem complete_minor (h : ℕ) (hcard : Fintype.card V = h)
    (hdeg : ∀ v, h - 1 ≤ G.degree v) : (completeGraph (Fin h)).IsMinor G := by
  classical
  have hall (u v : V) (hne : u ≠ v) : G.Adj u v := by
    have hsub : G.neighborFinset u ⊆ (Finset.univ : Finset V).erase u := by
      intro w hw
      have ha := (G.mem_neighborFinset _ _).mp hw
      exact Finset.mem_erase.mpr ⟨ha.ne.symm, Finset.mem_univ _⟩
    have hcardle : ((Finset.univ : Finset V).erase u).card ≤ (G.neighborFinset u).card := by
      simpa only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        hcard, G.card_neighborFinset_eq_degree] using hdeg u
    have heq := Finset.eq_of_subset_of_card_le hsub hcardle
    apply (G.mem_neighborFinset _ _).mp
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  let e : Fin h ≃ V := (Fin.castOrderIso hcard.symm).toEquiv.trans (Fintype.equivFin V).symm
  refine ⟨{
    branchSet := fun i => {e i}
    nonempty := fun _ => Set.singleton_nonempty _
    disjoint := fun i j hij => by
      rw [Set.disjoint_singleton]
      exact fun he => hij (e.injective he)
    connected := fun i => (MinorModel.refl G).connected (e i)
    adjacent := fun i j hij =>
      ⟨e i, rfl, e j, rfl, hall (e i) (e j) (fun he => hij.ne (e.injective he))⟩ }⟩

end Paper.CliqueDegree

#print axioms Paper.CliqueDegree.complete_minor
