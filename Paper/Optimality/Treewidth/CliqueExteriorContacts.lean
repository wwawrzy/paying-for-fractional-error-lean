import Paper.Optimality.Treewidth.CliqueNeighborhoodExterior

/-! A nonadjacent pair inside a least-degree neighborhood must have
contacts outside the closed neighborhood. Counting takes place on the
original vertex type, without relabeling or changing degree instances. -/
namespace Paper.CliqueExteriorContacts

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_contact (v x y : V) (hx : G.Adj v x) (hy : G.Adj v y)
    (hxy : x ≠ y) (hnot : ¬G.Adj x y) (hmin : G.degree v ≤ G.degree x) :
    ∃ z ∈ (insert v (G.neighborSet v))ᶜ, G.Adj x z := by
  classical
  by_contra hn
  push Not at hn
  have hinside : ∀ z, G.Adj x z → z ∈ insert v (G.neighborSet v) := by
    intro z hxz
    by_contra hz
    exact hn z hz hxz
  let C : Finset V := insert v (G.neighborFinset v)
  let S : Finset V := (C.erase x).erase y
  have hxC : x ∈ C := Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v x).mpr hx))
  have hyC : y ∈ C := Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v y).mpr hy))
  have hyErase : y ∈ C.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hyC⟩
  have hcard : S.card = G.degree v - 1 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem hyErase, Finset.card_erase_of_mem hxC]
    dsimp only [C]
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
      G.card_neighborFinset_eq_degree]
    omega
  have hsub : G.neighborFinset x ⊆ S := by
    intro z hz
    have hxz := (G.mem_neighborFinset x z).mp hz
    refine Finset.mem_erase.mpr ⟨fun hzy => hnot (hzy ▸ hxz), ?_⟩
    refine Finset.mem_erase.mpr ⟨fun hzx => G.loopless.irrefl x (hzx ▸ hxz), ?_⟩
    rcases hinside z hxz with hzv | hvz
    · exact Finset.mem_insert.mpr (Or.inl hzv)
    · exact Finset.mem_insert.mpr (Or.inr ((G.mem_neighborFinset v z).mpr hvz))
  have hcount := Finset.card_le_card hsub
  rw [G.card_neighborFinset_eq_degree, hcard] at hcount
  have hpos : 0 < (G.neighborFinset v).card :=
    Finset.card_pos.mpr ⟨x, (G.mem_neighborFinset v x).mpr hx⟩
  rw [G.card_neighborFinset_eq_degree] at hpos
  omega

end Paper.CliqueExteriorContacts

#print axioms Paper.CliqueExteriorContacts.exists_contact
