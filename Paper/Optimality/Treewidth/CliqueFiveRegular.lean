import Paper.Optimality.Treewidth.CliqueFiveTrianglePartition

/-! A two-regular graph on five vertices has no triangle. -/
namespace Paper.CliqueFiveRegular
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem no_triangle (hV : Fintype.card V = 5) (hd : ∀ x, H.degree x = 2)
    (S : Finset V) (hS : S.card = 3) : ¬H.IsClique (S : Set V) := by
  intro hc
  have hR : Sᶜ.card = 2 := by rw [Finset.card_compl, hV, hS]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < Sᶜ.card by omega)
  have hsub : H.neighborFinset x ⊆ Sᶜ.erase x := by
    intro y hy
    have hxy := (H.mem_neighborFinset x y).mp hy
    refine Finset.mem_erase.mpr ⟨hxy.ne.symm, Finset.mem_compl.mpr ?_⟩
    intro hyS
    exact (Finset.mem_compl.mp hx)
      (CliqueEightComplement.triangle_closed H (fun z => (hd z).le) S hS hc y hyS x hxy.symm)
  have hb := Finset.card_le_card hsub
  rw [H.card_neighborFinset_eq_degree, hd, Finset.card_erase_of_mem hx, hR] at hb
  omega

theorem neighbors_nonadjacent (hV : Fintype.card V = 5) (hd : ∀ x, H.degree x = 2)
    (v a b : V) (hva : H.Adj v a) (hvb : H.Adj v b) (hab : a ≠ b) : ¬H.Adj a b := by
  intro hadj
  apply no_triangle H hV hd {v, a, b}
  · simp [hva.ne, hvb.ne, hab]
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first | exact False.elim (hxy rfl) | exact hva | exact hva.symm |
        exact hvb | exact hvb.symm | exact hadj | exact hadj.symm

theorem neighbor_partition (hV : Fintype.card V = 5) (hd : ∀ x, H.degree x = 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 2) (v : V) :
    (H.neighborFinset v).card = 2 ∧
      H.IsIndepSet ((H.neighborFinset v : Finset V) : Set V) ∧
      ((insert v (H.neighborFinset v))ᶜ : Finset V).card = 2 ∧
      H.IsClique (((insert v (H.neighborFinset v))ᶜ : Finset V) : Set V) := by
  refine ⟨?_, ?_, ?_, CliqueFiveNonneighbors.clique H hsmall v⟩
  · rw [H.card_neighborFinset_eq_degree, hd]
  · intro a ha b hb hab
    exact neighbors_nonadjacent H hV hd v a b
      ((H.mem_neighborFinset v a).mp ha) ((H.mem_neighborFinset v b).mp hb) hab
  · rw [Finset.card_compl, Finset.card_insert_of_notMem (H.notMem_neighborFinset_self v),
      H.card_neighborFinset_eq_degree, hd, hV]

end Paper.CliqueFiveRegular
#print axioms Paper.CliqueFiveRegular.no_triangle
#print axioms Paper.CliqueFiveRegular.neighbors_nonadjacent
#print axioms Paper.CliqueFiveRegular.neighbor_partition
