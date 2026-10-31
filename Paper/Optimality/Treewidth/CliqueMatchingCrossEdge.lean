import Paper.Optimality.Treewidth.CliqueFourMatchings

namespace Paper.CliqueMatchingCrossEdge
open SimpleGraph CliqueFourMatchings

theorem exists_edge (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj]
    (hd : ∀ x, 2 ≤ H.degree x) (k : Fin 3) :
    ∃ x ∈ part k false, ∃ y ∈ part k true, H.Adj x y := by
  classical
  have hnon : (part k false).Nonempty :=
    Finset.card_pos.mp (by rw [part_card]; decide)
  obtain ⟨x, hx⟩ := hnon
  by_contra hn
  have hsub : H.neighborFinset x ⊆ (part k false).erase x := by
    intro y hy
    have hxy : H.Adj x y := by simpa only [mem_neighborFinset] using hy
    have hyfalse : y ∈ part k false := by
      have hu : y ∈ part k false ∪ part k true := by
        rw [(part_partition k).2]
        exact Finset.mem_univ y
      rcases Finset.mem_union.mp hu with hl | hr
      · exact hl
      · exact False.elim (hn ⟨x, hx, y, hr, hxy⟩)
    exact Finset.mem_erase.mpr ⟨fun heq => H.loopless.irrefl x (heq ▸ hxy), hyfalse⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hx, part_card] at hh
  change H.degree x ≤ 2 - 1 at hh
  have hlo := hd x
  omega

end Paper.CliqueMatchingCrossEdge
#print axioms Paper.CliqueMatchingCrossEdge.exists_edge
