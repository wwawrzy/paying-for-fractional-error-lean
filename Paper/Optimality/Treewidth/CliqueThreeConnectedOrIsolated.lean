import Paper.Optimality.Treewidth.CliqueEightFiveClique
namespace Paper.CliqueThreeConnectedOrIsolated
open SimpleGraph
theorem fin_three (H : SimpleGraph (Fin 3)) :
    H.Connected ∨ ∃ x, ∀ y, ¬H.Adj x y := by
  classical
  by_cases h01 : H.Adj 0 1 <;> by_cases h02 : H.Adj 0 2 <;> by_cases h12 : H.Adj 1 2
  all_goals solve
    | (left
       rw [connected_iff_exists_forall_reachable]
       refine ⟨0,?_⟩
       intro y
       fin_cases y
       · exact Reachable.refl _
       · first | exact h01.reachable | exact h02.reachable.trans h12.symm.reachable
       · first | exact h02.reachable | exact h01.reachable.trans h12.reachable)
    | (right; refine ⟨0,?_⟩; intro y; fin_cases y <;> first
        | exact H.irrefl
        | exact h01
        | exact h02
        | exact h12
        | exact fun h => h01 h.symm
        | exact fun h => h02 h.symm
        | exact fun h => h12 h.symm)
    | (right; refine ⟨1,?_⟩; intro y; fin_cases y <;> first
        | exact H.irrefl
        | exact h01
        | exact h02
        | exact h12
        | exact fun h => h01 h.symm
        | exact fun h => h02 h.symm
        | exact fun h => h12 h.symm)
    | (right; refine ⟨2,?_⟩; intro y; fin_cases y <;> first
        | exact H.irrefl
        | exact h01
        | exact h02
        | exact h12
        | exact fun h => h01 h.symm
        | exact fun h => h02 h.symm
        | exact fun h => h12 h.symm)

variable {V : Type} [Fintype V]
theorem of_card (H : SimpleGraph V) (hcard : Fintype.card V = 3) :
    H.Connected ∨ ∃ x, ∀ y, ¬H.Adj x y := by
  classical
  let e : Fin 3 ≃ V := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let J := H.comap e.toEmbedding
  rcases fin_three J with hc | ⟨x,hx⟩
  · left
    exact hc.map (Iso.comap e H).toHom (Iso.comap e H).surjective
  · right
    refine ⟨e x,?_⟩
    intro y hy
    apply hx (e.symm y)
    change H.Adj (e x) (e (e.symm y))
    simpa only [e.apply_symm_apply] using hy
end Paper.CliqueThreeConnectedOrIsolated
