import Paper.Optimality.Treewidth.CliqueForcedExteriorContact
namespace Paper.CliqueTwoOutsideForced
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem forced (T : Finset V) (a z : V)
    (hdegree : G.inducedDegree a Tᶜ = 2)
    (hinner : (T.filter (fun y => G.Adj a y ∧ G.Adj z y)).card ≤ 3)
    (hcommon : 5 ≤ Fintype.card (G.commonNeighbors a z)) :
    ∀ q, q ∉ T → G.Adj a q → G.Adj q z := by
  classical
  intro q hq haq
  by_contra hn
  let I := T.filter (fun y => G.Adj a y ∧ G.Adj z y)
  let O := Tᶜ.filter (G.Adj a)
  let M := (G.commonNeighbors a z).toFinset
  have hqO : q ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hq,haq⟩
  have hsub : M ⊆ I ∪ O.erase q := by
    intro y hy
    obtain ⟨hay,hzy⟩ := Set.mem_toFinset.mp hy
    by_cases hyT : y ∈ T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyT,hay,hzy⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_erase.mpr
      refine ⟨?_,Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hyT,hay⟩⟩
      intro hyq
      subst y
      exact hn hzy.symm
  have hb := (Finset.card_le_card hsub).trans (Finset.card_union_le I (O.erase q))
  have hc : (O.erase q).card = 1 := by
    rw [Finset.card_erase_of_mem hqO]
    change G.inducedDegree a Tᶜ - 1 = 1
    omega
  have hM : M.card = Fintype.card (G.commonNeighbors a z) := by
    dsimp [M]
    simp only [Set.toFinset_card]
  change I.card ≤ 3 at hinner
  omega
theorem not_contact (T : Finset V) (x p z : V) (hx : x ∈ T) (hz : z ∈ T)
    (h7 : G.inducedDegree x T = 7) (hT : T.card = 8)
    (h6 : G.inducedDegree z T = 6) (hp : p ∉ T) (hxp : G.Adj x p)
    (hreg : G.inducedDegree z (G.neighborFinset x) = 5) : ¬G.Adj p z := by
  classical
  intro hpz
  have hzx : z ≠ x := by intro heq; subst z; omega
  have hxz := CliqueForcedExteriorContact.universal_inside G T x hx hT h7 z hz hzx
  let D := (T.filter (G.Adj z)).erase x
  have hxm : x ∈ T.filter (G.Adj z) := Finset.mem_filter.mpr ⟨hx,hxz.symm⟩
  have hD : D.card = 5 := by
    rw [Finset.card_erase_of_mem hxm]
    change G.inducedDegree z T - 1 = 5
    omega
  have hpD : p ∉ D := fun hh => hp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hh)).1
  have hsub : insert p D ⊆ (G.neighborFinset x).filter (G.Adj z) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hxp,hpz.symm⟩
    · obtain ⟨hyx,hy⟩ := Finset.mem_erase.mp hy
      obtain ⟨hyT,hzy⟩ := Finset.mem_filter.mp hy
      have hxy := CliqueForcedExteriorContact.universal_inside G T x hx hT h7 y hyT hyx
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hxy,hzy⟩
  have hb := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hpD,hD] at hb
  change 6 ≤ G.inducedDegree z (G.neighborFinset x) at hb
  omega
end Paper.CliqueTwoOutsideForced

