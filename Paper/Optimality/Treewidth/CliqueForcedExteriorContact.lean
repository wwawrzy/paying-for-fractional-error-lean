import Paper.Optimality.Treewidth.SevenCliqueTwentySixClassification
namespace Paper.CliqueForcedExteriorContact
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem forced (T : Finset V) (x p z : V) (hx : x ∈ T) (hxz : G.Adj x z)
    (hunique : ∀ y, y ∉ T → G.Adj x y → y = p)
    (hz : G.inducedDegree z T = 5)
    (hcn : 5 ≤ Fintype.card (G.commonNeighbors x z)) : G.Adj p z := by
  classical
  by_contra hn
  let N := (G.commonNeighbors x z).toFinset
  have hsub : N ⊆ (T.filter (G.Adj z)).erase x := by
    intro y hy
    have hh := Set.mem_toFinset.mp hy
    obtain ⟨hxy,hzy⟩ := hh
    have hyT : y ∈ T := by
      by_contra hyT
      have hyp := hunique y hyT hxy
      subst y
      exact hn hzy.symm
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_filter.mpr ⟨hyT,hzy⟩⟩
    intro hyx
    subst y
    exact G.irrefl hxy
  have hxm : x ∈ T.filter (G.Adj z) := Finset.mem_filter.mpr ⟨hx,hxz.symm⟩
  have hbound := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hxm] at hbound
  change N.card ≤ G.inducedDegree z T - 1 at hbound
  rw [hz] at hbound
  have hN : N.card = Fintype.card (G.commonNeighbors x z) := by
    dsimp [N]
    simp only [Set.toFinset_card]
  omega
theorem universal_inside (T : Finset V) (x : V) (hx : x ∈ T)
    (hT : T.card = 8) (hd : G.inducedDegree x T = 7) :
    ∀ z ∈ T, z ≠ x → G.Adj x z := by
  classical
  have hsub : T.filter (G.Adj x) ⊆ T.erase x := by
    intro z hz
    obtain ⟨hz,hxz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_erase.mpr ⟨fun h => G.irrefl (h ▸ hxz),hz⟩
  have heq : T.filter (G.Adj x) = T.erase x := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_erase_of_mem hx,hT]
    change 7 ≤ G.inducedDegree x T
    omega
  intro z hz hzx
  have hm : z ∈ T.filter (G.Adj x) := heq.symm ▸ Finset.mem_erase.mpr ⟨hzx,hz⟩
  exact (Finset.mem_filter.mp hm).2
end Paper.CliqueForcedExteriorContact
