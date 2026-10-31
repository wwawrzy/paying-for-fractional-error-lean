import Paper.Endpoints.Girth.HighGirthSpanningPath
set_option maxHeartbeats 200000
namespace Paper.HighGirthPathEdges

theorem spanning_path_extra_edges
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : ∀ z, G.degree z ≤ 2)
    (u v : V) (p : G.Walk u v) (hp : p.IsPath) (hspan : ∀ z : V, z ∈ p.support) :
    ∀ a b, G.Adj a b → p.toSubgraph.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  classical
    have hinternal : ∀ z ∈ p.support, z ≠ u → z ≠ v → ∀ y, G.Adj z y → p.toSubgraph.Adj z y := by
      intro z hz hzu hzv y hzy
      obtain ⟨i, hiz, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
      have hi0 : i ≠ 0 := by
        intro heq
        subst i
        exact hzu (by simpa using hiz.symm)
      have hilt : i < p.length := by
        by_contra hn
        have heq : i = p.length := by omega
        subst i
        exact hzv (by simpa using hiz.symm)
      have hnz : (p.toSubgraph.neighborSet z).ncard = 2 := by
        simpa only [hiz] using hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      have hzdeg : (G.neighborSet z).ncard ≤ 2 := by
        rw [Set.ncard_eq_toFinset_card']
        simpa using hd z
      have heq : p.toSubgraph.neighborSet z = G.neighborSet z :=
        Set.eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset z) (by omega)
      have hy : y ∈ p.toSubgraph.neighborSet z := heq.symm ▸ hzy
      exact hy
    intro a b hab
    by_cases ha : a = u ∨ a = v
    · by_cases hb : b = u ∨ b = v
      · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact False.elim (hab.ne rfl)
        · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
        · exact Or.inr (Or.inr ⟨rfl,rfl⟩)
        · exact False.elim (hab.ne rfl)
      · left
        exact (hinternal b (hspan b) (fun h => hb (Or.inl h)) (fun h => hb (Or.inr h)) a hab.symm).symm
    · left
      exact hinternal a (hspan a) (fun h => ha (Or.inl h)) (fun h => ha (Or.inr h)) b hab

end Paper.HighGirthPathEdges

#print axioms Paper.HighGirthPathEdges.spanning_path_extra_edges
