import GraphTheory.SimpleGraph.Minor.ContractibleEdge

/-! The existing constructive three-connectivity contraction theorem gives
a genuine K4 minor. This will supply the irreducible case of elimination in
K4-minor-free graphs, rather than assuming their series-parallel structure. -/
namespace Paper.CliqueFourConnectivity

open SimpleGraph SimpleGraph.EdgeContraction

theorem of_three_connected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h3 : G.IsKConnected 3) :
    ¬ G.IsKMinorFree 4 := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = n →
      H.IsKConnected 3 → ¬ H.IsKMinorFree 4 by
    exact hh _ V G rfl h3
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H _ hcard hconn hfree
    by_cases he : Nonempty (H ≃g (⊤ : SimpleGraph (Fin 4)))
    · obtain ⟨e⟩ := he
      apply hfree
      refine ⟨{
        branchSet := fun i => {e.symm i}
        nonempty := fun i => Set.singleton_nonempty _
        disjoint := fun i j hij => by
          rw [Set.disjoint_singleton]
          exact fun hh => hij (e.symm.injective hh)
        connected := fun i => (MinorModel.refl H).connected _
        adjacent := fun i j hij =>
          ⟨e.symm i, rfl, e.symm j, rfl, e.symm.map_adj_iff.mpr hij⟩ }⟩
    · obtain ⟨u, v, huv, hcontr⟩ := IsKConnected.three_exists_contractible_edge H hconn he
      have hsmall : Fintype.card (ContrVertex u v) < n := by
        have hh := contrVertex_card_lt huv.ne
        omega
      exact ih _ hsmall (ContrVertex u v) (contrGraph H u v) rfl hcontr
        (IsHMinorFree.minor hfree (contrGraph_isMinor_of_adj H huv))

theorem not_three_connected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : G.IsKMinorFree 4) :
    ¬ G.IsKConnected 3 := fun h3 => of_three_connected G h3 hfree

end Paper.CliqueFourConnectivity

#print axioms Paper.CliqueFourConnectivity.of_three_connected
#print axioms Paper.CliqueFourConnectivity.not_three_connected
