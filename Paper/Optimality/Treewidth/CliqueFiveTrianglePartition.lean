import Paper.Optimality.Treewidth.CliqueFiveNonneighbors

/-! The triangle case on five vertices is a disjoint triangle and edge. -/
namespace Paper.CliqueFiveTrianglePartition
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem complement_clique (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 2)
    (S : Finset V) (hS : S.card = 3) (hc : H.IsClique (S : Set V)) :
    H.IsClique ((Sᶜ : Finset V) : Set V) := by
  obtain ⟨d, hdS⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  intro x hx y hy hxy
  have hxS := Finset.mem_compl.mp hx
  have hyS := Finset.mem_compl.mp hy
  apply CliqueFiveNonneighbors.adjacent H hsmall d x y
  · exact fun h => hxS (h ▸ hdS)
  · exact fun h => hyS (h ▸ hdS)
  · exact hxy
  · exact fun h => hxS (CliqueEightComplement.triangle_closed H hd S hS hc d hdS x h)
  · exact fun h => hyS (CliqueEightComplement.triangle_closed H hd S hS hc d hdS y h)

theorem low_degree_partition (hV : Fintype.card V = 5) (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 2)
    (v : V) (hv : H.degree v ≤ 1) :
    ∃ S : Finset V, S.card = 3 ∧ H.IsClique (S : Set V) ∧ Sᶜ.card = 2 ∧
      H.IsClique ((Sᶜ : Finset V) : Set V) ∧
      (∀ x ∈ S, ∀ y ∈ Sᶜ, ¬H.Adj x y) := by
  obtain ⟨S, hS, hc⟩ := CliqueFiveNonneighbors.low_degree_triangle H hV hd hsmall v hv
  refine ⟨S, hS, hc, ?_, complement_clique H hd hsmall S hS hc, ?_⟩
  · rw [Finset.card_compl, hV, hS]
  · intro x hx y hy hxy
    exact (Finset.mem_compl.mp hy)
      (CliqueEightComplement.triangle_closed H hd S hS hc x hx y hxy)

end Paper.CliqueFiveTrianglePartition
#print axioms Paper.CliqueFiveTrianglePartition.complement_clique
#print axioms Paper.CliqueFiveTrianglePartition.low_degree_partition
