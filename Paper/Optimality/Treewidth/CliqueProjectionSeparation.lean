import Paper.Optimality.Treewidth.CliqueMinimalSeparation

/-! Two actual projections across a near-complete separator contradict
global affine minimality. Each side gains an edge and remains an actual
minor. The separator has at most two missing edges. -/
namespace Paper.CliqueProjectionSeparation

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem impossible
    (he : G.edgeFinset.card + 9 = 4 * Fintype.card V)
    (hd : ∀ v, 4 ≤ G.degree v)
    (hminimal : CliqueMinorMinimal.BelowThreshold G 4 9 4)
    (S : Finset V) (s : Separation G S)
    [Fintype s.left] [Fintype s.right] [Fintype (S : Set V)]
    (L : SimpleGraph s.left) [DecidableRel L.Adj]
    (R : SimpleGraph s.right) [DecidableRel R.Adj]
    (hLminor : L.IsMinor G) (hRminor : R.IsMinor G)
    (hLadd : (G.induce s.left).edgeFinset.card + 1 ≤ L.edgeFinset.card)
    (hRadd : (G.induce s.right).edgeFinset.card + 1 ≤ R.edgeFinset.card)
    (hmissing : S.card.choose 2 ≤ (G.induce (S : Set V)).edgeFinset.card + 2) : False := by
  classical
  have hL := hminimal s.left L hLminor (CliqueMinimalSeparation.left_floor G s hd) (by
    simpa only [Nat.card_eq_fintype_card] using Separation.card_left_lt G s)
  have hRfloor : 4 ≤ Fintype.card s.right := by
    have hh := CliqueMinimalSeparation.left_floor G (CliqueFourSeparation.flip G s) hd
    simpa only [Fintype.card_eq_nat_card] using hh
  have hR := hminimal s.right R hRminor hRfloor (by
      simpa only [Nat.card_eq_fintype_card] using Separation.card_right_lt G s)
  have hsum := CliqueSeparationCount.edge_sum G s
  have hvertices := CliqueSeparationCount.vertex_sum G s
  have hchoose := CliqueMinimalSeparation.choose_bound S.card
  omega

end Paper.CliqueProjectionSeparation

#print axioms Paper.CliqueProjectionSeparation.impossible
