import Paper.Optimality.Treewidth.SevenCliqueNineOrder
import Paper.Optimality.Treewidth.SevenCliqueSevenComponent
import Paper.Optimality.Treewidth.SevenCliqueGlobalReduction
namespace Paper.SevenCliqueTwentyTwoVertices
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem edge_bound (hG : G.IsKMinorFree 7) (hlo : 5 ≤ Fintype.card V)
    (hhi : Fintype.card V ≤ 22) : G.edgeFinset.card ≤ 5*Fintype.card V-15 := by
  classical
  by_contra hn
  have hdense : 5*Fintype.card V-14 ≤ G.edgeFinset.card := by omega
  obtain ⟨W,_,_,H,_,hm,hH,hW,he,hcn,hdeg,hminimal,hsep,hproper,v,hv,hcases⟩ :=
    SevenCliqueGlobalReduction.extract G hG hlo hdense
  have hWupper : Fintype.card W ≤ 22 := by
    obtain ⟨m⟩ := hm
    have hh := m.natCard_le
    have hcard : Fintype.card W ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hh
    omega
  have hmin : ∀ z, H.degree v ≤ H.degree z := by
    intro z
    rw [hv]
    exact H.minDegree_le_degree z
  have hlarge : 23 ≤ Fintype.card W := by
    rcases hcases with h8 | h9
    · exact SevenCliqueSevenComponent.order_twenty_three H hH v h8 hmin (hcn v) (hproper v) hsep
    · have hh := SevenCliqueNineOrder.order_twenty_eight H v h9 hmin he
      omega
  omega
end Paper.SevenCliqueTwentyTwoVertices



