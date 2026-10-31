import Paper.Optimality.Treewidth.SevenCliqueTwentySixExclusion
namespace Paper.SevenCliqueTwentySixVertices
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem edge_bound (hG : G.IsKMinorFree 7) (hlo : 5 ≤ Fintype.card V)
    (hhi : Fintype.card V ≤ 26) : G.edgeFinset.card ≤ 5*Fintype.card V-15 := by
  classical
  by_contra hn
  have hdense : 5*Fintype.card V-14 ≤ G.edgeFinset.card := by omega
  obtain ⟨W,_,_,H,_,hm,hH,hW,he,hcn,hdeg,hminimal,hsep,hproper,v,hv,hcases⟩ :=
    SevenCliqueGlobalReduction.extract G hG hlo hdense
  have hWupper : Fintype.card W ≤ 26 := by
    obtain ⟨m⟩ := hm
    have hh := m.natCard_le
    have hcard : Fintype.card W ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hh
    omega
  have hmin : ∀ z, H.degree v ≤ H.degree z := by
    intro z
    rw [hv]
    exact H.minDegree_le_degree z
  rcases hcases with h8 | h9
  · have hlow := SevenCliqueTwentyFiveCore.order_twenty_six H hH v h8 hmin (hcn v) (hproper v) hsep he
    have horder : Fintype.card W = 26 := by omega
    obtain ⟨C,hC⟩ := SevenCliqueTwentySixNeighborhood.has_eight H hH v h8 hmin (hcn v) (hproper v) hsep horder
    exact SevenCliqueTwentySixExclusion.component_impossible H hH horder hdeg hcn hsep he hminimal v h8 C hC
  · have hh := SevenCliqueNineOrder.order_twenty_eight H v h9 hmin he
    omega
end Paper.SevenCliqueTwentySixVertices
