import Paper.Optimality.Treewidth.CliqueEightFourClique
import Paper.Optimality.Treewidth.SevenCliqueExteriorDisconnected

/-! The verified eight-vertex witness applies to an actual least-degree
neighborhood in a K7-minor-free graph. No minor certificate is assumed. -/
namespace Paper.SevenCliqueEightFourClique
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exterior_not_connected (hG : G.IsKMinorFree 7)
    (v : V) (hv : G.degree v = 8) (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w))
    (S : Finset (G.neighborSet v)) (hcard : S.card = 4)
    (hclique : (G.induce (G.neighborSet v)).IsClique (S : Set (G.neighborSet v))) :
    ¬(G.induce (insert v (G.neighborSet v))ᶜ).Connected := by
  classical
  have hV : Fintype.card (G.neighborSet v) = 8 := by
    rw [G.card_neighborSet_eq_degree, hv]
  have hd : ∀ w : G.neighborSet v, 5 ≤ (G.induce (G.neighborSet v)).degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v 5 w (hcn w w.property)
  obtain ⟨p, q, hpq, ⟨m⟩⟩ := CliqueEightFourClique.unrestricted
    (G.induce (G.neighborSet v)) S hV hcard hd hclique
  exact SevenCliqueExteriorDisconnected.not_connected hG v hmin p q hpq m

end Paper.SevenCliqueEightFourClique
#print axioms Paper.SevenCliqueEightFourClique.exterior_not_connected
