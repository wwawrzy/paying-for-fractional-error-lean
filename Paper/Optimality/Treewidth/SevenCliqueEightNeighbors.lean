import Paper.Optimality.Treewidth.CliqueEightMinFive
import Paper.Optimality.Treewidth.SevenCliqueExteriorDisconnected
namespace Paper.SevenCliqueEightNeighbors
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem exterior_not_connected (hG : G.IsKMinorFree 7)
    (v : V) (hv : G.degree v = 8) (hmin : ∀ z, G.degree v ≤ G.degree z)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w)) :
    ¬(G.induce (insert v (G.neighborSet v))ᶜ).Connected := by
  classical
  have hn : Fintype.card (G.neighborSet v) = 8 := by rw [G.card_neighborSet_eq_degree,hv]
  have hd : ∀ w : G.neighborSet v, 5 ≤ (G.induce (G.neighborSet v)).degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v 5 w (hcn w w.property)
  obtain ⟨p,q,hpq,⟨m⟩⟩ := CliqueEightMinFive.minor (G.induce (G.neighborSet v)) hn hd
  exact SevenCliqueExteriorDisconnected.not_connected hG v hmin p q hpq m
end Paper.SevenCliqueEightNeighbors
#print axioms Paper.SevenCliqueEightNeighbors.exterior_not_connected
