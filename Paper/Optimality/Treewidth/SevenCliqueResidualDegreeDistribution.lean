import Paper.Optimality.Treewidth.SevenCliqueTwentySixClassification
namespace Paper.CliqueResidualDegreeDistribution
open SimpleGraph
theorem template_counts (a b : Fin 5)
    (hp : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) :
    Fintype.card {x : Fin 8 // (CliqueEightResidualTemplates.graph a b).degree x = 5} = 5 ∧
    Fintype.card {x : Fin 8 // (CliqueEightResidualTemplates.graph a b).degree x = 6} = 2 ∧
    Fintype.card {x : Fin 8 // (CliqueEightResidualTemplates.graph a b).degree x = 7} = 1 := by
  rcases hp with h | h | h | h <;> rcases h with ⟨rfl,rfl⟩ <;> decide

theorem iso_count {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) (n : ℕ) :
    Fintype.card {x : V // G.degree x = n} = Fintype.card {y : W // H.degree y = n} := by
  classical
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv e.toEquiv (fun x => by change G.degree x = n ↔ H.degree (e x) = n; rw [e.degree_eq])
end Paper.CliqueResidualDegreeDistribution
namespace Paper.SevenCliqueTwentySixClassification
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem degree_distribution (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    let H := G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)
    Fintype.card {x // H.degree x = 5} = 5 ∧
    Fintype.card {x // H.degree x = 6} = 2 ∧
    Fintype.card {x // H.degree x = 7} = 1 := by
  classical
  obtain ⟨a,b,⟨e⟩,hp⟩ := component G hG horder hmin hcn hsep v hv8 C hsize
  have hh := CliqueResidualDegreeDistribution.template_counts a b hp
  simpa only [CliqueResidualDegreeDistribution.iso_count _ _ e] using hh
end Paper.SevenCliqueTwentySixClassification
