import Paper.Optimality.Treewidth.CliqueEightActualTemplate
namespace Paper.SevenCliqueTwentySixClassification
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem component (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    let H := G.induce ((vertices (outside G (insert v (G.neighborSet v)) C)) : Set V)
    ∃ a b : Fin 5, Nonempty (H ≃g CliqueEightResidualTemplates.graph a b) ∧
      ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)) := by
  classical
  let T := vertices (outside G (insert v (G.neighborSet v)) C)
  let H := G.induce (T : Set V)
  have hcard : Fintype.card (T : Set V) = 8 := by
    simpa only [Fintype.card_eq_nat_card,Finset.coe_sort_coe,Nat.card_eq_finsetCard] using hsize
  have hm : ∀ z, G.degree v ≤ G.degree z := by intro z; rw [hv8]; exact hmin z
  have hf := SevenCliqueEightComponent.small_component_free G hG v hv8 hm C (by omega)
  have he := SevenCliqueEightExact.component_edges G hG v hv8 hm (hcn v) C hsize
  have hlow : ∀ x, 5 ≤ H.degree x := by
    intro x
    rw [InducedCounting.degree_induce_eq_inducedDegree G T x]
    exact SevenCliqueTwentySixInterior.five_le G hG horder hmin hcn hsep v hv8 C hsize x.val x.property
  obtain ⟨u,hu,hmatch⟩ := SevenCliqueTwentySixFivePattern.exists_pattern G hG horder hmin hcn hsep v hv8 C hsize
  have hd := CliqueSixExtremalLocal.five_complement H hf hcard he u hu
  exact CliqueEightActualTemplate.surviving H hcard he hlow u hu hd hmatch hf
end Paper.SevenCliqueTwentySixClassification
