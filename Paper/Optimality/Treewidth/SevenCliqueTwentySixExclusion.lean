import Paper.Optimality.Treewidth.CliqueResidualBoundaryThree
import Paper.Optimality.Treewidth.CliqueAffineBoundaryBudget
import Paper.Optimality.Treewidth.SevenCliqueTwentyFiveVertices
namespace Paper.SevenCliqueTwentySixExclusion
open SimpleGraph CliqueComponentBoundary SevenCliqueEightExteriorSize
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem component_impossible (hG : G.IsKMinorFree 7) (horder : Fintype.card V = 26)
    (hmin : ∀ z, 8 ≤ G.degree z)
    (hcn : ∀ u w, G.Adj u w → 5 ≤ Fintype.card (G.commonNeighbors u w))
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (PlaneTopology.WagnerSeparation.Separation G S))
    (hedges : G.edgeFinset.card+14 = 5*Fintype.card V)
    (hminimal : CliqueMinorMinimal.BelowThreshold G 5 14 5)
    (v : V) (hv8 : G.degree v = 8)
    (C : (G.induce (insert v (G.neighborSet v))ᶜ).ConnectedComponent)
    (hsize : (vertices (outside G (insert v (G.neighborSet v)) C)).card = 8) :
    False := by
  classical
  let X := outside G (insert v (G.neighborSet v)) C
  let T := vertices X
  have hm : ∀ z, G.degree v ≤ G.degree z := by intro z; rw [hv8]; exact hmin z
  obtain ⟨a,b,⟨e⟩,hp⟩ := SevenCliqueTwentySixClassification.component G hG horder hmin hcn hsep v hv8 C hsize
  obtain ⟨ec⟩ := CliqueResidualCanonical.canonical a b hp
  have hdegree : ∀ z ∈ T, G.degree z = 8 := by
    intro z hz
    exact SevenCliqueEightRegular.component_regular G hG v hv8 hm (hcn v) C hsize z hz
  have hreg : ∀ a ∈ T, ∀ z ∈ T, G.Adj a z → G.inducedDegree z (G.neighborFinset a) = 5 := by
    intro a ha z hz haz
    have ha8 := hdegree a ha
    have hma : ∀ w, G.degree a ≤ G.degree w := by intro w; rw [ha8]; exact hmin w
    have hproper : G.degree a+1 < Fintype.card V := by rw [ha8,horder]; decide
    obtain ⟨D,hD⟩ := SevenCliqueTwentySixNeighborhood.has_eight G hG a ha8 hma (hcn a) hproper hsep horder
    exact SevenCliqueEightNeighborhood.neighborhood_regular G hG a ha8 hma (hcn a) D hD z
      ((G.mem_neighborFinset a z).mpr haz)
  have hb := CliqueResidualBoundaryThree.bound G T hsize (e.trans ec) hdegree hcn hreg
  have hsz : T.card = 8 := hsize
  have hne : (T : Set V).Nonempty := by
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
    exact ⟨z,hz⟩
  have hout : (T : Set V) ⊆ (insert v (G.neighborSet v))ᶜ := by
    intro z hz
    exact outside_subset G (insert v (G.neighborSet v)) C ((mem_vertices X z).mp hz)
  have hl := (CliqueAffineBoundaryBudget.boundary_budget G hedges
    (fun z => by have hh := hmin z; omega) hminimal v (T : Set V) hne hout).2
  omega
end Paper.SevenCliqueTwentySixExclusion
