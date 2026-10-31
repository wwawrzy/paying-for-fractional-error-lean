import Paper.RedBlue.IncidenceDensity
import Paper.Communication.SurfaceGirthThreshold
import Paper.Certificates.Counting.ApproximateOrientation
namespace Paper.RedBlue
attribute [local instance] Classical.propDecidable
open SimpleGraph SevenFoundation GeneralCoveringRounding
variable {V : Type} [Fintype V] [DecidableEq V]
theorem surface_incidence_density (G : SimpleGraph V) [DecidableRel G.Adj]
    (rot : SignedRotation G) (e : ℝ) (he : (rot.eulerGenus : ℝ) ≤ e)
    (R B : Finset V) (hRB : Disjoint R B) :
    ∀ S : Finset V,
      ((incidenceGraph G (rows G R B)).inducedEdgeCount S : ℝ) ≤ 2*S.card+2*e := by
  classical
  let I := incidenceGraph G (rows G R B)
  have hIG : I ≤ G := fun _ _ h => h.1
  obtain ⟨s,hs⟩ := SignedRotation.exists_subgraph_genus_le G rot I hIG
  have hsR : (s.eulerGenus : ℝ) ≤ e := (by exact_mod_cast hs : (s.eulerGenus : ℝ) ≤ (rot.eulerGenus : ℝ)) |>.trans he
  have hg := PlanarCrossingEdges.girth_four_of_bipartite I (incidence_bipartite G R B hRB)
  intro S
  have hh := SurfaceGirthThreshold.induced_density I s 4 (by omega) hg e hsR S
  norm_num at hh
  exact hh
theorem surface_incidence_orientation (G : SimpleGraph V) [DecidableRel G.Adj]
    (rot : SignedRotation G) (g : ℕ) (he : (rot.eulerGenus : ℝ) ≤ g)
    (R B : Finset V) (hRB : Disjoint R B) :
    ∃ O : ApproximateOrientation.MultiOrientation (incidenceGraph G (rows G R B)) 1,
      ∃ err : V → ℕ,
      (∀ v, ApproximateOrientation.load _ O v ≤ 2+err v) ∧ (∑ v, err v) ≤ 2*g := by
  classical
  apply ApproximateOrientation.exists_orientation _ 2 (2*g) 1
  intro S
  have h := surface_incidence_density G rot (g : ℝ) he R B hRB S
  have hn : (incidenceGraph G (rows G R B)).inducedEdgeCount S ≤ 2*S.card+2*g := by
    exact_mod_cast h
  simpa using hn
end Paper.RedBlue
#print axioms Paper.RedBlue.surface_incidence_density
#print axioms Paper.RedBlue.surface_incidence_orientation
