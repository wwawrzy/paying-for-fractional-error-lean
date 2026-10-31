import Paper.Endpoints.Rounding.GeneralCoveringRounding
import Paper.Endpoints.Girth.PlanarCrossingEdges

/-! The actual red-blue incidence graph in the planar application
of full-version-new, Corollary fv:rb:upper. -/
namespace Paper.RedBlue
open SimpleGraph SevenFoundation GeneralCoveringRounding
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def rows (R B : Finset V) (r : V) : Finset V :=
  if r ∈ R then G.neighborFinset r ∩ B else ∅

theorem mem_rows (R B : Finset V) (r v : V) :
    v ∈ rows G R B r ↔ r ∈ R ∧ G.Adj r v ∧ v ∈ B := by
  by_cases hr : r ∈ R <;> simp [rows, hr, G.mem_neighborFinset]

theorem rows_local (R B : Finset V) (r : V) : rows G R B r ⊆ closed G r := by
  intro v hv
  exact (mem_closed G v r).mpr (Or.inr ((mem_rows G R B r v).mp hv).2.1)

theorem no_self (R B : Finset V) (r : V) : r ∉ rows G R B r := by
  intro hr
  exact G.loopless.irrefl r ((mem_rows G R B r r).mp hr).2.1

theorem incidence_le_between (R B : Finset V) :
    incidenceGraph G (rows G R B) ≤ G.between (R : Set V) (B : Set V) := by
  intro u v huv
  apply between_adj.mpr
  refine ⟨huv.1, ?_⟩
  rcases huv.2 with hv | hu
  · obtain ⟨huR, _, hvB⟩ := (mem_rows G R B u v).mp hv
    exact Or.inl ⟨huR, hvB⟩
  · obtain ⟨hvR, _, huB⟩ := (mem_rows G R B v u).mp hu
    exact Or.inr ⟨huB, hvR⟩

theorem incidence_bipartite (R B : Finset V) (hRB : Disjoint R B) :
    (incidenceGraph G (rows G R B)).IsBipartite := by
  exact Colorable.mono_left (incidence_le_between G R B)
    (between_isBipartite (G := G) (Finset.disjoint_coe.mpr hRB))

theorem planar_density (hplanar : G.IsPlanar) (R B : Finset V) (hRB : Disjoint R B) :
    Incidence.InducedDensityBound (incidenceGraph G (rows G R B)) 2 := by
  have hp : (incidenceGraph G (rows G R B)).IsPlanar :=
    hplanar.mono (fun _ _ h => h.1)
  have hb := incidence_bipartite G R B hRB
  have hd := CurrentPlanarFaceBound.induced_density hp 4 (by decide)
    (PlanarCrossingEdges.girth_four_of_bipartite _ hb)
  norm_num at hd
  exact hd

end Paper.RedBlue
#print axioms Paper.RedBlue.rows_local
#print axioms Paper.RedBlue.no_self
#print axioms Paper.RedBlue.incidence_le_between
#print axioms Paper.RedBlue.incidence_bipartite
#print axioms Paper.RedBlue.planar_density
