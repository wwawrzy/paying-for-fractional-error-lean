import Paper.Endpoints.Components.ComponentDensity
import Paper.Endpoints.Components.IncidenceGraph
import Paper.Endpoints.Rounding.SurfaceResidualBudget
namespace Paper.SurfaceResidual
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)

theorem incidence_density (e : ℝ) (he : 0 ≤ e)
    (hden : ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ 3 * S.card + 3 * e) :
    Incidence.InducedDensityBound
      (CoveringIncidence.graph (cover G d) (CurrentBudget.demands G d)) (3 + 3 * e) := by
  apply ComponentDensity.subgraph_density G
  · exact CoveringIncidence.graph_le G _ _ (fun _ _ => Finset.inter_subset_left)
  · intro S
    by_cases hs : S = ∅
    · subst S
      simp [SimpleGraph.inducedEdgeCount]
    · have hc : (1 : ℝ) ≤ S.card := by
        exact_mod_cast Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      have h := hden S
      nlinarith
end Paper.SurfaceResidual
