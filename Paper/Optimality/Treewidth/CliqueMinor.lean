import Paper.Optimality.Treewidth.TreewidthMinor
import Paper.Optimality.Treewidth.TreewidthLowDegree
import Paper.Optimality.Treewidth.PathPowerTreewidth

/-! The complete-minor obstruction follows from actual minor monotonicity of
treewidth and the proved low-degree theorem. No clique-bag axiom is used. -/
namespace Paper.CliqueMinorTreewidth

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem excluded {r h : ℕ} (hG : G.treeWidth ≤ r) (hrh : r + 1 < h) :
    G.IsKMinorFree h := by
  intro hm
  have hw : (completeGraph (Fin h)).treeWidth ≤ r :=
    (TreewidthMinor.treeWidth_mono hm).trans hG
  letI : Nonempty (Fin h) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := TreewidthLowDegree.of_treeWidth r hw
  rw [complete_graph_degree, Fintype.card_fin] at hv
  omega

theorem pathPower (n r : ℕ) : (PathPowerTreewidth.graph n r).IsKMinorFree (r + 2) :=
  excluded (PathPowerTreewidth.treeWidth_le n r) (by omega)

end Paper.CliqueMinorTreewidth

#print axioms Paper.CliqueMinorTreewidth.excluded
#print axioms Paper.CliqueMinorTreewidth.pathPower
