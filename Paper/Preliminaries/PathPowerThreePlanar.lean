import Paper.Preliminaries.PathPowerIntervals
import Paper.Optimality.Treewidth.TreewidthMinor
import Paper.Optimality.Treewidth.TreewidthLowDegree
import GraphTheory.SimpleGraph.Planar.Basic

namespace Paper.PathPowerThreePlanar
open SimpleGraph PathPowerTreewidth

/-- Width three excludes K5 using the proved minor-width and low-degree lemmas. -/
theorem no_K5 (n : ℕ) : (graph n 3).IsK5MinorFree := by
  intro hminor
  have hwidth : (completeGraph (Fin 5)).treeWidth ≤ 3 :=
    (TreewidthMinor.treeWidth_mono hminor).trans (treeWidth_le n 3)
  obtain ⟨v, hv⟩ := TreewidthLowDegree.of_treeWidth (G := completeGraph (Fin 5)) 3 hwidth
  simpa using hv

/-- The interval argument excludes the actual nine-edge bipartite minor model. -/
theorem no_K33 (n : ℕ) : (graph n 3).IsK33MinorFree := by
  rintro ⟨M⟩
  apply IntervalBiclique.no_cross (PathPowerIntervals.intervals M)
  intro i j
  exact PathPowerIntervals.adjacent_overlap M (by simp)

/-- Third powers of finite paths are genuinely planar in the repository's
forbidden-minor definition. No geometric/planarity axiom is invoked. -/
theorem isPlanar (n : ℕ) : (graph n 3).IsPlanar := ⟨no_K5 n, no_K33 n⟩

end Paper.PathPowerThreePlanar
