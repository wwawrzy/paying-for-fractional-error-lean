import Paper.Preliminaries.MinorDensity

/-! The all-minors density hypothesis is inherited by actual minors. -/
namespace Paper.MinorInheritance
universe u
variable {V U : Type u} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem minor (J : SimpleGraph U) [DecidableRel J.Adj] {a : ℝ}
    (hden : MinorDensity.Bound G a) (hm : SimpleGraph.IsMinor J G) : MinorDensity.Bound J a := by
  intro A _ _ K _ hK
  exact hden A K (hK.trans hm)

theorem induced {a : ℝ} (hden : MinorDensity.Bound G a) (W : Finset V) :
    MinorDensity.Bound (G.induce (W : Set V)) a :=
  minor G _ hden (SimpleGraph.IsMinor.of_induce G _)
end Paper.MinorInheritance
