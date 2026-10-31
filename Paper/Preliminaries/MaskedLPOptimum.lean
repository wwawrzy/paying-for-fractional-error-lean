import Paper.Preliminaries.MaskedLP

namespace Paper.MaskedLPOptimum
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem number_le_feasible (R : Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (x : V → ℝ) (hx : PartialOptimum.Feasible G R x) :
    PartialOptimum.number G R c ≤ PartialOptimum.objective c x := by
  obtain ⟨z, hz, _, hmin⟩ := PartialOptimum.exists_optimum G R c hc
  have hl : IsLeast (PartialOptimum.values G R c) (PartialOptimum.objective c z) := by
    refine ⟨⟨z, hz, rfl⟩, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    exact hmin w hw
  exact hl.csInf_eq.trans_le (hmin x hx)

theorem number_eq (H R : Finset V) (hR : R ⊆ H) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    PartialOptimum.number (MaskedTaskGraph.graph G H) R c =
      PartialOptimum.number (G.induce (H : Set V)) (InducedSubsets.lift H R)
        (fun v : ↥(H : Set V) => c v.val) := by
  apply le_antisymm
  · obtain ⟨z, hz, he⟩ := PartialOptimum.exists_optimum_eq_number (G.induce (H : Set V))
      (InducedSubsets.lift H R) (fun v : ↥(H : Set V) => c v.val) (fun v => hc v.val)
    calc
      _ ≤ PartialOptimum.objective c (MaskedLP.extend H z) :=
        number_le_feasible (MaskedTaskGraph.graph G H) R c hc (MaskedLP.extend H z)
          (MaskedLP.extend_feasible G H R hR z hz)
      _ = PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) z := MaskedLP.extend_cost H c z
      _ = _ := he
  · obtain ⟨x, hx, he⟩ := PartialOptimum.exists_optimum_eq_number (MaskedTaskGraph.graph G H) R c hc
    calc
      _ ≤ PartialOptimum.objective (fun v : ↥(H : Set V) => c v.val) (fun v => x v.val) :=
        number_le_feasible (G.induce (H : Set V)) (InducedSubsets.lift H R)
          (fun v : ↥(H : Set V) => c v.val) (fun v => hc v.val) (fun v => x v.val)
          (MaskedLP.restrict_feasible G H R hR x hx)
      _ ≤ PartialOptimum.objective c x := MaskedLP.restrict_cost_le H c x hc hx.1
      _ = _ := he
end Paper.MaskedLPOptimum
