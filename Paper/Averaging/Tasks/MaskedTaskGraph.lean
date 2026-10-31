import Paper.Preliminaries.MinorDensity
import Paper.Preliminaries.SevenFoundation

/-! A task/zone graph on public identifiers: keep precisely edges whose
two endpoints participate. Outside vertices remain isolated. -/
namespace Paper.MaskedTaskGraph
variable {V : Type} [DecidableEq V]

def graph (G : SimpleGraph V) (H : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ H ∧ v ∈ H
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

instance maskedAdj (G : SimpleGraph V) [DecidableRel G.Adj] (H : Finset V) :
    DecidableRel (graph G H).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem le (G : SimpleGraph V) (H : Finset V) : graph G H ≤ G := fun _ _ h => h.1

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem neighbor_inside (H : Finset V) (v : V) (hv : v ∈ H) :
    (graph G H).neighborFinset v = G.neighborFinset v ∩ H := by
  ext u
  simp only [SimpleGraph.mem_neighborFinset, graph, Finset.mem_inter, hv, true_and]

theorem neighbor_outside (H : Finset V) (v : V) (hv : v ∉ H) :
    (graph G H).neighborFinset v = ∅ := by
  ext u
  simp only [SimpleGraph.mem_neighborFinset, graph, hv, false_and, and_false, Finset.notMem_empty]

theorem induced_eq (H : Finset V) : (graph G H).induce (H : Set V) = G.induce (H : Set V) := by
  ext u v
  change (G.Adj u.val v.val ∧ u.val ∈ H ∧ v.val ∈ H) ↔ G.Adj u.val v.val
  exact ⟨fun h => h.1, fun h => ⟨h, u.property, v.property⟩⟩

theorem density (H : Finset V) {a : ℝ} (h : MinorDensity.Bound G a) : MinorDensity.Bound (graph G H) a :=
  fun A _ _ J _ hJ => h A J (hJ.trans (SimpleGraph.IsMinor.of_subgraph (le G H)))

theorem closed_inside (H : Finset V) (v : V) (hv : v ∈ H) :
    SevenFoundation.closed (graph G H) v = SevenFoundation.closed G v ∩ H := by
  ext u
  simp only [SevenFoundation.mem_closed, graph, Finset.mem_inter]
  constructor
  · rintro (he | ⟨ha, _, hu⟩)
    · exact ⟨Or.inl he, he ▸ hv⟩
    · exact ⟨Or.inr ha, hu⟩
  · rintro ⟨he | ha, hu⟩
    · exact Or.inl he
    · exact Or.inr ⟨ha, hv, hu⟩
end Paper.MaskedTaskGraph
