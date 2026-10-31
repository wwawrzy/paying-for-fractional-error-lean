import Paper.Averaging.Tasks.MaskedTaskGraph
import Paper.Solver.LocalSearch.SearchSpec

namespace Paper.MaskedTaskCover
open SevenFoundation
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem closed_sum {A : Type} [AddCommMonoid A] (H : Finset V) (v : V) (hv : v ∈ H)
    (f : V → A) (hz : ∀ u, u ∉ H → f u = 0) :
    (∑ u ∈ closed (MaskedTaskGraph.graph G H) v, f u) = ∑ u ∈ closed G v, f u := by
  rw [MaskedTaskGraph.closed_inside G H v hv]
  apply Finset.sum_subset Finset.inter_subset_left
  intro u hu hn
  exact hz u (fun h => hn (Finset.mem_inter.mpr ⟨hu, h⟩))

theorem cover (H : Finset V) (d p : V → ℕ)
    (hd : ∀ r, r ∉ H → d r = 0) (hp : ∀ u, u ∉ H → p u = 0)
    (hcover : ∀ r, d r ≤ ∑ u ∈ closed G r, p u) :
    ∀ r, d r ≤ ∑ u ∈ closed (MaskedTaskGraph.graph G H) r, p u := by
  intro r
  by_cases hr : r ∈ H
  · rw [closed_sum G H r hr p hp]
    exact hcover r
  · rw [hd r hr]
    exact Nat.zero_le _

theorem closed_subset (H : Finset V) (r : V) : closed (MaskedTaskGraph.graph G H) r ⊆ closed G r := by
  intro u hu
  rcases (mem_closed (MaskedTaskGraph.graph G H) u r).mp hu with he | ha
  · exact (mem_closed G u r).mpr (Or.inl he)
  · exact (mem_closed G u r).mpr (Or.inr ha.1)

theorem valid_original [LinearOrder V] (H : Finset V) {B q m : ℕ}
    (c : V → Fin (B + 1)) (d : V → Fin (q + 1)) (w : SolutionWord.Word V B)
    (hw : SearchSpec.Valid (MaskedTaskGraph.graph G H) H c d m w) :
    SearchSpec.Valid G H c d m w := by
  refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩
  intro r
  exact (hw.2.2.2 r).trans (Finset.sum_le_sum_of_subset_of_nonneg (closed_subset G H r)
    (fun _ _ _ => Nat.zero_le _))
end Paper.MaskedTaskCover
