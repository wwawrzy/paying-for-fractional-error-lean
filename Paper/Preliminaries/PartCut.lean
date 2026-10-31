import Paper.Preliminaries.CrossingEdges
import Paper.Preliminaries.SmallParts

/-! The actual graph of edges between distinct parts, defined directly
from the physical partition family. -/
namespace Paper.PartCut
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def graph (S : Finset V) (P : Finset (Finset V)) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ ¬ ∃ U ∈ P, u ∈ U ∧ v ∈ U
  symm := fun _ _ ⟨ha, hu, hv, hn⟩ => ⟨ha.symm, hv, hu, fun ⟨U, hU, hvU, huU⟩ => hn ⟨U, hU, huU, hvU⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem le (S : Finset V) (P : Finset (Finset V)) : graph G S P ≤ G := fun _ _ h => h.1

theorem family_mono (S : Finset V) {P Q : Finset (Finset V)} (hPQ : P ⊆ Q) :
    graph G S Q ≤ graph G S P := by
  intro u v h
  exact ⟨h.1, h.2.1, h.2.2.1, fun ⟨U, hU, hu, hv⟩ => h.2.2.2 ⟨U, hPQ hU, hu, hv⟩⟩

theorem singleton_bound (S : Finset V) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    2 * (graph G S (S.image (fun v => {v}))).edgeFinset.card ≤ Δ * S.card := by
  let K := graph G S (S.image (fun v => {v}))
  have hdeg' : ∀ v, K.degree v ≤ G.degree v := fun v => SimpleGraph.degree_le_of_le (v := v) (le G S _)
  have hz : ∀ v ∉ S, K.degree v = 0 := by
    intro v hv
    change (K.neighborFinset v).card = 0
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact hv ((K.mem_neighborFinset v u).mp hu).2.1
  have hs : (∑ v, K.degree v) = ∑ v ∈ S, K.degree v :=
    (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hz v hv)).symm
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, hs]
  calc
    _ ≤ ∑ _v ∈ S, Δ := Finset.sum_le_sum (fun v _ => (hdeg' v).trans (hdeg v))
    _ = _ := by simp [mul_comm]
end Paper.PartCut
