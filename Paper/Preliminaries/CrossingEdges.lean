import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! Edges crossing any physical labeling are bounded by the incidence
budget of a vertex set meeting every crossing edge. -/
namespace Paper.CrossingEdges
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type*}

def graph (S : Finset V) (p : V → A) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S ∧ p u ≠ p v
  symm := fun _ _ ⟨ha, hu, hv, hn⟩ => ⟨ha.symm, hv, hu, hn.symm⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem edge_cover (S D : Finset V) (p : V → A)
    (hcover : ∀ u v, (graph G S p).Adj u v → u ∈ D ∨ v ∈ D) :
    (graph G S p).edgeFinset ⊆ D.biUnion (fun v => G.incidenceFinset v) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
    have ha : (graph G S p).Adj u v := by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    rcases hcover u v ha with hu | hv
    · exact Finset.mem_biUnion.mpr ⟨u, hu,
        (G.mem_incidenceFinset _ _).mpr ((G.mk'_mem_incidenceSet_left_iff).mpr ha.1)⟩
    · exact Finset.mem_biUnion.mpr ⟨v, hv,
        (G.mem_incidenceFinset _ _).mpr ((G.mk'_mem_incidenceSet_right_iff).mpr ha.1)⟩

theorem count (S D : Finset V) (p : V → A) (Δ : ℕ)
    (hdeg : ∀ v ∈ D, G.degree v ≤ Δ)
    (hcover : ∀ u v, (graph G S p).Adj u v → u ∈ D ∨ v ∈ D) :
    (graph G S p).edgeFinset.card ≤ Δ * D.card := by
  calc
    _ ≤ (D.biUnion (fun v => G.incidenceFinset v)).card := Finset.card_le_card (edge_cover G S D p hcover)
    _ ≤ ∑ v ∈ D, (G.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ D, G.degree v := by simp only [SimpleGraph.card_incidenceFinset_eq_degree]
    _ ≤ ∑ _v ∈ D, Δ := Finset.sum_le_sum hdeg
    _ = _ := by simp [mul_comm]
end Paper.CrossingEdges
