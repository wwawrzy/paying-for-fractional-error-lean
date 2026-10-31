import Paper.Preliminaries.SevenFoundation
import GraphTheory.SimpleGraph.InducedCounting

/-!
# Closed incidences between overlapping vertex sets

The incidence bound is proved from the actual graph. Only its final corollary
assumes an edge-density bound, explicitly for every induced subgraph and with
a real parameter. This is the graph-counting input for the selection saving
in the self-contained the covering paper paper.
-/

namespace Paper.Incidence

open scoped BigOperators
open SevenFoundation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Edge density of every induced subgraph, without rounding the parameter. -/
def InducedDensityBound (t : ℝ) : Prop :=
  ∀ S : Finset V, (G.inducedEdgeCount S : ℝ) ≤ t * S.card

theorem card_interedges_self (S : Finset V) :
    (G.interedges S S).card = 2 * G.inducedEdgeCount S := by
  simpa only [SimpleGraph.interedges_def, InducedCounting.arcs] using
    InducedCounting.card_arcs_eq_two_mul G S

theorem card_interedges_comm (A B : Finset V) :
    (G.interedges A B).card = (G.interedges B A).card := by
  have heq : (G.interedges A B).image Prod.swap = G.interedges B A := by
    ext p
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (G.swap_mem_interedges_iff).mpr hq
    · intro hp
      exact ⟨p.swap, (G.swap_mem_interedges_iff).mpr hp, Prod.swap_swap p⟩
  rw [← heq, Finset.card_image_of_injective _ Prod.swap_injective]

theorem interedges_inter_reverse (A B : Finset V) :
    G.interedges A B ∩ G.interedges B A = G.interedges (A ∩ B) (A ∩ B) := by
  ext p
  simp only [Finset.mem_inter, SimpleGraph.mem_interedges_iff]
  tauto

theorem interedges_union_reverse_subset (A B : Finset V) :
    G.interedges A B ∪ G.interedges B A ⊆ G.interedges (A ∪ B) (A ∪ B) := by
  intro p hp
  simp only [Finset.mem_union, SimpleGraph.mem_interedges_iff] at hp ⊢
  tauto

/-- Internal edges in the overlap can contribute twice, and all other edges once. -/
theorem card_interedges_le (A B : Finset V) :
    (G.interedges A B).card ≤
      G.inducedEdgeCount (A ∪ B) + G.inducedEdgeCount (A ∩ B) := by
  have hcard := Finset.card_union_add_card_inter (G.interedges A B) (G.interedges B A)
  have hsub := Finset.card_le_card (interedges_union_reverse_subset G A B)
  rw [interedges_inter_reverse, card_interedges_self,
    ← card_interedges_comm G A B] at hcard
  rw [card_interedges_self] at hsub
  omega

theorem card_interedges_eq_sum (A B : Finset V) :
    (G.interedges A B).card = ∑ v ∈ A, (B.filter (G.Adj v)).card := by
  simp only [SimpleGraph.interedges_def, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.sum_product]

theorem closed_inter_card (v : V) (B : Finset V) :
    (closed G v ∩ B).card = (B.filter (G.Adj v)).card + if v ∈ B then 1 else 0 := by
  by_cases hv : v ∈ B
  · have heq : closed G v ∩ B = insert v (B.filter (G.Adj v)) := by
      ext u
      simp only [Finset.mem_inter, mem_closed, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨heq | hadj, hu⟩
        · exact Or.inl heq
        · exact Or.inr ⟨hu, hadj⟩
      · rintro (rfl | ⟨hu, hadj⟩)
        · exact ⟨Or.inl rfl, hv⟩
        · exact ⟨Or.inr hadj, hu⟩
    rw [heq, Finset.card_insert_of_notMem (by simp), if_pos hv]
  · have heq : closed G v ∩ B = B.filter (G.Adj v) := by
      ext u
      simp only [Finset.mem_inter, mem_closed, Finset.mem_filter]
      constructor
      · rintro ⟨heq | hadj, hu⟩
        · exact False.elim (hv (heq ▸ hu))
        · exact ⟨hu, hadj⟩
      · rintro ⟨hu, hadj⟩
        exact ⟨Or.inr hadj, hu⟩
    simp [heq, hv]

theorem sum_closed_inter_card (A B : Finset V) :
    (∑ v ∈ A, (closed G v ∩ B).card) =
      (G.interedges A B).card + (A ∩ B).card := by
  simp_rw [closed_inter_card]
  rw [Finset.sum_add_distrib, ← card_interedges_eq_sum]
  congr 1
  have heq : A.filter (fun v => v ∈ B) = A ∩ B := by
    ext v
    simp
  rw [← heq]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- The graph-level closed-incidence inequality, with no density hypothesis. -/
theorem closed_incidence_le (A B : Finset V) :
    (∑ v ∈ A, (closed G v ∩ B).card) ≤
      G.inducedEdgeCount (A ∪ B) + G.inducedEdgeCount (A ∩ B) + (A ∩ B).card := by
  rw [sum_closed_inter_card]
  exact Nat.add_le_add_right (card_interedges_le G A B) _

/-- A real density parameter gives the exact coefficient used in the paper. -/
theorem closed_incidence_le_of_density {t : ℝ} (hdensity : InducedDensityBound G t)
    (A B : Finset V) :
    (∑ v ∈ A, ((closed G v ∩ B).card : ℝ)) ≤
      t * (A ∪ B).card + (t + 1) * (A ∩ B).card := by
  have hnat := closed_incidence_le G A B
  have hreal : (∑ v ∈ A, ((closed G v ∩ B).card : ℝ)) ≤
      (G.inducedEdgeCount (A ∪ B) : ℝ) +
        (G.inducedEdgeCount (A ∩ B) : ℝ) + (A ∩ B).card := by
    exact_mod_cast hnat
  have hUnion := hdensity (A ∪ B)
  have hInter := hdensity (A ∩ B)
  nlinarith

end Paper.Incidence
