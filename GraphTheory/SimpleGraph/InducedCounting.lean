/-
Copyright (c) 2026 Wojciech Wawrzyniak. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import GraphTheory.SimpleGraph.Degeneracy

/-! # Arcs, degrees and edge counts of induced subgraphs -/
namespace InducedCounting
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The **arcs of `G` inside `s`**, that is the ordered pairs of adjacent
vertices of `s`.  Every edge of `G[s]` gives two arcs. -/
def arcs (s : Finset V) : Finset (V × V) :=
  (s ×ˢ s).filter (fun p => G.Adj p.1 p.2)

@[simp] theorem mem_arcs {s : Finset V} {p : V × V} :
    p ∈ arcs G s ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ G.Adj p.1 p.2 := by
  simp [arcs, Finset.mem_product, and_assoc]

theorem arcs_mono {s t : Finset V} (h : s ⊆ t) : arcs G s ⊆ arcs G t := by
  intro p hp
  rw [mem_arcs] at hp ⊢
  exact ⟨h hp.1, h hp.2.1, hp.2.2⟩

/-- The arcs inside `s` are counted by the induced degrees. -/
theorem card_arcs (s : Finset V) :
    (arcs G s).card = ∑ v ∈ s, G.inducedDegree v s := by
  have hb : arcs G s
      = s.biUnion (fun v => (s.filter (G.Adj v)).image (fun u => (v, u))) := by
    ext p
    simp only [mem_arcs, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨p.1, h1, p.2, ⟨h2, h3⟩, rfl⟩
    · rintro ⟨v, hv, u, ⟨hu, hadj⟩, rfl⟩
      exact ⟨hv, hu, hadj⟩
  rw [hb, Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro v _
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    rfl
  · intro x _ y _ hxy
    refine Finset.disjoint_left.2 ?_
    rintro ⟨p1, p2⟩ hp hq
    simp only [Finset.mem_image, Finset.mem_filter] at hp hq
    obtain ⟨u, -, hu⟩ := hp
    obtain ⟨u', -, hu'⟩ := hq
    rw [Prod.mk.injEq] at hu hu'
    exact hxy (hu.1.trans hu'.1.symm)

/-- The degree in the induced subgraph `G[s]` is the induced degree. -/
theorem degree_induce_eq_inducedDegree (s : Finset V)
    (v : {x : V // x ∈ (s : Set V)}) :
    (G.induce (s : Set V)).degree v = G.inducedDegree v.val s := by
  unfold SimpleGraph.inducedDegree SimpleGraph.degree
  simp only [SimpleGraph.neighborFinset]
  rw [Set.toFinset_card, ← Fintype.card_coe (s.filter (G.Adj v.val))]
  apply Fintype.card_of_bijective
    (f := fun (u : (G.induce (s : Set V)).neighborSet v) =>
      (⟨u.val.val, by
        rw [Finset.mem_filter]
        refine ⟨u.val.property, ?_⟩
        have hu := u.property
        rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj] at hu
        exact hu⟩ : {x // x ∈ s.filter (G.Adj v.val)}))
  constructor
  · intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  · intro ⟨w, hw⟩
    rw [Finset.mem_filter] at hw
    refine ⟨⟨⟨w, hw.1⟩, ?_⟩, by simp⟩
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.induce_adj]
    exact hw.2

/-- The handshake identity inside `s`: the induced degrees sum to twice the
number of induced edges, that is to the number of arcs. -/
theorem sum_inducedDegree_eq_two_mul (s : Finset V) :
    ∑ v ∈ s, G.inducedDegree v s = 2 * G.inducedEdgeCount s := by
  rw [SimpleGraph.inducedEdgeCount,
    ← SimpleGraph.sum_degrees_eq_twice_card_edges (G.induce (s : Set V)),
    Finset.sum_subtype (p := fun x => x ∈ (s : Set V)) s (fun x => by simp)
      (fun v => G.inducedDegree v s)]
  exact Finset.sum_congr rfl (fun v _ => (degree_induce_eq_inducedDegree G s v).symm)

theorem card_arcs_eq_two_mul (s : Finset V) :
    (arcs G s).card = 2 * G.inducedEdgeCount s := by
  rw [card_arcs, sum_inducedDegree_eq_two_mul]


end InducedCounting
