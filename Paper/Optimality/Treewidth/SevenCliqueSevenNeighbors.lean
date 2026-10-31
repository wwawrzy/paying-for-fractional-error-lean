import Paper.Optimality.Treewidth.SevenCliqueProjection
import Paper.Optimality.Treewidth.CliqueNeighborhoodExterior

/-! Degree seven is impossible in an affine K7 core. The genuine outside
component adds an edge to a seven-vertex neighborhood of minimum degree
five, exceeding the proved K6 bound for the same rooted projection. -/
namespace Paper.SevenCliqueSevenNeighbors

open SimpleGraph PlaneTopology.WagnerSeparation CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem impossible (hG : G.IsKMinorFree 7)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (v : V) (hv : G.degree v = 7) (hproper : G.degree v + 1 < Fintype.card V)
    (hcn : ∀ w, G.Adj v w → 5 ≤ Fintype.card (G.commonNeighbors v w)) : False := by
  classical
  obtain ⟨X, hX, hXne, hout, hBN⟩ := CliqueNeighborhoodExterior.exists_exterior G v hproper
  let B := boundary G X
  have hnot := CliqueNeighborhoodExterior.boundary_not_clique G v X hXne hout hsep
  change ¬(∀ a ∈ (B : Set V), ∀ b ∈ (B : Set V), a ≠ b → G.Adj a b) at hnot
  push Not at hnot
  obtain ⟨a, ha, b, hb, hab, hnotab⟩ := hnot
  let aN : G.neighborSet v := ⟨a, hBN ha⟩
  let bN : G.neighborSet v := ⟨b, hBN hb⟩
  have hanchor : a ∉ X ∧ ∃ z ∈ X, G.Adj a z := (mem_boundary G X a).mp ha
  have hother : b ∉ X ∧ ∃ z ∈ X, G.Adj b z := (mem_boundary G X b).mp hb
  let S : Set V := insert a X
  have haS : aN.val ∈ S := Set.mem_insert _ _
  have hconn : (G.induce S).Connected := by
    obtain ⟨z, hz, haz⟩ := hanchor.2
    have hsingle := (MinorModel.refl G).connected a
    simpa only [Set.singleton_union] using
      connected_induce_union hsingle.preconnected hX.preconnected
        (Set.mem_singleton a) hz haz
  have hside : ∀ z ∈ S, z ∈ G.neighborSet v → z = aN.val := by
    intro z hz hzN
    rcases hz with hza | hzX
    · exact hza
    · exact False.elim (hout hzX (Or.inr hzN))
  have hvS : v ∉ S := by
    intro hh
    rcases hh with hva | hvX
    · exact G.loopless.irrefl v (hva.symm ▸ hBN ha)
    · exact hout hvX (Set.mem_insert _ _)
  have hcard : Fintype.card (G.neighborSet v) = 7 := by
    rw [G.card_neighborSet_eq_degree, hv]
  have hbound := SevenCliqueProjection.star_bound G hG v (G.neighborSet v) (fun _ h => h)
    aN S haS hconn hside hvS (by omega)
  have hgrow := CliqueStarBound.growth G (G.neighborSet v) aN bN S
    (fun hh => hab (congrArg Subtype.val hh)) hnotab (by
      obtain ⟨z, hz, hbz⟩ := hother.2
      exact ⟨z, Or.inr hz, hbz.symm⟩)
  letI : Nonempty (G.neighborSet v) := Fintype.card_pos_iff.mp (by omega)
  have hd : ∀ w : G.neighborSet v, 5 ≤ (G.induce (G.neighborSet v)).degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v 5 w (hcn w w.property)
  have hmin : 5 ≤ (G.induce (G.neighborSet v)).minDegree :=
    (G.induce (G.neighborSet v)).le_minDegree_of_forall_le_degree 5 hd
  have hshake := (G.induce (G.neighborSet v)).minDegree_mul_card_le_two_mul_card_edges
  have hmul := Nat.mul_le_mul_right (Fintype.card (G.neighborSet v)) hmin
  rw [hcard] at hbound hshake hmul
  omega

end Paper.SevenCliqueSevenNeighbors

#print axioms Paper.SevenCliqueSevenNeighbors.impossible
