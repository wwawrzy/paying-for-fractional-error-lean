import Paper.Optimality.Treewidth.CliqueNeighborhoodExterior
import Paper.Optimality.Treewidth.CliqueStarBound

/-! A degree-seven neighborhood in the remaining global K6 case has
exactly fourteen edges and is four-regular. An actual outside component
supplies the missing edge used in the projection argument. -/
namespace Paper.SixCliqueSevenRegular

open SimpleGraph PlaneTopology.WagnerSeparation CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_count (hG : G.IsKMinorFree 6) (horder : 10 ≤ Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (v : V) (hv : G.degree v = 7)
    (hcn : ∀ w, G.Adj v w → 4 ≤ Fintype.card (G.commonNeighbors v w)) :
    (G.induce (G.neighborSet v)).edgeFinset.card = 14 := by
  classical
  obtain ⟨X, hX, hXne, hout, hBN⟩ :=
    CliqueNeighborhoodExterior.exists_exterior G v (by omega)
  have hvX : v ∉ X := fun hh => hout hh (Set.mem_insert _ _)
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
    rcases hh with hva | hvX'
    · exact G.loopless.irrefl v (hva.symm ▸ hBN ha)
    · exact hvX hvX'
  have hcard : Fintype.card (G.neighborSet v) = 7 := by
    rw [G.card_neighborSet_eq_degree, hv]
  have hbound := CliqueStarBound.edge_bound G hG v (G.neighborSet v) (fun _ h => h)
    aN S haS hconn hside hvS (by omega)
  have hgrow := CliqueStarBound.growth G (G.neighborSet v) aN bN S
    (fun hh => hab (congrArg Subtype.val hh)) hnotab (by
      obtain ⟨z, hz, hbz⟩ := hother.2
      exact ⟨z, Or.inr hz, hbz.symm⟩)
  letI : Nonempty (G.neighborSet v) := Fintype.card_pos_iff.mp (by omega)
  have hd : ∀ w : G.neighborSet v, 4 ≤ (G.induce (G.neighborSet v)).degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v 4 w (hcn w w.property)
  have hmin : 4 ≤ (G.induce (G.neighborSet v)).minDegree :=
    (G.induce (G.neighborSet v)).le_minDegree_of_forall_le_degree 4 hd
  have hshake := (G.induce (G.neighborSet v)).minDegree_mul_card_le_two_mul_card_edges
  have hmul := Nat.mul_le_mul_right (Fintype.card (G.neighborSet v)) hmin
  rw [hcard] at hbound hshake hmul
  omega

theorem regular (v : V) (hv : G.degree v = 7)
    (he : (G.induce (G.neighborSet v)).edgeFinset.card = 14)
    (hcn : ∀ w, G.Adj v w → 4 ≤ Fintype.card (G.commonNeighbors v w)) :
    ∀ w : G.neighborSet v, (G.induce (G.neighborSet v)).degree w = 4 := by
  classical
  have hcard : Fintype.card (G.neighborSet v) = 7 := by
    rw [G.card_neighborSet_eq_degree, hv]
  have hd : ∀ w : G.neighborSet v, 4 ≤ (G.induce (G.neighborSet v)).degree w := by
    intro w
    exact commonNeighbors_implies_induced_degree G v 4 w (hcn w w.property)
  have hsum : (∑ w : G.neighborSet v, (G.induce (G.neighborSet v)).degree w) = 28 := by
    rw [(G.induce (G.neighborSet v)).sum_degrees_eq_twice_card_edges, he]
  intro w
  have hwlow := hd w
  have hrest : ∑ z ∈ Finset.univ.erase w, 4 ≤
      ∑ z ∈ Finset.univ.erase w, (G.induce (G.neighborSet v)).degree z :=
    Finset.sum_le_sum (fun z _ => hd z)
  have hwsum := Finset.sum_erase_add (Finset.univ (α := G.neighborSet v))
    (fun z => (G.induce (G.neighborSet v)).degree z) (Finset.mem_univ w)
  change (∑ z ∈ Finset.univ.erase w, (G.induce (G.neighborSet v)).degree z) +
    (G.induce (G.neighborSet v)).degree w =
      (∑ z : G.neighborSet v, (G.induce (G.neighborSet v)).degree z) at hwsum
  have hsize : (Finset.univ.erase w : Finset (G.neighborSet v)).card = 6 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, hcard]
  simp only [Finset.sum_const, smul_eq_mul, hsize] at hrest
  omega

theorem neighborhood_degree (v : V) (w : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree w = G.inducedDegree w.val (G.neighborFinset v) := by
  classical
  have he : ((G.induce (G.neighborSet v)).neighborFinset w).image Subtype.val =
      (G.neighborFinset v).filter (G.Adj w.val) := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v y.val).mpr y.property,
        ((G.induce (G.neighborSet v)).mem_neighborFinset w y).mp hy⟩
    · intro hz
      obtain ⟨hzN, hwz⟩ := Finset.mem_filter.mp hz
      let zN : G.neighborSet v := ⟨z, (G.mem_neighborFinset v z).mp hzN⟩
      exact Finset.mem_image.mpr ⟨zN,
        ((G.induce (G.neighborSet v)).mem_neighborFinset w zN).mpr hwz, rfl⟩
  have hc := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

theorem regular_finset (v : V) (hv : G.degree v = 7)
    (he : (G.induce (G.neighborSet v)).edgeFinset.card = 14)
    (hcn : ∀ w, G.Adj v w → 4 ≤ Fintype.card (G.commonNeighbors v w)) :
    ∀ w ∈ G.neighborFinset v, G.inducedDegree w (G.neighborFinset v) = 4 := by
  intro w hw
  let wN : G.neighborSet v := ⟨w, (G.mem_neighborFinset v w).mp hw⟩
  rw [← neighborhood_degree G v wN]
  exact regular G v hv he hcn wN

end Paper.SixCliqueSevenRegular

#print axioms Paper.SixCliqueSevenRegular.edge_count
#print axioms Paper.SixCliqueSevenRegular.regular
#print axioms Paper.SixCliqueSevenRegular.neighborhood_degree
#print axioms Paper.SixCliqueSevenRegular.regular_finset
