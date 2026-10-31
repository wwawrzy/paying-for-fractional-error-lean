import Paper.Optimality.Treewidth.SixCliqueGlobalReduction
import Paper.Optimality.Treewidth.CliqueComponentBoundary
import Paper.Optimality.Treewidth.CliqueStarBound

/-! The degree-six case of the global K6 reduction. A real outside
component has a nonclique boundary. Absorbing it creates a new edge in
the six-vertex neighborhood, contradicting the K5 additive bound. -/
namespace Paper.SixCliqueSixNeighbors

open SimpleGraph PlaneTopology.WagnerSeparation CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem impossible (hG : G.IsKMinorFree 6) (horder : 10 ≤ Fintype.card V)
    (hsep : ∀ S : Finset V, G.IsClique (S : Set V) → IsEmpty (Separation G S))
    (v : V) (hv : G.degree v = 6)
    (hcn : ∀ w, G.Adj v w → 4 ≤ Fintype.card (G.commonNeighbors v w)) : False := by
  classical
  let A : Set V := insert v (G.neighborSet v)
  have hex : ∃ x, x ∉ A := by
    by_contra hn
    push_neg at hn
    have heq : insert v (G.neighborFinset v) = Finset.univ := by
      ext x
      simp only [Finset.mem_insert, G.mem_neighborFinset, Finset.mem_univ, iff_true]
      exact hn x
    have hsize := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
      G.card_neighborFinset_eq_degree, Finset.card_univ, hv] at hsize
    omega
  obtain ⟨x, hx⟩ := hex
  let C := (G.induce Aᶜ).connectedComponentMk ⟨x, hx⟩
  let X := outside G A C
  have hX : (G.induce X).Connected := outside_connected G A C
  have hXA : X ⊆ Aᶜ := outside_subset G A C
  have hvX : v ∉ X := fun hh => hXA hh (Set.mem_insert _ _)
  have hno : ∀ z ∈ X, ¬G.Adj v z := by
    intro z hz hadj
    exact hXA hz (Or.inr hadj)
  have hXne : X.Nonempty := by
    obtain ⟨z, hz⟩ := C.nonempty_supp
    exact ⟨z.val, z, hz, rfl⟩
  let B := boundary G X
  have hBN : (B : Set V) ⊆ G.neighborSet v := by
    intro y hy
    have hyA : y ∈ A := boundary_subset G A C hy
    rcases hyA with hyv | hyN
    · subst y
      obtain ⟨_, z, hz, hvz⟩ := (mem_boundary G X v).mp hy
      exact False.elim (hno z hz hvz)
    · exact hyN
  have hnot : ¬G.IsClique (B : Set V) := by
    intro hh
    have hi := hsep B hh
    exact hi.false (separation G X hXne v hvX hno)
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
    · exact False.elim (hXA hzX (Or.inr hzN))
  have hvS : v ∉ S := by
    intro hh
    rcases hh with hva | hvX'
    · exact G.loopless.irrefl v (hva.symm ▸ hBN ha)
    · exact hvX hvX'
  have hcard : Fintype.card (G.neighborSet v) = 6 := by
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

end Paper.SixCliqueSixNeighbors

#print axioms Paper.SixCliqueSixNeighbors.impossible
