import Paper.Optimality.Treewidth.SixCliqueSevenRegular

/-! A component boundary in the remaining seven-neighbor case has at
most one missing neighbor at each boundary vertex. Two such missing
neighbors would both become edges in the same actual star projection. -/
namespace Paper.SixCliqueBoundaryMissing

open SimpleGraph CliqueComponentBoundary
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem unique (hG : G.IsKMinorFree 6) (v : V) (hv : G.degree v = 7)
    (he : (G.induce (G.neighborSet v)).edgeFinset.card = 14)
    (X : Set V) (hX : (G.induce X).Connected)
    (hout : X ⊆ (insert v (G.neighborSet v))ᶜ)
    (hBN : (boundary G X : Set V) ⊆ G.neighborSet v)
    (u : V) (hu : u ∈ boundary G X)
    (a : V) (ha : a ∈ boundary G X) (hau : a ≠ u) (hna : ¬G.Adj u a)
    (b : V) (hb : b ∈ boundary G X) (hbu : b ≠ u) (hnb : ¬G.Adj u b) : a = b := by
  classical
  by_contra hab
  let uN : G.neighborSet v := ⟨u, hBN hu⟩
  let aN : G.neighborSet v := ⟨a, hBN ha⟩
  let bN : G.neighborSet v := ⟨b, hBN hb⟩
  have hanchor : u ∉ X ∧ ∃ z ∈ X, G.Adj u z := (mem_boundary G X u).mp hu
  have hattacha : ∃ z ∈ X, G.Adj a z := ((mem_boundary G X a).mp ha).2
  have hattachb : ∃ z ∈ X, G.Adj b z := ((mem_boundary G X b).mp hb).2
  let S : Set V := insert u X
  have huS : uN.val ∈ S := Set.mem_insert _ _
  have hconn : (G.induce S).Connected := by
    obtain ⟨z, hz, huz⟩ := hanchor.2
    have hsingle := (MinorModel.refl G).connected u
    simpa only [Set.singleton_union] using
      connected_induce_union hsingle.preconnected hX.preconnected
        (Set.mem_singleton u) hz huz
  have hside : ∀ z ∈ S, z ∈ G.neighborSet v → z = uN.val := by
    intro z hz hzN
    rcases hz with hzu | hzX
    · exact hzu
    · exact False.elim (hout hzX (Or.inr hzN))
  have hvS : v ∉ S := by
    intro hh
    rcases hh with hvu | hvX
    · exact G.loopless.irrefl v (hvu.symm ▸ hBN hu)
    · exact hout hvX (Set.mem_insert _ _)
  have hcard : Fintype.card (G.neighborSet v) = 7 := by
    rw [G.card_neighborSet_eq_degree, hv]
  have hbound := CliqueStarBound.edge_bound G hG v (G.neighborSet v) (fun _ h => h)
    uN S huS hconn hside hvS (by omega)
  have hgrow := CliqueStarBound.growth_two G (G.neighborSet v) uN aN bN S
    (fun hh => hau (congrArg Subtype.val hh).symm)
    (fun hh => hbu (congrArg Subtype.val hh).symm)
    (fun hh => hab (congrArg Subtype.val hh)) hna hnb (by
      obtain ⟨z, hz, haz⟩ := hattacha
      exact ⟨z, Or.inr hz, haz.symm⟩) (by
      obtain ⟨z, hz, hbz⟩ := hattachb
      exact ⟨z, Or.inr hz, hbz.symm⟩)
  rw [hcard] at hbound
  rw [he] at hgrow
  omega

end Paper.SixCliqueBoundaryMissing

#print axioms Paper.SixCliqueBoundaryMissing.unique
