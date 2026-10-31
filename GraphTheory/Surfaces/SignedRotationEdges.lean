import GraphTheory.Surfaces.SignedRotation

/-! The flag-edge quotient is exactly the original graph's edge set. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)

private theorem same_dart (d : G.Dart) (b c : Bool) :
    (pairSetoid r.edgeFlip (sideFlip (G := G))).r (d, b) (d, c) := by
  cases b <;> cases c
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  · exact Relation.EqvGen.rel _ _ (Or.inr rfl)
  · exact Relation.EqvGen.refl _

theorem edge_relation_iff (x y : Flag G) :
    (pairSetoid r.edgeFlip (sideFlip (G := G))).r x y ↔ x.1.edge = y.1.edge := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
      rcases h with h | h
      · subst b
        simp [edgeFlip]
      · subst b
        rfl
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih hj => exact ih.trans hj
  · rcases x with ⟨d, b⟩
    rcases y with ⟨e, c⟩
    intro h
    rcases (dart_edge_eq_iff d e).mp h with h | h
    · subst d
      exact same_dart r e b c
    · subst d
      apply Relation.EqvGen.trans _ (r.edgeFlip (e.symm, b)) _
        (Relation.EqvGen.rel _ _ (Or.inl rfl))
      simpa [edgeFlip] using
        same_dart r e (if r.twist e.symm then b else !b) c

def edgeValue : r.Edge → G.edgeSet :=
  Quotient.lift (fun x : Flag G => ⟨x.1.edge, x.1.edge_mem⟩)
    (fun x y h => Subtype.ext ((edge_relation_iff r x y).mp h))

theorem edgeValue_injective : Function.Injective r.edgeValue := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  apply Quotient.sound
  exact (edge_relation_iff r a b).mpr (congrArg Subtype.val h)

theorem edgeValue_surjective : Function.Surjective r.edgeValue := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | _ a b =>
    exact ⟨Quotient.mk _ (⟨(a, b), he⟩, false), rfl⟩

noncomputable def edgeEquiv : r.Edge ≃ G.edgeSet :=
  Equiv.ofBijective r.edgeValue ⟨r.edgeValue_injective, r.edgeValue_surjective⟩

theorem edge_card [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    Nat.card r.Edge = G.edgeFinset.card := by
  rw [Nat.card_congr r.edgeEquiv, Nat.card_eq_fintype_card, G.card_edgeSet]

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.edge_relation_iff
#print axioms SimpleGraph.SignedRotation.edgeValue_injective
#print axioms SimpleGraph.SignedRotation.edgeValue_surjective
#print axioms SimpleGraph.SignedRotation.edge_card
