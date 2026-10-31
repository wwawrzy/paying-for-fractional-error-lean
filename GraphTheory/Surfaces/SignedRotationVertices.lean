import GraphTheory.Surfaces.SignedRotationEdges

/-! Local cyclicity identifies flag vertices with nonisolated graph vertices. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)

private theorem vertex_same_dart (d : G.Dart) (b c : Bool) :
    (pairSetoid (sideFlip (G := G)) r.cornerFlip).r (d, b) (d, c) := by
  cases b <;> cases c
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
  · exact Relation.EqvGen.rel _ _ (Or.inl rfl)
  · exact Relation.EqvGen.refl _

private theorem vertex_rotation (d : G.Dart) :
    (pairSetoid (sideFlip (G := G)) r.cornerFlip).r (d, false) (r.σ d, false) := by
  exact Relation.EqvGen.trans _ (r.σ d, true) _
    (Relation.EqvGen.rel _ _ (Or.inr rfl))
    (Relation.EqvGen.rel _ _ (Or.inl rfl))

private theorem vertex_rotation_pow (d : G.Dart) (n : ℕ) :
    (pairSetoid (sideFlip (G := G)) r.cornerFlip).r (d, false) ((r.σ ^ n) d, false) := by
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact Relation.EqvGen.trans _ _ _ ih (vertex_rotation r ((r.σ ^ n) d))

variable [Fintype V] [DecidableRel G.Adj]

theorem vertex_relation_iff (x y : Flag G) :
    (pairSetoid (sideFlip (G := G)) r.cornerFlip).r x y ↔
      x.1.toProd.1 = y.1.toProd.1 := by
  constructor
  · intro h
    induction h with
    | rel a b h =>
      rcases h with h | h
      · subst b
        rfl
      · subst b
        exact (r.cornerFlip_source a).symm
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih hj => exact ih.trans hj
  · rcases x with ⟨d, b⟩
    rcases y with ⟨e, c⟩
    intro h
    obtain ⟨n, hn⟩ := (r.cyclic d e h).exists_nat_pow_eq
    have hp := vertex_rotation_pow r d n
    rw [hn] at hp
    exact Relation.EqvGen.trans _ _ _ (vertex_same_dart r d b false)
      (Relation.EqvGen.trans _ _ _ hp (vertex_same_dart r e false c))

def vertexValue : r.Vertex → G.support :=
  Quotient.lift (fun x : Flag G => ⟨x.1.fst, ⟨x.1.snd, x.1.adj⟩⟩)
    (fun x y h => Subtype.ext ((vertex_relation_iff r x y).mp h))

theorem vertexValue_injective : Function.Injective r.vertexValue := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b h
  apply Quotient.sound
  exact (vertex_relation_iff r a b).mpr (congrArg Subtype.val h)

theorem vertexValue_surjective : Function.Surjective r.vertexValue := by
  rintro ⟨v, hv⟩
  obtain ⟨w, hw⟩ := G.mem_support.mp hv
  exact ⟨Quotient.mk _ (⟨(v, w), hw⟩, false), rfl⟩

noncomputable def vertexEquiv : r.Vertex ≃ G.support :=
  Equiv.ofBijective r.vertexValue ⟨r.vertexValue_injective, r.vertexValue_surjective⟩

theorem vertex_card : Nat.card r.Vertex = Nat.card G.support :=
  Nat.card_congr r.vertexEquiv

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.vertex_relation_iff
#print axioms SimpleGraph.SignedRotation.vertexValue_injective
#print axioms SimpleGraph.SignedRotation.vertexValue_surjective
#print axioms SimpleGraph.SignedRotation.vertex_card
