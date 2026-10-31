import GraphTheory.Surfaces.SignedRotationRestrictionFlags

/-! A face path cannot leave an adjacency-closed vertex set. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G) (s : Set V)
  (hs : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)

include hs in
theorem face_relation_mem_iff {x y : Flag G}
    (h : (pairSetoid r.edgeFlip r.cornerFlip).r x y) :
    x.1.fst ∈ s ↔ y.1.fst ∈ s := by
  induction h with
  | rel a b h =>
    rcases h with h | h
    · subst b
      exact ⟨fun ha => hs ha a.1.adj, fun hb => hs hb a.1.adj.symm⟩
    · subst b
      rw [r.cornerFlip_source]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih hj => exact ih.trans hj

def pullFlag (x : Flag G) (hx : x.1.fst ∈ s) : Flag (G.induce s) :=
  ((closedDartEquiv s hs).symm ⟨x.1, hx⟩, x.2)

theorem include_pullFlag (x : Flag G) (hx : x.1.fst ∈ s) :
    includeFlag s hs (pullFlag s hs x hx) = x := by
  rcases x with ⟨d, b⟩
  simp [includeFlag, pullFlag]

theorem pullFlag_include (x : Flag (G.induce s)) :
    pullFlag s hs (includeFlag s hs x) x.1.fst.property = x := by
  apply includeFlag_injective s hs
  exact include_pullFlag s hs _ _

theorem pullFlag_face_relation {x y : Flag G}
    (h : (pairSetoid r.edgeFlip r.cornerFlip).r x y)
    (hx : x.1.fst ∈ s) (hy : y.1.fst ∈ s) :
    (pairSetoid (r.restrictClosed s hs).edgeFlip (r.restrictClosed s hs).cornerFlip).r
      (pullFlag s hs x hx) (pullFlag s hs y hy) := by
  induction h with
  | rel a b h =>
    apply Relation.EqvGen.rel
    rcases h with h | h
    · left
      apply includeFlag_injective s hs
      rw [r.includeFlag_edgeFlip, include_pullFlag, include_pullFlag, h]
    · right
      apply includeFlag_injective s hs
      rw [r.includeFlag_cornerFlip, include_pullFlag, include_pullFlag, h]
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ (ih hy hx)
  | trans a b c hab hbc ih hj =>
    have hb := (r.face_relation_mem_iff s hs hab).mp hx
    exact Relation.EqvGen.trans _ _ _ (ih hx hb) (hj hb hy)

theorem includeFace_injective : Function.Injective (r.includeFace s hs) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro x y h
  apply Quotient.sound
  have hp := r.pullFlag_face_relation s hs (Quotient.exact h)
    x.1.fst.property y.1.fst.property
  simpa only [pullFlag_include] using hp

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.face_relation_mem_iff
#print axioms SimpleGraph.SignedRotation.includeFace_injective
