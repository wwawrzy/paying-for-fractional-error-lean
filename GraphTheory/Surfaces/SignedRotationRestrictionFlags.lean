import GraphTheory.Surfaces.SignedRotationRestriction

/-! The flag inclusion of an adjacency-closed induced graph respects all three
surface involutions, and therefore maps its face classes into the original map. -/
namespace SimpleGraph.SignedRotation

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (r : SignedRotation G) (s : Set V)
  (hs : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s)

def includeFlag (x : Flag (G.induce s)) : Flag G :=
  ((closedDartEquiv s hs x.1).val, x.2)

theorem includeFlag_injective : Function.Injective (includeFlag s hs) := by
  rintro ⟨d, b⟩ ⟨e, c⟩ h
  apply Prod.ext
  · apply (closedDartEquiv s hs).injective
    exact Subtype.ext (congrArg Prod.fst h)
  · exact congrArg (fun z : Flag G => z.2) h

theorem includeFlag_edgeFlip (x : Flag (G.induce s)) :
    includeFlag s hs ((r.restrictClosed s hs).edgeFlip x) =
      r.edgeFlip (includeFlag s hs x) := rfl

theorem includeFlag_sideFlip (x : Flag (G.induce s)) :
    includeFlag s hs (sideFlip x) = sideFlip (includeFlag s hs x) := rfl

theorem includeFlag_cornerFlip (x : Flag (G.induce s)) :
    includeFlag s hs ((r.restrictClosed s hs).cornerFlip x) =
      r.cornerFlip (includeFlag s hs x) := by
  rcases x with ⟨d, b⟩
  cases b <;> simp only [cornerFlip, Bool.false_eq_true, if_false, if_true]
  · exact Prod.ext (r.closedRotation_dart s hs d) rfl
  · exact Prod.ext (r.closedRotation_symm_dart s hs d) rfl

theorem includeFlag_face_relation {x y : Flag (G.induce s)}
    (h : (pairSetoid (r.restrictClosed s hs).edgeFlip
      (r.restrictClosed s hs).cornerFlip).r x y) :
    (pairSetoid r.edgeFlip r.cornerFlip).r (includeFlag s hs x) (includeFlag s hs y) := by
  induction h with
  | rel a b h =>
    apply Relation.EqvGen.rel
    rcases h with h | h
    · left
      rw [← r.includeFlag_edgeFlip, h]
    · right
      rw [← r.includeFlag_cornerFlip, h]
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih hj => exact Relation.EqvGen.trans _ _ _ ih hj

def includeFace : (r.restrictClosed s hs).Face → r.Face :=
  Quotient.lift (fun x => Quotient.mk _ (includeFlag s hs x))
    (fun _ _ h => Quotient.sound (r.includeFlag_face_relation s hs h))

end SimpleGraph.SignedRotation

#print axioms SimpleGraph.SignedRotation.includeFlag_injective
#print axioms SimpleGraph.SignedRotation.includeFlag_cornerFlip
#print axioms SimpleGraph.SignedRotation.includeFace
