import GraphTheory.Surfaces.SignedRotationFaceFlags
import GraphTheory.Surfaces.SignedRotationDeletionSteps
import GraphTheory.Surfaces.SignedRotationDeletionFreshCorners
namespace SimpleGraph.SignedRotation
open PlaneTopology.PlaneEdgeInsertion PlaneTopology.PlaneEdgeDeletion
variable {V : Type*} (G : SimpleGraph V) (u v : V)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable (hne : u ≠ v) (hmiss : ¬ G.Adj u v)
theorem deleteAddedEdge_reverse_step_cases (r : SignedRotation (G ⊔ edge u v)) (d : G.Dart) :
    ∃ e : G.Dart, (deleteAddedEdge G u v hne hmiss r).σ.symm d = e ∧
      (pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl e) = Sum.inl d ∨
       ∃ b : Bool,
         pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inl e) = Sum.inr b ∧
         pulledPerm G u v hne hmiss r.toRotationSystem (Sum.inr b) = Sum.inl d) := by
  let q := (deleteAddedEdge G u v hne hmiss r).σ
  obtain ⟨e, he, hc⟩ := deleteAddedEdge_step_cases G u v hne hmiss r (q.symm d)
  have hed : e = d := by
    change q (q.symm d) = e at he
    simpa using he.symm
  subst e
  refine ⟨q.symm d, rfl, ?_⟩
  simpa only [← show q = (deleteAddedEdge G u v hne hmiss r).σ from rfl, Equiv.apply_symm_apply] using hc
/-- Every deleted corner is unchanged or bypasses the two sides of one
removed dart. The output flag is the actual corner of the deleted rotation. -/
theorem deleteAddedEdge_corner_cases (r : SignedRotation (G ⊔ edge u v)) (x : Flag G) :
    let y := (deleteAddedEdge G u v hne hmiss r).cornerFlip x
    r.cornerFlip (augmentedDart G u v hne (Sum.inl x.1), x.2) =
        (augmentedDart G u v hne (Sum.inl y.1), y.2) ∨
    ∃ b c : Bool,
      r.cornerFlip (augmentedDart G u v hne (Sum.inl x.1), x.2) =
        (augmentedDart G u v hne (Sum.inr b), c) ∧
      r.cornerFlip (augmentedDart G u v hne (Sum.inr b), !c) =
        (augmentedDart G u v hne (Sum.inl y.1), y.2) := by
  have hs (d e : G.Dart ⊕ Bool)
      (h : pulledPerm G u v hne hmiss r.toRotationSystem d = e) :
      r.σ (augmentedDart G u v hne d) = augmentedDart G u v hne e := by
    have hh := congrArg (augmentedDartEquiv G u v hne hmiss) h
    simpa only [pulledPerm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply, augmentedDartEquiv_apply] using hh
  rcases x with ⟨d, c⟩
  cases c
  · obtain ⟨e, he, hc⟩ := deleteAddedEdge_step_cases G u v hne hmiss r d
    simp only [cornerFlip, Bool.false_eq_true, ↓reduceIte, he]
    rcases hc with hc | ⟨b, h₁, h₂⟩
    · left; exact Prod.ext (hs _ _ hc) rfl
    · right
      exact ⟨b, true, Prod.ext (hs _ _ h₁) rfl,
        by simpa only [Bool.not_true, cornerFlip, Bool.false_eq_true, ↓reduceIte] using
          (Prod.ext (hs _ _ h₂) (rfl : true = true))⟩
  · obtain ⟨e, he, hc⟩ := deleteAddedEdge_reverse_step_cases G u v hne hmiss r d
    simp only [cornerFlip, ↓reduceIte, he]
    have hi (a b : (G ⊔ edge u v).Dart) (h : r.σ a = b) : r.σ.symm b = a := by
      rw [← h, Equiv.symm_apply_apply]
    rcases hc with hc | ⟨b, h₁, h₂⟩
    · left; exact Prod.ext (hi _ _ (hs _ _ hc)) rfl
    · right
      refine ⟨b, false, Prod.ext (hi _ _ (hs _ _ h₂)) rfl, ?_⟩
      simpa only [Bool.not_false, cornerFlip, ↓reduceIte] using
        (Prod.ext (hi _ _ (hs _ _ h₁)) (rfl : false = false))

def deletionFaceSetoid (r : SignedRotation (G ⊔ edge u v)) : Setoid (Flag (G ⊔ edge u v)) :=
  Relation.EqvGen.setoid (fun x y => r.edgeFlip x = y ∨ r.cornerFlip x = y ∨
    ∃ b c : Bool, x = (augmentedDart G u v hne (Sum.inr b), c) ∧
      y = (augmentedDart G u v hne (Sum.inr b), !c))

def survivingFlag (x : Flag G) : Flag (G ⊔ edge u v) :=
  (augmentedDart G u v hne (Sum.inl x.1), x.2)

theorem deletion_corner_relation (r : SignedRotation (G ⊔ edge u v)) (x : Flag G) :
    (deletionFaceSetoid G u v hne r).r (survivingFlag G u v hne x)
      (survivingFlag G u v hne ((deleteAddedEdge G u v hne hmiss r).cornerFlip x)) := by
  rcases deleteAddedEdge_corner_cases G u v hne hmiss r x with h | ⟨b,c,h₁,h₂⟩
  · exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl h))
  · have hleft : (deletionFaceSetoid G u v hne r).r (survivingFlag G u v hne x)
        (augmentedDart G u v hne (Sum.inr b), c) :=
      Relation.EqvGen.rel _ _ (Or.inr (Or.inl h₁))
    have hmid : (deletionFaceSetoid G u v hne r).r
        (augmentedDart G u v hne (Sum.inr b), c)
        (augmentedDart G u v hne (Sum.inr b), !c) :=
      Relation.EqvGen.rel _ _ (Or.inr (Or.inr ⟨b,c,rfl,rfl⟩))
    have hright : (deletionFaceSetoid G u v hne r).r
        (augmentedDart G u v hne (Sum.inr b), !c)
        (survivingFlag G u v hne ((deleteAddedEdge G u v hne hmiss r).cornerFlip x)) :=
      Relation.EqvGen.rel _ _ (Or.inr (Or.inl h₂))
    exact Relation.EqvGen.trans _ _ _ hleft (Relation.EqvGen.trans _ _ _ hmid hright)

theorem deletion_face_relation (r : SignedRotation (G ⊔ edge u v)) {x y : Flag G}
    (h : (pairSetoid (deleteAddedEdge G u v hne hmiss r).edgeFlip
      (deleteAddedEdge G u v hne hmiss r).cornerFlip).r x y) :
    (deletionFaceSetoid G u v hne r).r (survivingFlag G u v hne x)
      (survivingFlag G u v hne y) := by
  induction h with
  | rel a b h =>
    rcases h with h | h
    · subst b
      apply Relation.EqvGen.rel
      left
      exact (deleteAddedEdge_edgeFlip G u v hne hmiss r a).symm
    · subst b
      exact deletion_corner_relation G u v hne hmiss r a
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih hj => exact Relation.EqvGen.trans _ _ _ ih hj

noncomputable def deletionFaceMap (r : SignedRotation (G ⊔ edge u v)) :
    (deleteAddedEdge G u v hne hmiss r).Face → Quotient (deletionFaceSetoid G u v hne r) :=
  Quotient.map (survivingFlag G u v hne) (fun _ _ h => deletion_face_relation G u v hne hmiss r h)

theorem deletionFaceMap_surjective (r : SignedRotation (G ⊔ edge u v))
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Function.Surjective (deletionFaceMap G u v hne hmiss r) := by
  intro z
  refine Quotient.inductionOn z ?_
  rintro ⟨d,c⟩
  let E := augmentedDartEquiv G u v hne hmiss
  cases ht : E.symm d with
  | inl f =>
    have hd : d = augmentedDart G u v hne (Sum.inl f) := by
      have h := congrArg E ht
      simpa only [Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
    subst d
    exact ⟨Quotient.mk _ (f,c), rfl⟩
  | inr b =>
    have hd : d = augmentedDart G u v hne (Sum.inr b) := by
      have h := congrArg E ht
      simpa only [Equiv.apply_symm_apply, augmentedDartEquiv_apply] using h
    subst d
    obtain ⟨f,hf⟩ := hends b
    obtain ⟨g,hg⟩ := fresh_corner_survives G u v hne hmiss r b c f hf
    refine ⟨Quotient.mk _ (g,!c), ?_⟩
    apply Quotient.sound
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Or.inr (Or.inl hg)))

theorem deletion_surgery_classes_le_faces (r : SignedRotation (G ⊔ edge u v))
    (hends : ∀ b : Bool, ∃ d : G.Dart,
      (augmentedDart G u v hne (Sum.inr b)).fst = d.fst) :
    Nat.card (Quotient (deletionFaceSetoid G u v hne r)) ≤
      Nat.card (deleteAddedEdge G u v hne hmiss r).Face := by
  letI : Finite (deleteAddedEdge G u v hne hmiss r).Face :=
    Finite.of_surjective (Quotient.mk _ : Flag G → (deleteAddedEdge G u v hne hmiss r).Face)
      (fun q => Quotient.exists_rep q)
  exact Nat.card_le_card_of_surjective _ (deletionFaceMap_surjective G u v hne hmiss r hends)

theorem removed_flag_faces (r : SignedRotation (G ⊔ edge u v)) (b c : Bool) :
    r.faceOf (augmentedDart G u v hne (Sum.inr b), c) =
        r.faceOf (augmentedDart G u v hne (Sum.inr false), false) ∨
    r.faceOf (augmentedDart G u v hne (Sum.inr b), c) =
        r.faceOf (augmentedDart G u v hne (Sum.inr false), true) := by
  cases b
  · cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  · let j := if r.twist (augmentedDart G u v hne (Sum.inr true)) then c else !c
    have h : r.faceOf (augmentedDart G u v hne (Sum.inr true), c) =
        r.faceOf (augmentedDart G u v hne (Sum.inr false), j) := by
      exact (r.faceOf_edgeFlip (augmentedDart G u v hne (Sum.inr true), c)).symm
    cases hj : j
    · exact Or.inl (by simpa only [hj] using h)
    · exact Or.inr (by simpa only [hj] using h)

end SimpleGraph.SignedRotation




