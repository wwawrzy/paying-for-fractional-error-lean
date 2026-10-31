import GraphTheory.Plane.PlaneEdgeInsertion
import GraphTheory.Plane.PlaneLeafInsertion

/-!
# Actual face incidences retained by chord insertion

The two sides of an inserted chord are tracked through the checked actual
facial permutation. In particular, cofaciality with the chord's first endpoint
survives, even though the old face may split into two different faces.
-/

namespace PlaneTopology.PlaneChordFaces

open Equiv Equiv.Perm SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap
open PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneEdgeInsertion

variable {α : Type*} [DecidableEq α]

/-- Away from the two cut positions, the old facial successor is unchanged. -/
theorem chordPerm_apply_old (p : Perm α) (a b x : α)
    (hxa : p x ≠ a) (hxb : p x ≠ b) :
    chordPerm p a b (Sum.inl x) = Sum.inl (p x) := by
  simp [chordPerm, mul_apply, Equiv.swap_apply_def, hxa, hxb]

/-- The new dart oriented from the first endpoint enters the second old arc. -/
theorem chordPerm_apply_false (p : Perm α) (a b : α) :
    chordPerm p a b (Sum.inr false) = Sum.inl b := by
  simp [chordPerm, mul_apply, Equiv.swap_apply_def]

/-- The reverse new dart enters the first old arc. -/
theorem chordPerm_apply_true (p : Perm α) (a b : α) (hab : a ≠ b) :
    chordPerm p a b (Sum.inr true) = Sum.inl a := by
  simp [chordPerm, mul_apply, Equiv.swap_apply_def, hab]

/-- A concrete old arc avoiding both cut positions is preserved step for
step, not merely as a numerical face-count statement. -/
theorem chordPerm_pow_old (p : Perm α) (a b x : α) (n : ℕ)
    (havoid : ∀ i < n, (p ^ (i + 1)) x ≠ a ∧ (p ^ (i + 1)) x ≠ b) :
    (chordPerm p a b ^ n) (Sum.inl x) = Sum.inl ((p ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := havoid n (Nat.lt_succ_self n)
    have hprev := ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))
    rw [pow_succ', mul_apply, hprev]
    simpa only [pow_succ', mul_apply] using
      chordPerm_apply_old p a b ((p ^ n) x)
        (by simpa only [pow_succ', mul_apply] using hn.1)
        (by simpa only [pow_succ', mul_apply] using hn.2)

/-- Exact first-side arc incidence: after the reverse new dart, each old
position before the next cut is on that same new face. -/
theorem chordPerm_sameCycle_true_of_arc (p : Perm α) (a b : α) (hab : a ≠ b)
    (n : ℕ) (havoid : ∀ i < n, (p ^ (i + 1)) a ≠ a ∧ (p ^ (i + 1)) a ≠ b) :
    (chordPerm p a b).SameCycle (Sum.inr true) (Sum.inl ((p ^ n) a)) := by
  refine ⟨(n + 1 : ℕ), ?_⟩
  change (chordPerm p a b ^ (n + 1)) (Sum.inr true) = _
  rw [pow_succ, mul_apply, chordPerm_apply_true p a b hab]
  exact chordPerm_pow_old p a b a n havoid

/-- Exact second-side arc incidence for the forward new dart. -/
theorem chordPerm_sameCycle_false_of_arc (p : Perm α) (a b : α)
    (n : ℕ) (havoid : ∀ i < n, (p ^ (i + 1)) b ≠ a ∧ (p ^ (i + 1)) b ≠ b) :
    (chordPerm p a b).SameCycle (Sum.inr false) (Sum.inl ((p ^ n) b)) := by
  refine ⟨(n + 1 : ℕ), ?_⟩
  change (chordPerm p a b ^ (n + 1)) (Sum.inr false) = _
  rw [pow_succ, mul_apply, chordPerm_apply_false]
  exact chordPerm_pow_old p a b b n havoid

/-- Every old cofacial incidence is retained either by its original witness,
or by one of the two witnesses at the first endpoint of the new chord. -/
theorem chordPerm_sameCycle_cover [Finite α] (p : Perm α) (a b c x : α)
    (hcx : p.SameCycle c x) :
    (chordPerm p a b).SameCycle (Sum.inl c) (Sum.inl x) ∨
      (chordPerm p a b).SameCycle (Sum.inl a) (Sum.inl x) ∨
        (chordPerm p a b).SameCycle (Sum.inr false) (Sum.inl x) := by
  obtain ⟨n, rfl⟩ := hcx.exists_nat_pow_eq
  clear hcx
  induction n with
  | zero => exact Or.inl (SameCycle.refl _ _)
  | succ n ih =>
    rw [pow_succ', mul_apply]
    by_cases ha : p ((p ^ n) c) = a
    · exact Or.inr (Or.inl (ha ▸ SameCycle.refl _ _))
    · by_cases hb : p ((p ^ n) c) = b
      · right
        right
        rw [hb]
        exact ⟨1, by simpa using chordPerm_apply_false p a b⟩
      · have hstep : (chordPerm p a b).SameCycle (Sum.inl ((p ^ n) c))
            (Sum.inl (p ((p ^ n) c))) :=
          ⟨1, by simpa using chordPerm_apply_old p a b ((p ^ n) c) ha hb⟩
        rcases ih with h | h | h
        · exact Or.inl (h.trans hstep)
        · exact Or.inr (Or.inl (h.trans hstep))
        · exact Or.inr (Or.inr (h.trans hstep))

variable {V : Type*} (G : SimpleGraph V)

/-- Two vertices have actual outgoing darts belonging to one actual face. -/
def CoFacial (r : G.RotationSystem) (u v : V) : Prop :=
  ∃ d e : G.Dart, d.fst = u ∧ e.fst = v ∧ r.SameFace d e

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A chord changes an old face step only when it enters one of the two
endpoint vertices. This is the geometric arc-retention interface. -/
theorem insertedRotation_facePerm_old_of_target_ne (r : G.RotationSystem) (u v : V)
    (d e : G.Dart) (hne : u ≠ v) (hmiss : ¬G.Adj u v)
    (hd : d.fst = u) (he : e.fst = v) (x : G.Dart)
    (hxu : x.snd ≠ u) (hxv : x.snd ≠ v) :
    (insertedRotation G u v r d e hne hmiss hd he).facePerm
        (augmentedDart G u v hne (Sum.inl x)) =
      augmentedDart G u v hne (Sum.inl (r.facePerm x)) := by
  have hxd : r.facePerm x ≠ d := by
    intro h
    apply hxu
    rw [← r.facePerm_source x, h, hd]
  have hxe : r.facePerm x ≠ e := by
    intro h
    apply hxv
    rw [← r.facePerm_source x, h, he]
  change (insertedRotation G u v r d e hne hmiss hd he).facePerm
    (augmentedDartEquiv G u v hne hmiss (Sum.inl x)) = _
  rw [insertedRotation_facePerm, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    chordPerm_apply_old r.facePerm d e x hxd hxe]
  rfl

omit [Fintype V] [DecidableRel G.Adj] in
/-- Any finite old facial arc whose internal successor vertices avoid the
two chord endpoints remains an exact arc of the actual inserted map. -/
theorem insertedRotation_facePerm_pow_old (r : G.RotationSystem) (u v : V)
    (d e : G.Dart) (hne : u ≠ v) (hmiss : ¬G.Adj u v)
    (hd : d.fst = u) (he : e.fst = v) (x : G.Dart) (n : ℕ)
    (havoid : ∀ i < n, ((r.facePerm ^ i) x).snd ≠ u ∧
      ((r.facePerm ^ i) x).snd ≠ v) :
    ((insertedRotation G u v r d e hne hmiss hd he).facePerm ^ n)
        (augmentedDart G u v hne (Sum.inl x)) =
      augmentedDart G u v hne (Sum.inl ((r.facePerm ^ n) x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := havoid n (Nat.lt_succ_self n)
    rw [pow_succ', mul_apply, ih (fun i hi => havoid i (Nat.lt_succ_of_lt hi))]
    simpa only [pow_succ', mul_apply] using
      insertedRotation_facePerm_old_of_target_ne G r u v d e hne hmiss hd he
        ((r.facePerm ^ n) x) hn.1 hn.2

/-- Transport the face-coverage statement through the real augmented graph
dart equivalence. -/
theorem insertedRotation_sameFace_cover (r : G.RotationSystem) (u v : V)
    (d e : G.Dart) (hne : u ≠ v) (hmiss : ¬G.Adj u v)
    (hd : d.fst = u) (he : e.fst = v) (c x : G.Dart) (hcx : r.SameFace c x) :
    let r' := insertedRotation G u v r d e hne hmiss hd he
    let E := augmentedDart G u v hne
    r'.SameFace (E (Sum.inl c)) (E (Sum.inl x)) ∨
      r'.SameFace (E (Sum.inl d)) (E (Sum.inl x)) ∨
        r'.SameFace (E (Sum.inr false)) (E (Sum.inl x)) := by
  dsimp only
  have h := chordPerm_sameCycle_cover r.facePerm d e c x hcx
  have htransport (s t : G.Dart ⊕ Bool)
      (hst : (chordPerm r.facePerm d e).SameCycle s t) :
      (insertedRotation G u v r d e hne hmiss hd he).SameFace
        (augmentedDart G u v hne s) (augmentedDart G u v hne t) := by
    change (insertedRotation G u v r d e hne hmiss hd he).facePerm.SameCycle
      (augmentedDartEquiv G u v hne hmiss s) (augmentedDartEquiv G u v hne hmiss t)
    rw [insertedRotation_facePerm]
    exact sameCycle_map _ _ (augmentedDartEquiv G u v hne hmiss)
      (fun _ => by simp) hst
  rcases h with h | h | h
  · exact Or.inl (htransport _ _ h)
  · exact Or.inr (Or.inl (htransport _ _ h))
  · exact Or.inr (Or.inr (htransport _ _ h))

/-- Every vertex formerly cofacial with the first endpoint remains cofacial
with it after inserting the chord. The witnessing face may change. -/
theorem coFacial_insertedRotation (r : G.RotationSystem) (u v : V)
    (d e : G.Dart) (hne : u ≠ v) (hmiss : ¬G.Adj u v)
    (hd : d.fst = u) (he : e.fst = v) (x : V) (hx : CoFacial G r u x) :
    CoFacial (G ⊔ edge u v) (insertedRotation G u v r d e hne hmiss hd he) u x := by
  obtain ⟨c, f, hc, hf, hcf⟩ := hx
  rcases insertedRotation_sameFace_cover G r u v d e hne hmiss hd he c f hcf with h | h | h
  · exact ⟨augmentedDart G u v hne (Sum.inl c),
      augmentedDart G u v hne (Sum.inl f), hc, hf, h⟩
  · exact ⟨augmentedDart G u v hne (Sum.inl d),
      augmentedDart G u v hne (Sum.inl f), hd, hf, h⟩
  · exact ⟨augmentedDart G u v hne (Sum.inr false),
      augmentedDart G u v hne (Sum.inl f), rfl, hf, h⟩

#print axioms chordPerm_sameCycle_cover
#print axioms coFacial_insertedRotation
#print axioms insertedRotation_facePerm_pow_old

end PlaneTopology.PlaneChordFaces
