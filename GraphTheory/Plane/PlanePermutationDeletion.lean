import GraphTheory.Plane.PlanePermutationSurgery

/-! # Exact removal of a point from a finite permutation cycle -/

namespace PlaneTopology.PlanePermutationDeletion

open Equiv Equiv.Perm

variable {α β : Type*}

/-- Collapsing some permutation steps to zero steps still preserves orbit
membership after mapping. -/
theorem sameCycle_map_of_steps [Finite α] (p : Perm α) (q : Perm β) (f : α → β)
    (hstep : ∀ x, q.SameCycle (f x) (f (p x))) {x y : α} (hxy : p.SameCycle x y) :
    q.SameCycle (f x) (f y) := by
  obtain ⟨n, rfl⟩ := hxy.exists_nat_pow_eq
  clear hxy
  induction n with
  | zero => exact SameCycle.refl _ _
  | succ n ih =>
    rw [pow_succ', mul_apply]
    exact ih.trans (hstep _)

variable [DecidableEq α]

/-- Make `a` fixed and bypass it in its previous cycle. -/
def erasePoint (p : Perm α) (a : α) : Perm α := swap a (p a) * p

/-- The removed point becomes a fixed point. -/
theorem erasePoint_fixed (p : Perm α) (a : α) : erasePoint p a a = a := by
  simp [erasePoint, mul_apply]

/-- A surviving point whose successor was removed now skips directly over it. -/
theorem erasePoint_apply_of_eq (p : Perm α) (a x : α) (hx : p x = a) :
    erasePoint p a x = p a := by
  simp [erasePoint, mul_apply, hx]

/-- Away from the removed point and its predecessor, the permutation is unchanged. -/
theorem erasePoint_apply_of_ne (p : Perm α) (a x : α) (hx : x ≠ a) (hpx : p x ≠ a) :
    erasePoint p a x = p x := by
  have hpa : p x ≠ p a := fun h => hx (p.injective h)
  simp [erasePoint, mul_apply, Equiv.swap_apply_of_ne_of_ne hpx hpa]

/-- Removing a point preserves same-cycle relations between surviving points. -/
theorem erasePoint_sameCycle [Finite α] (p : Perm α) (a : α)
    {x y : α} (hx : x ≠ a) (hy : y ≠ a) (hxy : p.SameCycle x y) :
    (erasePoint p a).SameCycle x y := by
  let f : α → α := fun z => if z = a then p a else z
  have hf : ∀ z, (erasePoint p a).SameCycle (f z) (f (p z)) := by
    intro z
    by_cases hz : z = a
    · subst z
      simp only [f, if_pos rfl]
      by_cases ha : p a = a
      · simp only [ha]
        exact SameCycle.refl _ _
      · simp only [if_neg ha]
        exact SameCycle.refl _ _
    · by_cases hpz : p z = a
      · simp only [f, if_neg hz, hpz, if_pos rfl]
        exact ⟨1, by simpa using erasePoint_apply_of_eq p a z hpz⟩
      · simp only [f, if_neg hz, if_neg hpz]
        exact ⟨1, by simpa using erasePoint_apply_of_ne p a z hz hpz⟩
  simpa only [f, if_neg hx, if_neg hy] using
    sameCycle_map_of_steps p (erasePoint p a) f hf hxy

/-- The bypass operation preserves any label already preserved by the permutation. -/
theorem erasePoint_preserves (p : Perm α) (a : α) (f : α → β)
    (hf : ∀ x, f (p x) = f x) (x : α) : f (erasePoint p a x) = f x := by
  rw [erasePoint, mul_apply,
    PlaneTopology.PlanePermutationSurgery.map_swap_eq f a (p a) (p x) (hf a).symm]
  exact hf x

/-- Reinsert the removed point immediately before its former successor. -/
theorem swap_mul_erasePoint (p : Perm α) (a : α) :
    swap a (p a) * erasePoint p a = p := by
  simp [erasePoint, ← mul_assoc]

omit [DecidableEq α] in
/-- An injective map commuting with permutations reflects orbit membership. -/
theorem sameCycle_reflect [Finite β] (p : Perm α) (q : Perm β) (f : α → β)
    (hf : Function.Injective f) (hcomm : ∀ x, f (p x) = q (f x))
    {x y : α} (hxy : q.SameCycle (f x) (f y)) : p.SameCycle x y := by
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  have hp : ∀ n : ℕ, f ((p ^ n) x) = (q ^ n) (f x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', mul_apply, hcomm, ih]
  refine ⟨(n : ℤ), ?_⟩
  rw [zpow_natCast]
  apply hf
  exact (hp n).trans hn

omit [DecidableEq α] in
/-- The left summand as an explicit subtype equivalence. -/
def leftEquiv : α ≃ {x : α ⊕ Bool // x.isLeft} where
  toFun a := ⟨Sum.inl a, rfl⟩
  invFun x := x.val.getLeft x.property
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    rcases x with ⟨x, hx⟩
    cases x <;> simp_all

omit [DecidableEq α] in
/-- A permutation fixing the right summand preserves membership in the left. -/
theorem isLeft_iff_of_fixedRight (p : Perm (α ⊕ Bool))
    (hr : ∀ b, p (Sum.inr b) = Sum.inr b) (x : α ⊕ Bool) :
    (p x).isLeft ↔ x.isLeft := by
  cases x with
  | inr b => rw [hr b]
  | inl a =>
    cases hp : p (Sum.inl a) with
    | inl b => simp
    | inr b =>
      have h := p.injective (hp.trans (hr b).symm)
      cases h

omit [DecidableEq α] in
/-- Restrict a permutation fixing both fresh points to the old left summand. -/
def restrictLeft (p : Perm (α ⊕ Bool)) (hr : ∀ b, p (Sum.inr b) = Sum.inr b) : Perm α :=
  leftEquiv.symm.permCongr (p.subtypePerm (isLeft_iff_of_fixedRight p hr))

omit [DecidableEq α] in
/-- Restriction acts exactly as the original permutation on old elements. -/
theorem restrictLeft_inl_apply (p : Perm (α ⊕ Bool))
    (hr : ∀ b, p (Sum.inr b) = Sum.inr b) (a : α) :
    Sum.inl (restrictLeft p hr a) = p (Sum.inl a) := by
  change (leftEquiv (leftEquiv.symm
    ((p.subtypePerm (isLeft_iff_of_fixedRight p hr)) (leftEquiv a)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

omit [DecidableEq α] in
/-- Extending the restriction by the two fixed points recovers the original permutation. -/
theorem sumCongr_restrictLeft (p : Perm (α ⊕ Bool))
    (hr : ∀ b, p (Sum.inr b) = Sum.inr b) :
    Equiv.sumCongr (restrictLeft p hr) (Equiv.refl Bool) = p := by
  apply Equiv.ext
  intro x
  cases x with
  | inl a => exact restrictLeft_inl_apply p hr a
  | inr b => exact (hr b).symm

omit [DecidableEq α] in
/-- Orbit membership in the fixed-right permutation descends to its restriction. -/
theorem restrictLeft_sameCycle [Finite α] (p : Perm (α ⊕ Bool))
    (hr : ∀ b, p (Sum.inr b) = Sum.inr b) {a b : α}
    (hab : p.SameCycle (Sum.inl a) (Sum.inl b)) :
    (restrictLeft p hr).SameCycle a b :=
  sameCycle_reflect (restrictLeft p hr) p Sum.inl Sum.inl_injective
    (restrictLeft_inl_apply p hr) hab

/-- Collapse the two chord darts onto their old facial successors. -/
def chordCollapse (a b : α) : α ⊕ Bool → α := Sum.elim id (fun c => if c then a else b)

/-- If the cut corners are cofacial, collapsing the inserted chord preserves
every facial orbit relation. Thus deleting the chord really merges its faces. -/
theorem sameCycle_chordPerm_collapse [Finite α] (p : Perm α) (a b : α)
    (hne : a ≠ b) (hab : p.SameCycle a b) {x y : α ⊕ Bool}
    (hxy : (PlaneTopology.PlanePermutationSurgery.chordPerm p a b).SameCycle x y) :
    p.SameCycle (chordCollapse a b x) (chordCollapse a b y) := by
  apply sameCycle_map_of_steps _ p (chordCollapse a b) _ hxy
  intro z
  cases z with
  | inl z =>
    have hstep : p.SameCycle z (p z) := ⟨1, by simp⟩
    by_cases hza : p z = a
    · have hz : p.SameCycle z b := hstep.trans (hza.symm ▸ hab)
      simpa [PlaneTopology.PlanePermutationSurgery.chordPerm, mul_apply,
        Equiv.swap_apply_def, hza, hne, chordCollapse] using hz
    · by_cases hzb : p z = b
      · have hz : p.SameCycle z a := hstep.trans (hzb.symm ▸ hab.symm)
        simpa [PlaneTopology.PlanePermutationSurgery.chordPerm, mul_apply,
          Equiv.swap_apply_def, hza, hzb, hne, Ne.symm hne, chordCollapse] using hz
      · simpa [PlaneTopology.PlanePermutationSurgery.chordPerm, mul_apply,
          Equiv.swap_apply_def, hza, hzb, chordCollapse] using hstep
  | inr z =>
    cases z <;> simp [PlaneTopology.PlanePermutationSurgery.chordPerm, mul_apply,
      Equiv.swap_apply_def, hne, chordCollapse, SameCycle.refl]

end PlaneTopology.PlanePermutationDeletion

#print axioms PlaneTopology.PlanePermutationDeletion.erasePoint_sameCycle
#print axioms PlaneTopology.PlanePermutationDeletion.sameCycle_chordPerm_collapse
