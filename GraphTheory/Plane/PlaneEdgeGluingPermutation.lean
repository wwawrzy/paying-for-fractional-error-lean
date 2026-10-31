import GraphTheory.Plane.PlaneChordCountBound
import GraphTheory.Plane.PlanePermutationDeletion

/-! # The asymmetric permutation splice underlying an edge sum -/

namespace PlaneTopology.PlaneEdgeGluingPermutation

open Equiv Equiv.Perm PlaneTopology.PlanePermutationSurgery PlaneTopology.PlaneChordCountBound

variable {α β : Type*} [DecidableEq α]

omit [DecidableEq α] in
/-- An invariant label is constant along every permutation orbit. -/
theorem sameCycle_label [Finite α] (p : Perm α) (f : α → β)
    (hf : ∀ x, f (p x) = f x) {x y : α} (hxy : p.SameCycle x y) : f x = f y := by
  have h := sameCycle_map p (Equiv.refl β) f (fun x => (hf x).symm) hxy
  exact h.eq_of_left rfl

/-- Gluing before one end and after its reverse conjugates the face permutation.
This identity is independent of any graph or Euler assumption. -/
theorem splice_face_conjugate (p t : Perm α) (a b : α)
    (ht : Function.Involutive t) :
    (swap (t a) (t b) * p * swap a b) * t =
      swap (t a) (t b) * (p * t) * (swap (t a) (t b))⁻¹ := by
  have h : swap a b * t = t * swap (t a) (t b) := by
    rw [mul_swap_eq_swap_mul, ht a, ht b]
  rw [swap_inv, mul_assoc (swap (t a) (t b) * p), h]
  simp only [mul_assoc]

/-- Nontrivial cycle types add under the disjoint sum of two permutations. -/
theorem cycleType_sumCongr [Fintype α] [Fintype β] [DecidableEq β]
    (p : Perm α) (q : Perm β) :
    Equiv.Perm.cycleType (Equiv.sumCongr p q) = p.cycleType + q.cycleType := by
  let l : Perm (α ⊕ β) := Equiv.sumCongr p (Equiv.refl β)
  let r : Perm (α ⊕ β) := Equiv.sumCongr (Equiv.refl α) q
  have hprod : l * r = Equiv.sumCongr p q := by ext x; cases x <;> rfl
  have hdis : l.Disjoint r := by
    intro x
    cases x with
    | inl a => exact Or.inr rfl
    | inr b => exact Or.inl rfl
  have hright : r.cycleType = q.cycleType := by
    have heq : r = (Equiv.sumComm β α).permCongr (Equiv.sumCongr q (Equiv.refl α)) := by
      ext x
      cases x <;> rfl
    rw [heq, cycleType_permCongr, cycleType_sumCongr_refl]
  rw [← hprod, hdis.cycleType_mul, hright]
  exact congrArg (fun s => s + q.cycleType) (cycleType_sumCongr_refl p)

/-- The full edge splice leaves the total number of faces unchanged, before
the duplicated edge is erased. -/
theorem cycleType_splice_face [Fintype α] (p t : Perm α) (a b : α)
    (ht : Function.Involutive t) :
    ((swap (t a) (t b) * p * swap a b) * t).cycleType = (p * t).cycleType := by
  rw [splice_face_conjugate p t a b ht, cycleType_conj]

/-- Joining two different orbits preserves every original orbit relation. -/
theorem sameCycle_swap_mul_preserved [Fintype α] (p : Perm α) (a b : α)
    (hnot : ¬p.SameCycle a b) {x y : α} (hxy : p.SameCycle x y) :
    (swap a b * p).SameCycle x y := by
  have hab := sameCycle_swap_mul_of_not_sameCycle p a b hnot
  apply sameCycle_of_steps p _ _ hxy
  intro z
  have hz : (swap a b * p).SameCycle z ((swap a b * p) z) := ⟨1, by simp⟩
  by_cases hza : p z = a
  · have heq : (swap a b * p) z = b := by simp [mul_apply, hza]
    exact hza.symm ▸ ((heq ▸ hz).trans hab.symm)
  · by_cases hzb : p z = b
    · have heq : (swap a b * p) z = a := by simp [mul_apply, hzb]
      exact hzb.symm ▸ ((heq ▸ hz).trans hab)
    · simpa [mul_apply, swap_apply_of_ne_of_ne hza hzb] using hz

/-- The analogous preservation law for swapping predecessors rather than successors. -/
theorem sameCycle_mul_swap_preserved [Fintype α] (p : Perm α) (a b : α)
    (hnot : ¬p.SameCycle a b) {x y : α} (hxy : p.SameCycle x y) :
    (p * swap a b).SameCycle x y := by
  rw [mul_swap_eq_swap_mul]
  apply sameCycle_swap_mul_preserved p (p a) (p b) _ hxy
  simpa only [sameCycle_apply_left, sameCycle_apply_right] using hnot

/-- Swapping predecessors of different orbits joins the chosen endpoint darts. -/
theorem sameCycle_mul_swap_ends [Fintype α] (p : Perm α) (a b : α)
    (hnot : ¬p.SameCycle a b) : (p * swap a b).SameCycle a b := by
  have hnot' : ¬p.SameCycle (p a) (p b) := by
    simpa only [sameCycle_apply_left, sameCycle_apply_right] using hnot
  have hjoin : (p * swap a b).SameCycle (p a) (p b) := by
    rw [mul_swap_eq_swap_mul]
    exact sameCycle_swap_mul_of_not_sameCycle p (p a) (p b) hnot'
  have ha := sameCycle_mul_swap_preserved p a b hnot
    (show p.SameCycle a (p a) from ⟨1, by simp⟩)
  have hb := sameCycle_mul_swap_preserved p a b hnot
    (show p.SameCycle b (p b) from ⟨1, by simp⟩)
  exact ha.trans (hjoin.trans hb.symm)

#print axioms cycleType_splice_face
#print axioms sameCycle_mul_swap_ends

end PlaneTopology.PlaneEdgeGluingPermutation
