import GraphTheory.Plane.PlaneChordCountBound
import GraphTheory.Plane.PlanePermutationDeletion

/-!
# The chord face-count increase characterizes cofacial corners

This converse supplies the actual common face exposed by edge deletion.
The proof reflects orbit membership through the two fixed-point insertions.
-/

namespace PlaneTopology.PlaneChordCountExact

open Equiv Equiv.Perm PlaneTopology.PlanePermutationSurgery PlaneTopology.PlanePermutationDeletion
  PlaneTopology.PlaneChordCountBound

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Inserting a fixed point cannot join two previously distinct old orbits. -/
theorem sameCycle_of_swap_mul_of_fixed (p : Perm α) (a b : α) (hb : p b = b)
    {x y : α} (hx : x ≠ b) (hy : y ≠ b)
    (hxy : (swap a b * p).SameCycle x y) : p.SameCycle x y := by
  have h := erasePoint_sameCycle (swap a b * p) b hx hy hxy
  have heq : erasePoint (swap a b * p) b = p := by
    unfold erasePoint
    rw [mul_apply, hb, swap_apply_right, swap_comm b a]
    simp [← mul_assoc]
  rwa [heq] at h

/-- If the actual number of facial cycles increases by one, the two old
corners were on one actual old face, rather than on two distinct faces. -/
theorem sameCycle_of_cycleType_card_chordPerm (p : Perm α) (a b : α)
    (hab : a ≠ b) (ha : p a ≠ a) (hb : p b ≠ b)
    (hcount : (chordPerm p a b).cycleType.card = p.cycleType.card + 1) :
    p.SameCycle a b := by
  classical
  let p₀ : Perm (α ⊕ Bool) := Equiv.sumCongr p (Equiv.refl Bool)
  let p₁ := swap (Sum.inl a) (Sum.inr false) * p₀
  let p₂ := swap (Sum.inl b) (Sum.inr true) * p₁
  have hp₀N : p₀ (Sum.inr false) = Sum.inr false := rfl
  have hp₀a : p₀ (Sum.inl a) ≠ Sum.inl a := by simpa [p₀] using ha
  have hp₁M : p₁ (Sum.inr true) = Sum.inr true := by
    simp [p₁, p₀, mul_apply, Equiv.swap_apply_def]
  have hp₁b : p₁ (Sum.inl b) ≠ Sum.inl b := by
    by_cases hpa : p b = a <;> simp_all [p₁, p₀, mul_apply, Equiv.swap_apply_def]
  have hp₁N : p₁ (Sum.inr false) = Sum.inl a := by simp [p₁, p₀, mul_apply]
  have hp₂N : p₂ (Sum.inr false) = Sum.inl a := by
    simp [p₂, mul_apply, hp₁N, Equiv.swap_apply_def, hab]
  have hp₂M : p₂ (Sum.inr true) = Sum.inl b := by simp [p₂, mul_apply, hp₁M]
  have hp₂aa : p₂ (Sum.inl a) ≠ Sum.inl a := by
    intro h
    have := p₂.injective (h.trans hp₂N.symm)
    contradiction
  have hp₂bb : p₂ (Sum.inl b) ≠ Sum.inl b := by
    intro h
    have := p₂.injective (h.trans hp₂M.symm)
    contradiction
  have hcount₀ : p₀.cycleType.card = p.cycleType.card := by
    rw [cycleType_sumCongr_refl (β := Bool)]
  have hcount₁ : p₁.cycleType.card = p₀.cycleType.card :=
    cycleType_card_swap_mul_of_fixed p₀ _ _ hp₀a hp₀N
  have hcount₂ : p₂.cycleType.card = p₁.cycleType.card :=
    cycleType_card_swap_mul_of_fixed p₁ _ _ hp₁b hp₁M
  rw [chordPerm_factorization p a b hab] at hcount
  change (swap (Sum.inl a) (Sum.inl b) * p₂).cycleType.card = _ at hcount
  have hcycle₂ : p₂.SameCycle (Sum.inl a) (Sum.inl b) := by
    by_contra hnot
    have hm := cycleType_card_swap_mul_of_not_sameCycle p₂ _ _ hnot hp₂aa hp₂bb
    rw [hcount₂, hcount₁, hcount₀] at hm
    omega
  have hcycle₁ : p₁.SameCycle (Sum.inl a) (Sum.inl b) :=
    sameCycle_of_swap_mul_of_fixed p₁ _ _ hp₁M (by simp) (by simp) hcycle₂
  have hcycle₀ : p₀.SameCycle (Sum.inl a) (Sum.inl b) :=
    sameCycle_of_swap_mul_of_fixed p₀ _ _ hp₀N (by simp) (by simp) hcycle₁
  exact sameCycle_reflect p p₀ Sum.inl Sum.inl_injective (fun _ => rfl) hcycle₀

/-- Exact cofaciality criterion for the +1 chord face-count case. -/
theorem cycleType_card_chordPerm_eq_add_one_iff (p : Perm α) (a b : α)
    (hab : a ≠ b) (ha : p a ≠ a) (hb : p b ≠ b) :
    (chordPerm p a b).cycleType.card = p.cycleType.card + 1 ↔ p.SameCycle a b :=
  ⟨sameCycle_of_cycleType_card_chordPerm p a b hab ha hb,
    fun h => cycleType_card_chordPerm p a b hab h ha⟩

#print axioms sameCycle_of_swap_mul_of_fixed
#print axioms sameCycle_of_cycleType_card_chordPerm
#print axioms cycleType_card_chordPerm_eq_add_one_iff

end PlaneTopology.PlaneChordCountExact
