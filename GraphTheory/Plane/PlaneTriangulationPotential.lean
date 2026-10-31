import GraphTheory.Faces.FacialSeparation

/-!
# Face-potential calculation for two consecutive triangle edges

On a vertex rotation, a face-boundary potential whose edge vector is supported
on two consecutive darts has one exceptional corner. This is the finite cyclic
calculation used to rule out crossing cofacial diagonals in an actual sphere
map; it does not assert existence of an embedding or a triangulation.
-/

namespace PlaneTopology.PlaneTriangulationPotential

/-- A function unchanged by a permutation step is constant on its cycles. -/
theorem eq_of_sameCycle_of_step_eq {X Y : Type*} [Finite X]
    (σ : Equiv.Perm X) (A : X → Y) (hstep : ∀ x, A (σ x) = A x)
    {a b : X} (hsame : σ.SameCycle a b) : A a = A b := by
  obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
  have hp : ∀ k : ℕ, A ((σ ^ k) a) = A a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hstep, ih]
  have h := hp n
  rw [hn] at h
  exact h.symm

/-- Two consecutive toggles of a cyclic binary potential isolate precisely
the corner between them. All other corners have the same potential. -/
theorem eq_outside_consecutive_toggles {X : Type*} [Finite X] [DecidableEq X]
    (σ : Equiv.Perm X) (A : X → ZMod 2) (a b : X)
    (hab : a ≠ b) (hσ : σ a = b)
    (hboundary : ∀ x, A x + A (σ x) = if x = a ∨ x = b then 1 else 0)
    {x : X} (hcycle : σ.SameCycle a x) (hxb : x ≠ b) : A x = A a := by
  let B : X → ZMod 2 := fun y => A y + if y = b then 1 else 0
  have hinv : ∀ y, B (σ y) = B y := by
    intro y
    have hsum := hboundary y
    by_cases hya : y = a
    · subst y
      simp only [hσ, true_or, if_true] at hsum
      simp only [B, hσ, hab, if_true, if_false, add_zero]
      calc
        A b + 1 = A b + (A a + A b) := by rw [hsum]
        _ = A a + (A b + A b) := by ac_rfl
        _ = A a := by rw [ZModModule.add_self, add_zero]
    · by_cases hyb : y = b
      · subst y
        have hσb : σ b ≠ b := by
          intro h
          exact hab (σ.injective (hσ.trans h.symm))
        simp only [B, hσb, if_true, if_false, add_zero]
        simp only [hya, false_or, if_true] at hsum
        calc
          A (σ b) = 1 - A b := eq_sub_of_add_eq (by simpa [add_comm] using hsum)
          _ = A b + 1 := by simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]
      · have hσyb : σ y ≠ b := by
          intro h
          exact hya (σ.injective (h.trans hσ.symm))
        simp only [B, hσyb, hyb, if_false, add_zero]
        simp only [hya, hyb, false_or, if_false] at hsum
        have hneg := eq_neg_of_add_eq_zero_left hsum
        simpa only [ZMod.neg_eq_self_mod_two] using hneg.symm
  have h := eq_of_sameCycle_of_step_eq σ B hinv hcycle
  simpa only [B, hab, hxb, if_false, add_zero] using h.symm

#print axioms eq_outside_consecutive_toggles

end PlaneTopology.PlaneTriangulationPotential
