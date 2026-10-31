import Mathlib

/-!
# Face-counting arithmetic for the girth endpoint

This module isolates the algebraic last step in the proof of the paper's
face-deficit estimate.  It does not construct a planar embedding and does not
prove the required charging estimate for short facial walks.  Those are the
topological inputs identified in `docs/girth-face-counting.md`.
-/

namespace Paper.GirthFaceCounting

open scoped BigOperators

/-- The nonnegative deficit of a face of boundary length `j` relative to `g`.
Lengths are represented in `ℤ` so that the definition remains meaningful
without a separate proof that `j ≤ g`. -/
def faceDeficit (g j : ℤ) : ℤ := max (g - j) 0

/-- A face's boundary length plus its deficit reaches the target girth. -/
theorem length_add_deficit_ge (g j : ℤ) :
    g ≤ j + faceDeficit g j := by
  unfold faceDeficit
  by_cases h : g - j ≤ 0
  · rw [max_eq_right h]
    omega
  · have h' : 0 ≤ g - j := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left h']
    omega

/-- Summing the pointwise deficit inequality over a finite family of faces
gives `g · number_of_faces ≤ total_perimeter + total_deficit`. -/
theorem girth_mul_faceCount_le_perimeter_add_deficit
    (g : ℤ) {F : Type*} [DecidableEq F]
    (faces : Finset F) (length : F → ℤ) :
    g * (faces.card : ℤ) ≤
      (∑ f ∈ faces, length f) +
        ∑ f ∈ faces, faceDeficit g (length f) := by
  calc
    g * (faces.card : ℤ) = ∑ f ∈ faces, g := by
      simp [mul_comm]
    _ ≤ ∑ f ∈ faces, (length f + faceDeficit g (length f)) := by
      apply Finset.sum_le_sum
      intro f hf
      exact length_add_deficit_ge g (length f)
    _ = (∑ f ∈ faces, length f) +
        ∑ f ∈ faces, faceDeficit g (length f) := by
      simp only [Finset.sum_add_distrib]

/-- Euler's equation and total facial perimeter turn a deficit charge bound
into the corresponding planar edge bound.  The hypotheses are abstract
integer data: in a graph application, `faces.card` is the number of faces,
`perimeter` is the sum of their boundary-walk lengths, and `charge` is the
total deficit assigned to marked vertices/edge sides. -/
theorem euler_deficit_edge_bound
    (g n m p : ℤ) {F : Type*} [DecidableEq F]
    (faces : Finset F) (length : F → ℤ)
    (hg : 3 ≤ g)
    (heuler : (faces.card : ℤ) + n = m + 2)
    (hperimeter : (∑ f ∈ faces, length f) = 2 * m)
    (hcharge :
      (∑ f ∈ faces, faceDeficit g (length f)) ≤ (g - 3) * p) :
    (g - 2) * m ≤ g * (n - 2) + (g - 3) * p := by
  have hface := girth_mul_faceCount_le_perimeter_add_deficit g faces length
  rw [hperimeter] at hface
  have hcharge' :
      g * (faces.card : ℤ) ≤ 2 * m + (g - 3) * p :=
    hface.trans (by linarith)
  have hcard : (faces.card : ℤ) = m + 2 - n := by omega
  rw [hcard] at hcharge'
  nlinarith

end Paper.GirthFaceCounting
