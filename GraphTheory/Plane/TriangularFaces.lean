import GraphTheory.Faces.FaithfulPlaneMap
import GraphTheory.SimpleGraph.Planar.Basic

/-!
# Triangular faces and triangulated supergraphs

A triangular rotation system has three darts in every face orbit. Reindexing
sums by these face orbits gives the exact Euler edge count for triangular
plane embeddings. A triangulated supergraph uses the same vertex type as the
original graph and carries a faithful connected plane map.
-/

namespace TriangularFaces

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.Faces.FaithfulPlaneMap.FaceAlgebra
open scoped BigOperators

universe u

variable {V : Type*} {G : SimpleGraph V}

/-- All face orbits have length three. Simple graphs exclude shorter orbits. -/
def Triangular (r : G.RotationSystem) : Prop :=
  ∀ d, r.facePerm (r.facePerm (r.facePerm d)) = d

/-- A triangular plane supergraph on the same vertex type. -/
def HasTriangulatedSupergraph {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop := by
  classical
  exact ∃ T : SimpleGraph V, G ≤ T ∧
    ∃ M : ConnectedPlaneMap T, Triangular M.rawRotation

/-- Every finite forbidden-minor planar graph on at least three vertices has
 a triangular plane supergraph on the same vertex type. -/
def PlanarTriangulation : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.IsPlanar → 3 ≤ Fintype.card V → HasTriangulatedSupergraph G

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A triangular face consists of the three successive darts starting at any
one of its darts. -/
theorem faceIndex_eq_iff_triangle (r : G.RotationSystem)
    (htri : ∀ d, r.facePerm (r.facePerm (r.facePerm d)) = d)
    (e d : G.Dart) :
    faceIndex r e = faceIndex r d ↔
      e = d ∨ e = r.facePerm d ∨ e = r.facePerm (r.facePerm d) := by
  constructor
  · intro h
    have hs := (faceIndex_eq_iff_sameFace r d e).mp h.symm
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    have hpow : ∀ n : ℕ, (r.facePerm ^ n) d = d ∨
        (r.facePerm ^ n) d = r.facePerm d ∨
        (r.facePerm ^ n) d = r.facePerm (r.facePerm d) := by
      intro n
      induction n with
      | zero => exact Or.inl rfl
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h | h
        · exact Or.inr (Or.inl (congrArg r.facePerm h))
        · exact Or.inr (Or.inr (congrArg r.facePerm h))
        · exact Or.inl ((congrArg r.facePerm h).trans (htri d))
    rw [← hn]
    exact hpow n
  · rintro (rfl | rfl | rfl)
    · rfl
    · exact faceIndex_facePerm r d
    · exact (faceIndex_facePerm r (r.facePerm d)).trans (faceIndex_facePerm r d)

/-- The finite dart fiber of a triangular face. -/
theorem faceIndex_fiber_eq_triangle (r : G.RotationSystem)
    (htri : ∀ d, r.facePerm (r.facePerm (r.facePerm d)) = d)
    (d : G.Dart) :
    Finset.univ.filter (fun e => faceIndex r e = faceIndex r d) =
      {d, r.facePerm d, r.facePerm (r.facePerm d)} := by
  classical
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  exact faceIndex_eq_iff_triangle r htri e d

/-- A triangular face has three distinct darts. -/
theorem triangle_darts_distinct (r : G.RotationSystem)
    (htri : ∀ d, r.facePerm (r.facePerm (r.facePerm d)) = d)
    (d : G.Dart) :
    d ≠ r.facePerm d ∧ d ≠ r.facePerm (r.facePerm d) ∧
      r.facePerm d ≠ r.facePerm (r.facePerm d) := by
  refine ⟨(r.facePerm_ne_self d).symm, ?_, ?_⟩
  · intro h
    have hh := congrArg r.facePerm h
    rw [htri] at hh
    exact r.facePerm_ne_self d hh
  · intro h
    exact (r.facePerm_ne_self d).symm (r.facePerm.injective h)

/-- Every triangular face has exactly three darts. -/
theorem card_faceIndex_fiber_eq_three (r : G.RotationSystem)
    (htri : ∀ d, r.facePerm (r.facePerm (r.facePerm d)) = d)
    (F : FaceIndex r) :
    (Finset.univ.filter (fun e => faceIndex r e = F)).card = 3 := by
  classical
  rw [← faceIndex_representative r F, faceIndex_fiber_eq_triangle r htri]
  obtain ⟨h01, h02, h12⟩ := triangle_darts_distinct r htri (faceRepresentative r F)
  simp [h01, h02, h12, -SimpleGraph.RotationSystem.facePerm_apply]

/-- Summing face weights over darts counts each triangular face three times. -/
theorem sum_face_weights_over_darts (r : G.RotationSystem)
    (htri : ∀ d, r.facePerm (r.facePerm (r.facePerm d)) = d)
    (w : FaceIndex r → ℕ) :
    (∑ d : G.Dart, w (faceIndex r d)) = 3 * ∑ F, w F := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (faceIndex r) (fun d ↦ w (faceIndex r d))]
  calc
    (∑ F, ∑ d ∈ Finset.univ.filter (fun d ↦ faceIndex r d = F), w (faceIndex r d)) =
        ∑ F, 3 * w F := by
      apply Finset.sum_congr rfl
      intro F _
      have h := Finset.sum_congr (s₁ := Finset.univ.filter (fun d ↦ faceIndex r d = F))
        rfl (fun d hd ↦ congrArg w (Finset.mem_filter.mp hd).2)
      rw [h, Finset.sum_const, card_faceIndex_fiber_eq_three r htri]
      rfl
    _ = 3 * ∑ F, w F := (Finset.mul_sum _ _ _).symm

/-- A triangular plane embedding attains the Euler edge bound. -/
theorem saturated_of_triangular_rotation (r : G.RotationSystem)
    (heuler : r.IsPlanarEmbedding) (htri : Triangular r) :
    G.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hhand := sum_face_weights_over_darts r htri (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    card_faceIndex_eq_numFaces, G.dart_card_eq_twice_card_edges, Nat.cast_id] at hhand
  change Fintype.card V + r.numFaces = G.edgeFinset.card + 2 at heuler
  omega

end TriangularFaces
