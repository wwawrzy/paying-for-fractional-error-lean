import GraphTheory.Plane.WagnerSeparation
import GraphTheory.Plane.WagnerSeparationAssembly

/-!
# Full constructive Wagner triangulation

Strong induction on the actual vertex cardinality. A three-connected graph
has the proved contraction embedding. Otherwise a minimum separator has
size zero, one or two; its strictly smaller sides are embedded inductively
and joined by the actual map constructors. The induction allows a connected
same-vertex supergraph, so disconnected inputs need no fictitious empty map.
-/

namespace PlaneTopology.WagnerGeneralEmbedding

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneSupergraphBasics
  PlaneTopology.WagnerSeparation PlaneTopology.WagnerSeparationAssembly PlaneTopology.WagnerSideUnion
  PlaneTopology.WagnerSeparatorSides

universe u

/-- Every finite minor-planar graph with at least two vertices has an
actual connected plane-map supergraph on precisely its original vertices. -/
theorem hasPlaneSupergraph_of_isPlanar {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsPlanar) (hcard : 2 ≤ Fintype.card V) :
    HasPlaneSupergraph G := by
  classical
  suffices h : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W), Fintype.card W = n → H.IsPlanar →
        2 ≤ Fintype.card W → HasPlaneSupergraph H by
    exact h _ V G rfl hG hcard
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H hW hplanar htwo
    by_cases hsmall : Fintype.card W ≤ 3
    · exact hasPlaneSupergraph_of_small H htwo hsmall
    have hlarge : 4 ≤ Fintype.card W := by omega
    by_cases h3 : H.IsKConnected 3
    · exact hasPlaneSupergraph_of_map
        (PlaneTopology.WagnerThreeEmbedding.planeMapOfIsPlanarThree H hplanar h3)
    obtain ⟨S, hSbound, hSconn, ⟨s⟩⟩ := exists_minimum_small_separation H hlarge h3
    let A := s.left
    let B := s.right
    have hAl : Fintype.card A < n := by
      have hh := Separation.card_left_lt H s
      simpa only [Nat.card_eq_fintype_card, hW] using hh
    have hBl : Fintype.card B < n := by
      have hh := Separation.card_right_lt H s
      simpa only [Nat.card_eq_fintype_card, hW] using hh
    haveI : Nonempty A := ⟨⟨s.left_private.choose, s.left_private.choose_spec.1⟩⟩
    haveI : Nonempty B := ⟨⟨s.right_private.choose, s.right_private.choose_spec.1⟩⟩
    have hApos : 0 < Fintype.card A := Fintype.card_pos
    have hBpos : 0 < Fintype.card B := Fintype.card_pos
    have hsideA (J : SimpleGraph A) (hJ : J.IsPlanar) (hA2 : 2 ≤ Fintype.card A) :
        HasPlaneSupergraph J := ih _ hAl A J rfl hJ hA2
    have hsideB (J : SimpleGraph B) (hJ : J.IsPlanar) (hB2 : 2 ≤ Fintype.card B) :
        HasPlaneSupergraph J := ih _ hBl B J rfl hJ hB2
    by_cases hS0 : S.card = 0
    · have hinter : A ∩ B = ∅ := by
        simpa only [Finset.card_eq_zero.mp hS0, Finset.coe_empty] using s.overlap
      by_cases hA2 : 2 ≤ Fintype.card A
      · have hA := hsideA (H.induce A) (hplanar.induce A) hA2
        by_cases hB2 : 2 ≤ Fintype.card B
        · exact hasPlaneSupergraph_of_disjoint_sides H A B s.cover hinter s.no_cross hA
            (hsideB (H.induce B) (hplanar.induce B) hB2)
        · exact hasPlaneSupergraph_of_singleton_right H A B s.cover hinter s.no_cross
            (by simpa only [Nat.card_eq_fintype_card] using (show Fintype.card B = 1 by omega)) hA
      · have hsum : Fintype.card W ≤ Fintype.card A + Fintype.card B := by
          have hh := Set.ncard_union_le A B
          rw [s.cover, Set.ncard_univ] at hh
          change Nat.card W ≤ Nat.card A + Nat.card B at hh
          simpa only [Nat.card_eq_fintype_card] using hh
        have hB2 : 2 ≤ Fintype.card B := by omega
        apply hasPlaneSupergraph_of_singleton_right H B A
          (by rw [Set.union_comm, s.cover]) (by rw [Set.inter_comm, hinter])
          (fun b hb a ha hab => s.no_cross a ha b hb hab.symm)
          (by simpa only [Nat.card_eq_fintype_card] using (show Fintype.card A = 1 by omega))
        exact hsideB (H.induce B) (hplanar.induce B) hB2
    have hSnonempty : (S : Set W).Nonempty := Finset.coe_nonempty.mpr
      (Finset.card_pos.mp (by omega))
    have hA2 : 2 ≤ Fintype.card A := by
      simpa only [Nat.card_eq_fintype_card] using
        two_le_card_left A B (S : Set W) s.overlap hSnonempty s.left_private
    have hB2 : 2 ≤ Fintype.card B := by
      simpa only [Nat.card_eq_fintype_card] using
        two_le_card_right A B (S : Set W) s.overlap hSnonempty s.right_private
    by_cases hS1 : S.card = 1
    · obtain ⟨v, hSv⟩ := Finset.card_eq_one.mp hS1
      have hinter : A ∩ B = {v} := by simpa only [hSv, Finset.coe_singleton] using s.overlap
      have hv : v ∈ A ∩ B := by rw [hinter]; simp
      exact hasPlaneSupergraph_of_point_sides H A B v hv.1 hv.2 s.cover hinter s.no_cross
        (hsideA (H.induce A) (hplanar.induce A) hA2)
        (hsideB (H.induce B) (hplanar.induce B) hB2)
    have hS2 : S.card = 2 := by omega
    obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.mp hS2
    have hinter : A ∩ B = {u, v} := by
      simpa only [hSuv, Finset.coe_insert, Finset.coe_singleton] using s.overlap
    have hu : u ∈ A ∩ B := by rw [hinter]; simp
    have hv : v ∈ A ∩ B := by rw [hinter]; simp
    have h2 : H.IsKConnected 2 := by simpa only [hS2] using hSconn
    let uA : A := ⟨u, hu.1⟩
    let vA : A := ⟨v, hv.1⟩
    let uB : B := ⟨u, hu.2⟩
    let vB : B := ⟨v, hv.2⟩
    have hAuv : uA ≠ vA := fun h => huv (congrArg Subtype.val h)
    have hBuv : uB ≠ vB := fun h => huv (congrArg Subtype.val h)
    have hAplanar := filledLeft_isPlanar H hplanar h2 A B uA vA hAuv
      s.cover hinter s.no_cross s.right_private
    have hBplanar := filledRight_isPlanar H hplanar h2 A B uB vB hBuv
      s.cover hinter s.no_cross s.left_private
    exact hasPlaneSupergraph_of_filled_sides H A B u v hu.1 hv.1 hu.2 hv.2 huv
      s.cover hinter s.no_cross
      (hsideA _ hAplanar hA2) (hsideB _ hBplanar hB2)

/-- Full same-vertex triangulation from the original forbidden-minor
definition of planarity, for every finite graph with at least three vertices. -/
theorem hasTriangulatedSupergraph_of_isPlanar {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsPlanar) (hcard : 3 ≤ Fintype.card V) :
    TriangularFaces.HasTriangulatedSupergraph G :=
  hasTriangulatedSupergraph_of_hasPlaneSupergraph G
    (hasPlaneSupergraph_of_isPlanar G hG (by omega)) hcard

/-- Finite forbidden-minor planar graphs on at least three vertices admit
triangular plane supergraphs, without an additional axiom or supplied embedding. -/
theorem planarTriangulation : TriangularFaces.PlanarTriangulation.{u} := by
  intro V _ _ G hG hcard
  exact hasTriangulatedSupergraph_of_isPlanar G hG hcard

#print axioms hasPlaneSupergraph_of_isPlanar
#print axioms hasTriangulatedSupergraph_of_isPlanar
#print axioms planarTriangulation

end PlaneTopology.WagnerGeneralEmbedding
