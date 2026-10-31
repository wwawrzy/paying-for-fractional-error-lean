import GraphTheory.SimpleGraph.Minor.ContractibleEdge
import GraphTheory.SimpleGraph.Planar.Basic
import GraphTheory.Plane.ConnectivityVertexDeletion

/-!
# The actual graph left after deleting a contracted vertex

Deleting the class of an edge uv from G/uv gives exactly G minus u and v.
Its former neighbors are the union of the actual neighbors of the two apices.
These are graph isomorphisms and adjacency identities, not embedding providers.
-/

namespace PlaneTopology.WagnerContractionGraph

open SimpleGraph SimpleGraph.EdgeContraction

variable {V : Type*}

/-- Vertices surviving deletion of both endpoints of the contracted edge. -/
abbrev ResidualVertex (u v : V) := {w : V // w ≠ u ∧ w ≠ v}

/-- Quotient vertices surviving deletion of the contracted class. -/
abbrev ContractedResidualVertex (u v : V) :=
  {q : ContrVertex u v // q ≠ contrMk u v u}

/-- The quotient map is a genuine bijection on the surviving vertices. -/
noncomputable def residualEquiv (u v : V) :
    ResidualVertex u v ≃ ContractedResidualVertex u v := by
  refine Equiv.ofBijective
    (fun w => ⟨contrMk u v w.val, fun h =>
      (not_or.mpr w.property) ((contrMk_eq_u_iff u v w.val).mp h)⟩) ⟨?_, ?_⟩
  · intro a b h
    apply Subtype.ext
    exact contrMk_injective u v a.property.1 a.property.2 b.property.1 b.property.2
      (congrArg Subtype.val h)
  · intro q
    obtain ⟨w, hw⟩ := contrMk_surjective u v q.val
    have hwu : w ≠ u := by
      intro h
      apply q.property
      simpa [h] using hw.symm
    have hwv : w ≠ v := by
      intro h
      apply q.property
      simpa [h, ← contrMk_eq u v] using hw.symm
    exact ⟨⟨w, hwu, hwv⟩, Subtype.ext hw⟩

/-- The forward vertex map is the original quotient map, without choices. -/
@[simp] theorem residualEquiv_apply (u v : V) (w : ResidualVertex u v) :
    (residualEquiv u v w).val = contrMk u v w.val := rfl

variable [DecidableEq V]

/-- Contraction changes no adjacency between two surviving vertices. -/
theorem contrGraph_adj_residual_iff (G : SimpleGraph V) (u v : V)
    (a b : ResidualVertex u v) :
    (contrGraph G u v).Adj (contrMk u v a.val) (contrMk u v b.val) ↔
      G.Adj a.val b.val := by
  constructor
  · rintro ⟨_, a', b', ha', hb', hadj⟩
    have ha : a' = a.val :=
      (contrMk_preimage_singleton u v a.property.1 a.property.2 a').mp ha'
    have hb : b' = b.val :=
      (contrMk_preimage_singleton u v b.property.1 b.property.2 b').mp hb'
    simpa [ha, hb] using hadj
  · intro hadj
    apply contrGraph_adj_of_adj G u v hadj
    intro h
    exact hadj.ne (contrMk_injective u v a.property.1 a.property.2
      b.property.1 b.property.2 h)

/-- The residual quotient graph is isomorphic to the actual induced graph
obtained by deleting the two endpoints before contraction. -/
noncomputable def residualIso (G : SimpleGraph V) (u v : V) :
    G.induce {w | w ≠ u ∧ w ≠ v} ≃g
      (contrGraph G u v).induce {q | q ≠ contrMk u v u} where
  toEquiv := residualEquiv u v
  map_rel_iff' := by
    intro a b
    exact contrGraph_adj_residual_iff G u v a b

/-- Neighbors of the contracted vertex are precisely the union of the old
neighbors of its two endpoints, restricted to surviving vertices. -/
theorem contracted_apex_adj_iff (G : SimpleGraph V) (u v : V)
    (w : ResidualVertex u v) :
    (contrGraph G u v).Adj (contrMk u v u) (contrMk u v w.val) ↔
      G.Adj u w.val ∨ G.Adj v w.val := by
  have hne : contrMk u v u ≠ contrMk u v w.val := by
    intro h
    exact (not_or.mpr w.property) ((contrMk_eq_u_iff u v w.val).mp h.symm)
  constructor
  · rintro ⟨_, a, b, ha, hb, hadj⟩
    have hb' : b = w.val :=
      (contrMk_preimage_singleton u v w.property.1 w.property.2 b).mp hb
    subst b
    rcases (contrMk_eq_u_iff u v a).mp ha with rfl | rfl
    · exact Or.inl hadj
    · exact Or.inr hadj
  · rintro (h | h)
    · exact ⟨hne, u, w.val, rfl, rfl, h⟩
    · exact ⟨hne, v, w.val, (contrMk_eq u v).symm, rfl, h⟩

section Finite

variable [Fintype V]

omit [Fintype V] in
/-- Actual contraction preserves both forbidden-minor conditions, including
the change of vertex type to the quotient. -/
theorem isPlanar_contrGraph (G : SimpleGraph V) (u v : V)
    (hG : G.IsPlanar) (huv : G.Adj u v) : (contrGraph G u v).IsPlanar := by
  have hm := contrGraph_isMinor_of_adj G huv
  exact ⟨fun h => hG.1 (h.trans hm), fun h => hG.2 (h.trans hm)⟩

/-- A non-base three-connected minor-planar graph has a genuinely smaller
three-connected minor-planar contraction for strong induction. -/
theorem exists_smaller_planar_three_contraction (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsPlanar) (h3 : G.IsKConnected 3)
    (hne : ¬Nonempty (G ≃g (⊤ : SimpleGraph (Fin 4)))) :
    ∃ u v : V, ∃ _huv : G.Adj u v,
      (contrGraph G u v).IsPlanar ∧
      (contrGraph G u v).IsKConnected 3 ∧
      Fintype.card (ContrVertex u v) < Fintype.card V := by
  obtain ⟨u, v, huv, hcontr⟩ :=
    SimpleGraph.EdgeContraction.IsKConnected.three_exists_contractible_edge G h3 hne
  exact ⟨u, v, huv, isPlanar_contrGraph G u v hG huv, hcontr,
    contrVertex_card_lt huv.ne⟩

/-- Deleting the contracted vertex of a three-connected contraction leaves
the original graph minus its two endpoints genuinely two-connected. -/
theorem residual_isKConnected_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (h3 : (contrGraph G u v).IsKConnected 3) :
    (G.induce {w | w ≠ u ∧ w ≠ v}).IsKConnected 2 := by
  classical
  have hcard := isKConnected_three_card_ge_four (contrGraph G u v) h3
  haveI : Nontrivial (ContrVertex u v) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have htwo := PlaneTopology.ConnectivityVertexDeletion.isKConnected_delete
    (contrGraph G u v) (contrMk u v u) (k := 2) (by omega) h3
  exact ((residualIso G u v).isKConnected_iff 2).mpr htwo

end Finite

#print axioms residualIso
#print axioms contracted_apex_adj_iff
#print axioms isPlanar_contrGraph
#print axioms exists_smaller_planar_three_contraction
#print axioms residual_isKConnected_two

end PlaneTopology.WagnerContractionGraph
