import GraphTheory.Plane.PlaneVertexGluingCover
import GraphTheory.Plane.PlaneFanInsertion
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! # Actual plane maps joined by one disjoint bridge -/

namespace PlaneTopology.PlaneDisjointBridge

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneLeafInsertion PlaneTopology.PlaneVertexGluingCover

variable {A B : Type*}

/-- Put a fresh leaf at the chosen vertex of the right graph. -/
def bridgeLeft (b : B) : Option A ↪ A ⊕ B where
  toFun
    | none => Sum.inr b
    | some a => Sum.inl a
  inj' := by intro x y h; cases x <;> cases y <;> simp_all

/-- The right graph is reparametrized with its attachment vertex as `none`. -/
def bridgeRight [DecidableEq B] (b : B) : Option {w : B // w ≠ b} ↪ A ⊕ B :=
  (Equiv.optionSubtypeNe b).toEmbedding.trans Function.Embedding.inr

/-- The two bridge charts overlap at precisely their attachment point. -/
theorem bridge_meet [DecidableEq B] (b : B)
    (x : Option A) (y : Option {w : B // w ≠ b})
    (h : bridgeLeft b x = bridgeRight b y) : x = none ∧ y = none := by
  cases x with
  | none =>
    refine ⟨rfl, (Equiv.optionSubtypeNe b).injective ?_⟩
    exact (Sum.inr.inj h).symm
  | some x => cases h

/-- The bridge charts cover the actual disjoint-sum vertex type. -/
theorem bridge_cover [DecidableEq B] (b : B) (v : A ⊕ B) :
    (∃ x, bridgeLeft b x = v) ∨ ∃ y, bridgeRight b y = v := by
  cases v with
  | inl a => exact Or.inl ⟨some a, rfl⟩
  | inr w =>
    exact Or.inr ⟨(Equiv.optionSubtypeNe b).symm w,
      congrArg Sum.inr ((Equiv.optionSubtypeNe b).apply_symm_apply w)⟩

/-- The mapped fresh-leaf graph is exactly the left graph plus the bridge edge. -/
theorem leaf_image_eq (G : SimpleGraph A) (a : A) (b : B) :
    (leafGraph G a).map (bridgeLeft b) =
      G.map Function.Embedding.inl ⊔ edge (Sum.inl a) (Sum.inr b) := by
  ext u v
  constructor
  · intro h
    obtain ⟨x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj (bridgeLeft b) (leafGraph G a) u v).mp h
    cases x with
    | none =>
      cases y with
      | none => exact hxy.elim
      | some y =>
        change a = y at hxy
        subst y
        exact Or.inr (by simp [bridgeLeft, edge_adj])
    | some x =>
      cases y with
      | none =>
        change x = a at hxy
        subst x
        exact Or.inr (by simp [bridgeLeft, edge_adj])
      | some y =>
        exact Or.inl ((SimpleGraph.map_adj Function.Embedding.inl G _ _).mpr
          ⟨x, y, hxy, rfl, rfl⟩)
  · intro h
    rcases h with hl | hr
    · obtain ⟨x, y, hxy, hx, hy⟩ := (SimpleGraph.map_adj Function.Embedding.inl G _ _).mp hl
      exact (SimpleGraph.map_adj (bridgeLeft b) (leafGraph G a) _ _).mpr
        ⟨some x, some y, hxy, hx, hy⟩
    · obtain ⟨h | h, _⟩ := (edge_adj (Sum.inl a) (Sum.inr b) u v).mp hr
      · rw [h.1, h.2]
        exact (SimpleGraph.map_adj (bridgeLeft b) (leafGraph G a) _ _).mpr
          ⟨some a, none, rfl, rfl, rfl⟩
      · rw [h.1, h.2]
        exact (SimpleGraph.map_adj (bridgeLeft b) (leafGraph G a) _ _).mpr
          ⟨none, some a, rfl, rfl, rfl⟩

/-- The graph disjoint sum is the union of the two disjoint graph images. -/
theorem sum_eq_images (G : SimpleGraph A) (H : SimpleGraph B) :
    G ⊕g H = G.map Function.Embedding.inl ⊔ H.map Function.Embedding.inr := by
  ext u v
  cases u <;> cases v <;> simp [SimpleGraph.sum, SimpleGraph.map_adj]

/-- Exact graph identity after the leaf-plus-point-gluing construction. -/
theorem bridge_image_eq [DecidableEq B] (G : SimpleGraph A) (H : SimpleGraph B) (a : A) (b : B) :
    imageUnion (leafGraph G a) (H.comap (Equiv.optionSubtypeNe b).toEmbedding)
      (bridgeLeft b) (bridgeRight b) = (G ⊕g H) ⊔ edge (Sum.inl a) (Sum.inr b) := by
  rw [imageUnion, bridgeRight, map_comap_equiv, leaf_image_eq, sum_eq_images]
  ac_rfl

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph A) (H : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Decidable adjacency in the exact bridge-joined graph. -/
instance bridgeGraphDecidableRel (a : A) (b : B) :
    DecidableRel ((G ⊕g H) ⊔ edge (Sum.inl a) (Sum.inr b)).Adj := by
  letI : DecidableRel (G ⊕g H).Adj := by
    intro x y
    cases x <;> cases y <;> dsimp [SimpleGraph.sum] <;> infer_instance
  intro x y
  infer_instance

/-- Join two actual plane maps by exactly one bridge between the chosen
vertices, retaining all original edges and no other new edge. -/
noncomputable def bridgePlaneMap (M : ConnectedPlaneMap G) (N : ConnectedPlaneMap H)
    (a : A) (b : B) : ConnectedPlaneMap ((G ⊕g H) ⊔ edge (Sum.inl a) (Sum.inr b)) := by
  let K := H.comap (Equiv.optionSubtypeNe b).toEmbedding
  let N' : ConnectedPlaneMap K := PlaneTopology.PlaneGeneralTransport.planeMap
    (SimpleGraph.Iso.comap (Equiv.optionSubtypeNe b) H).symm N
  let P := unionPlaneMap (leafGraph G a) K (bridgeLeft b) (bridgeRight b) rfl
    (bridge_meet b) (bridge_cover b) (leafPlaneMap G a M) N'
  exact PlaneTopology.PlaneFanInsertion.castPlaneMap (bridge_image_eq G H a b) P

end PlaneTopology.PlaneDisjointBridge

#print axioms PlaneTopology.PlaneDisjointBridge.bridge_image_eq
#print axioms PlaneTopology.PlaneDisjointBridge.bridgePlaneMap
