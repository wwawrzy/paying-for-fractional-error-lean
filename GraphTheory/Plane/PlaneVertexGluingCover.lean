import GraphTheory.Plane.PlaneVertexGluing
import Mathlib.Logic.Equiv.Option

/-! # Transport point gluing to exact ambient graph covers -/

namespace PlaneTopology.PlaneVertexGluingCover

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap PlaneTopology.PlaneVertexGluingGraph

variable {A B V : Type*}

/-- Place the canonical point-union vertex into the ambient covered type. -/
def unionVertex (f : Option A ↪ V) (g : Option B ↪ V) : Option (A ⊕ B) → V
  | none => f none
  | some (Sum.inl a) => f (some a)
  | some (Sum.inr b) => g (some b)

theorem unionVertex_left (f : Option A ↪ V) (g : Option B ↪ V) (a : Option A) :
    unionVertex f g (leftVertex a) = f a := by cases a <;> rfl

theorem unionVertex_right (f : Option A ↪ V) (g : Option B ↪ V)
    (hfg : f none = g none) (b : Option B) : unionVertex f g (rightVertex b) = g b := by
  cases b
  · exact hfg
  · rfl

/-- Every canonical glued vertex belongs to one of the two original vertex images. -/
theorem canonical_cover (z : Option (A ⊕ B)) :
    (∃ a : Option A, leftVertex a = z) ∨ ∃ b : Option B, rightVertex b = z := by
  cases z with
  | none => exact Or.inl ⟨none, rfl⟩
  | some z =>
    cases z with
    | inl a => exact Or.inl ⟨some a, rfl⟩
    | inr b => exact Or.inr ⟨some b, rfl⟩

/-- Identifying exactly one common point gives an injective ambient vertex map. -/
theorem unionVertex_injective (f : Option A ↪ V) (g : Option B ↪ V)
    (hfg : f none = g none)
    (hmeet : ∀ a b, f a = g b → a = none ∧ b = none) :
    Function.Injective (unionVertex f g) := by
  intro x y h
  rcases canonical_cover x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases canonical_cover y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rw [unionVertex_left, unionVertex_left] at h
    exact congrArg leftVertex (f.injective h)
  · rw [unionVertex_left, unionVertex_right f g hfg] at h
    obtain ⟨ha, hb⟩ := hmeet a b h
    rw [ha, hb]
    rfl
  · rw [unionVertex_right f g hfg, unionVertex_left] at h
    obtain ⟨hb, ha⟩ := hmeet b a h.symm
    rw [ha, hb]
    rfl
  · rw [unionVertex_right f g hfg, unionVertex_right f g hfg] at h
    exact congrArg rightVertex (g.injective h)

/-- An ambient cover gives surjectivity of the canonical vertex map. -/
theorem unionVertex_surjective (f : Option A ↪ V) (g : Option B ↪ V)
    (hfg : f none = g none)
    (hcover : ∀ v, (∃ a, f a = v) ∨ ∃ b, g b = v) :
    Function.Surjective (unionVertex f g) := by
  intro v
  rcases hcover v with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨leftVertex a, (unionVertex_left f g a).trans ha⟩
  · exact ⟨rightVertex b, (unionVertex_right f g hfg b).trans hb⟩

/-- Exact vertex equivalence for an ambient single-point cover. -/
noncomputable def unionEquiv (f : Option A ↪ V) (g : Option B ↪ V)
    (hfg : f none = g none)
    (hmeet : ∀ a b, f a = g b → a = none ∧ b = none)
    (hcover : ∀ v, (∃ a, f a = v) ∨ ∃ b, g b = v) : Option (A ⊕ B) ≃ V :=
  Equiv.ofBijective (unionVertex f g)
    ⟨unionVertex_injective f g hfg hmeet, unionVertex_surjective f g hfg hcover⟩

/-- The exact ambient union of the two graph images. -/
def imageUnion (L : SimpleGraph (Option A)) (R : SimpleGraph (Option B))
    (f : Option A ↪ V) (g : Option B ↪ V) : SimpleGraph V := L.map f ⊔ R.map g

/-- Canonical point gluing is exactly the ambient image union, with no missing
or added graph edge in the transport. -/
noncomputable def unionIso (L : SimpleGraph (Option A)) (R : SimpleGraph (Option B))
    (f : Option A ↪ V) (g : Option B ↪ V) (hfg : f none = g none)
    (hmeet : ∀ a b, f a = g b → a = none ∧ b = none)
    (hcover : ∀ v, (∃ a, f a = v) ∨ ∃ b, g b = v) :
    gluedGraph L R ≃g imageUnion L R f g where
  toEquiv := unionEquiv f g hfg hmeet hcover
  map_rel_iff' := by
    intro x y
    let E := unionEquiv f g hfg hmeet hcover
    constructor
    · intro h
      rcases h with hl | hr
      · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj f L _ _).mp hl
        exact Or.inl ((SimpleGraph.map_adj leftEmbedding L _ _).mpr
          ⟨a, b, hab, E.injective ((unionVertex_left f g a).trans ha),
            E.injective ((unionVertex_left f g b).trans hb)⟩)
      · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj g R _ _).mp hr
        exact Or.inr ((SimpleGraph.map_adj rightEmbedding R _ _).mpr
          ⟨a, b, hab, E.injective ((unionVertex_right f g hfg a).trans ha),
            E.injective ((unionVertex_right f g hfg b).trans hb)⟩)
    · intro h
      rcases h with hl | hr
      · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj leftEmbedding L _ _).mp hl
        exact Or.inl ((SimpleGraph.map_adj f L _ _).mpr
          ⟨a, b, hab, (unionVertex_left f g a).symm.trans (congrArg E ha),
            (unionVertex_left f g b).symm.trans (congrArg E hb)⟩)
      · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj rightEmbedding R _ _).mp hr
        exact Or.inr ((SimpleGraph.map_adj g R _ _).mpr
          ⟨a, b, hab, (unionVertex_right f g hfg a).symm.trans (congrArg E ha),
            (unionVertex_right f g hfg b).symm.trans (congrArg E hb)⟩)

/-- Reparametrizing a graph by an equivalence and mapping it back cancels exactly. -/
theorem map_comap_equiv {X Y Z : Type*} (H : SimpleGraph Y) (e : X ≃ Y) (f : Y ↪ Z) :
    (H.comap e.toEmbedding).map (e.toEmbedding.trans f) = H.map f := by
  rw [← SimpleGraph.map_symm H e, SimpleGraph.map_map]
  congr 1
  funext x
  exact congrArg f (e.apply_symm_apply x)

variable [Fintype A] [Fintype B] [Fintype V]
variable [DecidableEq A] [DecidableEq B] [DecidableEq V]
variable (L : SimpleGraph (Option A)) (R : SimpleGraph (Option B))
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

instance imageUnionDecidableRel (f : Option A ↪ V) (g : Option B ↪ V) :
    DecidableRel (imageUnion L R f g).Adj := by
  intro x y
  unfold imageUnion
  infer_instance

/-- Actual plane-map construction on any ambient single-point cover. -/
noncomputable def unionPlaneMap (f : Option A ↪ V) (g : Option B ↪ V)
    (hfg : f none = g none)
    (hmeet : ∀ a b, f a = g b → a = none ∧ b = none)
    (hcover : ∀ v, (∃ a, f a = v) ∨ ∃ b, g b = v)
    (M : ConnectedPlaneMap L) (N : ConnectedPlaneMap R) :
    ConnectedPlaneMap (imageUnion L R f g) :=
  PlaneTopology.PlaneGeneralTransport.planeMap (unionIso L R f g hfg hmeet hcover)
    (PlaneTopology.PlaneVertexGluing.gluedPlaneMap L R M N)

end PlaneTopology.PlaneVertexGluingCover

#print axioms PlaneTopology.PlaneVertexGluingCover.unionIso
#print axioms PlaneTopology.PlaneVertexGluingCover.unionPlaneMap
