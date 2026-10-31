import GraphTheory.Faces.FaithfulPlaneMap
import Mathlib.Combinatorics.SimpleGraph.Maps

/-! # Exact graph and dart union for gluing at one vertex -/

namespace PlaneTopology.PlaneVertexGluingGraph

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap

variable {A B : Type*}

/-- Left vertex inclusion, identifying only the distinguished `none`. -/
def leftVertex : Option A → Option (A ⊕ B) := Option.map Sum.inl

/-- Right vertex inclusion, identifying only the distinguished `none`. -/
def rightVertex : Option B → Option (A ⊕ B) := Option.map Sum.inr

theorem leftVertex_injective : Function.Injective (leftVertex (A := A) (B := B)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [leftVertex]

theorem rightVertex_injective : Function.Injective (rightVertex (A := A) (B := B)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rightVertex]

/-- The two vertex images intersect at precisely their distinguished vertices. -/
theorem leftVertex_eq_rightVertex_iff (x : Option A) (y : Option B) :
    leftVertex x = rightVertex y ↔ x = none ∧ y = none := by
  cases x <;> cases y <;> simp [leftVertex, rightVertex]

def leftEmbedding : Option A ↪ Option (A ⊕ B) := ⟨leftVertex, leftVertex_injective⟩

def rightEmbedding : Option B ↪ Option (A ⊕ B) := ⟨rightVertex, rightVertex_injective⟩

/-- The exact union of the two original graph images, with only `none` identified. -/
def gluedGraph (L : SimpleGraph (Option A)) (R : SimpleGraph (Option B)) :
    SimpleGraph (Option (A ⊕ B)) := L.map leftEmbedding ⊔ R.map rightEmbedding

variable (L : SimpleGraph (Option A)) (R : SimpleGraph (Option B))

def leftHom : L →g gluedGraph L R where
  toFun := leftVertex
  map_rel' := by
    intro x y h
    exact Or.inl ((SimpleGraph.map_adj leftEmbedding L _ _).mpr ⟨x, y, h, rfl, rfl⟩)

def rightHom : R →g gluedGraph L R where
  toFun := rightVertex
  map_rel' := by
    intro x y h
    exact Or.inr ((SimpleGraph.map_adj rightEmbedding R _ _).mpr ⟨x, y, h, rfl, rfl⟩)

/-- The exact union of connected summands is connected through `none`. -/
theorem gluedGraph_connected (hL : L.Connected) (hR : R.Connected) :
    (gluedGraph L R).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  intro x
  cases x with
  | none => exact Reachable.refl none
  | some x =>
    cases x with
    | inl a => exact (hL.preconnected none (some a)).map (leftHom L R)
    | inr b => exact (hR.preconnected none (some b)).map (rightHom L R)

def leftDart (d : L.Dart) : (gluedGraph L R).Dart := (leftHom L R).mapDart d

def rightDart (d : R.Dart) : (gluedGraph L R).Dart := (rightHom L R).mapDart d

/-- Every input dart is retained, since a single shared vertex shares no edge. -/
def gluedDart : L.Dart ⊕ R.Dart → (gluedGraph L R).Dart :=
  Sum.elim (leftDart L R) (rightDart L R)

theorem leftDart_injective : Function.Injective (leftDart L R) := by
  intro d e h
  apply Dart.ext
  have hp := congrArg (fun x : (gluedGraph L R).Dart => x.toProd) h
  exact Prod.ext (leftVertex_injective (congrArg Prod.fst hp))
    (leftVertex_injective (congrArg Prod.snd hp))

theorem rightDart_injective : Function.Injective (rightDart L R) := by
  intro d e h
  apply Dart.ext
  have hp := congrArg (fun x : (gluedGraph L R).Dart => x.toProd) h
  exact Prod.ext (rightVertex_injective (congrArg Prod.fst hp))
    (rightVertex_injective (congrArg Prod.snd hp))

/-- No dart can belong to both images: that would be a loop at `none`. -/
theorem leftDart_ne_rightDart (d : L.Dart) (e : R.Dart) : leftDart L R d ≠ rightDart L R e := by
  intro h
  have hp := congrArg (fun x : (gluedGraph L R).Dart => x.toProd) h
  have hfst := (leftVertex_eq_rightVertex_iff d.fst e.fst).mp (congrArg Prod.fst hp)
  have hsnd := (leftVertex_eq_rightVertex_iff d.snd e.snd).mp (congrArg Prod.snd hp)
  exact d.adj.ne (hfst.1.trans hsnd.1.symm)

theorem gluedDart_injective : Function.Injective (gluedDart L R) := by
  intro d e h
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (leftDart_injective L R h)
    | inr e => exact (leftDart_ne_rightDart L R d e h).elim
  | inr d =>
    cases e with
    | inl e => exact (leftDart_ne_rightDart L R e d h.symm).elim
    | inr e => exact congrArg Sum.inr (rightDart_injective L R h)

theorem gluedDart_surjective : Function.Surjective (gluedDart L R) := by
  intro d
  rcases d.adj with hl | hr
  · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj leftEmbedding L _ _).mp hl
    exact ⟨Sum.inl ⟨(a, b), hab⟩, Dart.ext _ _ (Prod.ext ha hb)⟩
  · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj rightEmbedding R _ _).mp hr
    exact ⟨Sum.inr ⟨(a, b), hab⟩, Dart.ext _ _ (Prod.ext ha hb)⟩

/-- Exact equivalence with the actual dart type of the union graph. -/
noncomputable def gluedDartEquiv : L.Dart ⊕ R.Dart ≃ (gluedGraph L R).Dart :=
  Equiv.ofBijective (gluedDart L R) ⟨gluedDart_injective L R, gluedDart_surjective L R⟩

/-- Genuine edge reversal acts independently on the two summands. -/
def gluedReversal : Equiv.Perm (L.Dart ⊕ R.Dart) :=
  Equiv.sumCongr (SimpleGraph.dartSymmPerm L) (SimpleGraph.dartSymmPerm R)

theorem gluedDart_reversal (d : L.Dart ⊕ R.Dart) :
    gluedDart L R (gluedReversal L R d) = (gluedDart L R d).symm := by
  cases d <;> rfl

/-- A left singleton contributes no vertices or edges beyond the common point. -/
noncomputable def rightIsoOfIsEmpty [IsEmpty A] : R ≃g gluedGraph L R where
  toEquiv := Equiv.ofBijective rightVertex ⟨rightVertex_injective, by
    intro x
    cases x with
    | none => exact ⟨none, rfl⟩
    | some x =>
      cases x with
      | inl a => exact isEmptyElim a
      | inr b => exact ⟨some b, rfl⟩⟩
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rcases h with hl | hr
      · obtain ⟨a, b, hab, _, _⟩ := (SimpleGraph.map_adj leftEmbedding L _ _).mp hl
        have hn (z : Option A) : z = none := by
          cases z with
          | none => rfl
          | some z => exact isEmptyElim z
        exact (hab.ne ((hn a).trans (hn b).symm)).elim
      · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj rightEmbedding R _ _).mp hr
        have ha' : a = x := rightVertex_injective ha
        have hb' : b = y := rightVertex_injective hb
        simpa only [ha', hb'] using hab
    · intro h
      exact (rightHom L R).map_adj h

/-- A right singleton similarly leaves precisely the left graph. -/
noncomputable def leftIsoOfIsEmpty [IsEmpty B] : L ≃g gluedGraph L R where
  toEquiv := Equiv.ofBijective leftVertex ⟨leftVertex_injective, by
    intro x
    cases x with
    | none => exact ⟨none, rfl⟩
    | some x =>
      cases x with
      | inl a => exact ⟨some a, rfl⟩
      | inr b => exact isEmptyElim b⟩
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rcases h with hl | hr
      · obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj leftEmbedding L _ _).mp hl
        have ha' : a = x := leftVertex_injective ha
        have hb' : b = y := leftVertex_injective hb
        simpa only [ha', hb'] using hab
      · obtain ⟨a, b, hab, _, _⟩ := (SimpleGraph.map_adj rightEmbedding R _ _).mp hr
        have hn (z : Option B) : z = none := by
          cases z with
          | none => rfl
          | some z => exact isEmptyElim z
        exact (hab.ne ((hn a).trans (hn b).symm)).elim
    · intro h
      exact (leftHom L R).map_adj h

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable [DecidableRel L.Adj] [DecidableRel R.Adj]

/-- Decidable adjacency of the finite exact graph union. -/
instance gluedGraphDecidableRel : DecidableRel (gluedGraph L R).Adj := by
  intro x y
  unfold gluedGraph
  infer_instance

omit [DecidableEq A] [DecidableEq B] in
/-- One identified vertex is removed from the sum of the vertex counts. -/
theorem card_glued_vertices : Fintype.card (Option (A ⊕ B)) + 1 =
    Fintype.card (Option A) + Fintype.card (Option B) := by
  simp only [Fintype.card_option, Fintype.card_sum]
  omega

/-- No edge is lost or duplicated under point gluing. -/
theorem card_glued_edges : (gluedGraph L R).edgeFinset.card = L.edgeFinset.card + R.edgeFinset.card := by
  have hc := Fintype.card_congr (gluedDartEquiv L R)
  rw [Fintype.card_sum, L.dart_card_eq_twice_card_edges, R.dart_card_eq_twice_card_edges,
    (gluedGraph L R).dart_card_eq_twice_card_edges] at hc
  omega

end PlaneTopology.PlaneVertexGluingGraph

#print axioms PlaneTopology.PlaneVertexGluingGraph.gluedDartEquiv
#print axioms PlaneTopology.PlaneVertexGluingGraph.rightIsoOfIsEmpty
