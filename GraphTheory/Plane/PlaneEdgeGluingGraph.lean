import GraphTheory.Faces.FaithfulPlaneMap
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The exact simple graph underlying an edge sum

The two endpoints are `Fin 2`; private vertex sets are kept disjoint. The
glued graph is the union of the two actual graph images, not an abstract
existence predicate or an assumed plane embedding.
-/

namespace PlaneTopology.PlaneEdgeGluingGraph

open SimpleGraph PlaneTopology.Faces.FaithfulPlaneMap

variable {A B : Type*}

/-- Place the left graph's vertices into the edge-sum vertex type. -/
def leftVertex : Fin 2 ⊕ A → Fin 2 ⊕ (A ⊕ B)
  | Sum.inl i => Sum.inl i
  | Sum.inr a => Sum.inr (Sum.inl a)

/-- Place the right graph's vertices into the edge-sum vertex type. -/
def rightVertex : Fin 2 ⊕ B → Fin 2 ⊕ (A ⊕ B)
  | Sum.inl i => Sum.inl i
  | Sum.inr b => Sum.inr (Sum.inr b)

theorem leftVertex_injective : Function.Injective (leftVertex (A := A) (B := B)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [leftVertex]

theorem rightVertex_injective : Function.Injective (rightVertex (A := A) (B := B)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rightVertex]

/-- The left and right images meet only at their common endpoint copies. -/
theorem leftVertex_eq_rightVertex_iff (x : Fin 2 ⊕ A) (y : Fin 2 ⊕ B) :
    leftVertex x = rightVertex y ↔ ∃ i : Fin 2, x = Sum.inl i ∧ y = Sum.inl i := by
  cases x <;> cases y <;> simp [leftVertex, rightVertex, eq_comm]

def leftEmbedding : (Fin 2 ⊕ A) ↪ (Fin 2 ⊕ (A ⊕ B)) :=
  ⟨leftVertex, leftVertex_injective⟩

def rightEmbedding : (Fin 2 ⊕ B) ↪ (Fin 2 ⊕ (A ⊕ B)) :=
  ⟨rightVertex, rightVertex_injective⟩

/-- The exact union of the two graph images, identifying only their common edge. -/
def gluedGraph (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B)) :
    SimpleGraph (Fin 2 ⊕ (A ⊕ B)) :=
  L.map leftEmbedding ⊔ R.map rightEmbedding

variable (L : SimpleGraph (Fin 2 ⊕ A)) (R : SimpleGraph (Fin 2 ⊕ B))

/-- The canonical left inclusion is an actual graph homomorphism. -/
def leftHom : L →g gluedGraph L R where
  toFun := leftVertex
  map_rel' := by
    intro x y h
    exact Or.inl ((SimpleGraph.map_adj leftEmbedding L _ _).mpr ⟨x, y, h, rfl, rfl⟩)

/-- The canonical right inclusion is an actual graph homomorphism. -/
def rightHom : R →g gluedGraph L R where
  toFun := rightVertex
  map_rel' := by
    intro x y h
    exact Or.inr ((SimpleGraph.map_adj rightEmbedding R _ _).mpr ⟨x, y, h, rfl, rfl⟩)

/-- Connected summands have a connected edge-sum graph because they share
the distinguished endpoint zero. -/
theorem gluedGraph_connected (hL : L.Connected) (hR : R.Connected) :
    (gluedGraph L R).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨Sum.inl 0, ?_⟩
  intro x
  cases x with
  | inl i =>
    obtain ⟨p⟩ := hL.preconnected (Sum.inl 0) (Sum.inl i)
    exact (p.map (leftHom L R)).reachable
  | inr x =>
    cases x with
    | inl a =>
      obtain ⟨p⟩ := hL.preconnected (Sum.inl 0) (Sum.inr a)
      exact (p.map (leftHom L R)).reachable
    | inr b =>
      obtain ⟨p⟩ := hR.preconnected (Sum.inl 0) (Sum.inr b)
      exact (p.map (rightHom L R)).reachable

/-- The two common vertices have precisely the adjacency of K₂. -/
theorem common_adj_iff (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (i j : Fin 2) :
    L.Adj (Sum.inl i) (Sum.inl j) ↔ i ≠ j := by
  fin_cases i <;> fin_cases j <;> simp [hL, hL.symm]

/-- Left dart transport into the exact graph union. -/
def leftDart (d : L.Dart) : (gluedGraph L R).Dart := (leftHom L R).mapDart d

/-- Right dart transport into the exact graph union. -/
def rightDart (d : R.Dart) : (gluedGraph L R).Dart := (rightHom L R).mapDart d

/-- Keep right darts other than the two orientations of the common edge. -/
def RightSurvivor := {d : R.Dart // ¬(d.fst.isLeft ∧ d.snd.isLeft)}

/-- Exact candidate dart domain: all left darts and nonduplicated right darts. -/
abbrev GluedDart := L.Dart ⊕ RightSurvivor R

/-- The candidate domain maps to actual darts of the exact graph union. -/
def gluedDart : GluedDart L R → (gluedGraph L R).Dart
  | Sum.inl d => leftDart L R d
  | Sum.inr d => rightDart L R d.1

/-- Each side's injective vertex inclusion gives an injective dart inclusion. -/
theorem leftDart_injective : Function.Injective (leftDart L R) := by
  intro d e h
  apply Dart.ext
  have hp := congrArg (fun x : (gluedGraph L R).Dart ↦ x.toProd) h
  exact Prod.ext (leftVertex_injective (congrArg Prod.fst hp))
    (leftVertex_injective (congrArg Prod.snd hp))

theorem rightDart_injective : Function.Injective (rightDart L R) := by
  intro d e h
  apply Dart.ext
  have hp := congrArg (fun x : (gluedGraph L R).Dart ↦ x.toProd) h
  exact Prod.ext (rightVertex_injective (congrArg Prod.fst hp))
    (rightVertex_injective (congrArg Prod.snd hp))

/-- No surviving right dart is identified with a left dart. -/
theorem leftDart_ne_rightSurvivor (d : L.Dart) (e : RightSurvivor R) :
    leftDart L R d ≠ rightDart L R e.1 := by
  intro h
  have hp := congrArg (fun x : (gluedGraph L R).Dart ↦ x.toProd) h
  obtain ⟨i, _, hi⟩ := (leftVertex_eq_rightVertex_iff d.fst e.1.fst).mp (congrArg Prod.fst hp)
  obtain ⟨j, _, hj⟩ := (leftVertex_eq_rightVertex_iff d.snd e.1.snd).mp (congrArg Prod.snd hp)
  exact e.2 (by simp [hi, hj])

theorem gluedDart_injective : Function.Injective (gluedDart L R) := by
  intro d e h
  cases d with
  | inl d =>
    cases e with
    | inl e => exact congrArg Sum.inl (leftDart_injective L R h)
    | inr e => exact (leftDart_ne_rightSurvivor L R d e h).elim
  | inr d =>
    cases e with
    | inl e => exact (leftDart_ne_rightSurvivor L R e d h.symm).elim
    | inr e =>
      exact congrArg Sum.inr (Subtype.ext (rightDart_injective L R h))

/-- Every actual union dart is a left dart or a nonduplicated right dart. -/
theorem gluedDart_surjective (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) :
    Function.Surjective (gluedDart L R) := by
  classical
  intro d
  rcases d.adj with hl | hr
  · obtain ⟨u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj leftEmbedding L _ _).mp hl
    refine ⟨Sum.inl ⟨(u, v), huv⟩, ?_⟩
    apply Dart.ext
    exact Prod.ext hu hv
  · obtain ⟨u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj rightEmbedding R _ _).mp hr
    by_cases hkeep : ¬(u.isLeft ∧ v.isLeft)
    · refine ⟨Sum.inr ⟨⟨(u, v), huv⟩, hkeep⟩, ?_⟩
      apply Dart.ext
      exact Prod.ext hu hv
    · have hboth : u.isLeft ∧ v.isLeft := not_not.mp hkeep
      cases u with
      | inr a => simp at hboth
      | inl i =>
        cases v with
        | inr b => simp at hboth
        | inl j =>
          have hij : i ≠ j := fun h ↦ huv.ne (congrArg Sum.inl h)
          refine ⟨Sum.inl ⟨(Sum.inl i, Sum.inl j), (common_adj_iff L hL i j).mpr hij⟩, ?_⟩
          apply Dart.ext
          exact Prod.ext hu hv

/-- Exact equivalence between nonduplicated input darts and actual glued darts. -/
noncomputable def gluedDartEquiv (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) :
    GluedDart L R ≃ (gluedGraph L R).Dart :=
  Equiv.ofBijective (gluedDart L R)
    ⟨gluedDart_injective L R, gluedDart_surjective L R hL⟩

theorem gluedDartEquiv_apply (hL : L.Adj (Sum.inl 0) (Sum.inl 1)) (d : GluedDart L R) :
    gluedDartEquiv L R hL d = gluedDart L R d := rfl

/-- Reversal of a surviving right dart is still a surviving right dart. -/
def rightSurvivorReverse (d : RightSurvivor R) : RightSurvivor R :=
  ⟨d.1.symm, fun h ↦ d.2 ⟨h.2, h.1⟩⟩

/-- The genuine edge reversal on the nonduplicated dart domain. -/
def gluedReversal : Equiv.Perm (GluedDart L R) where
  toFun := Sum.map Dart.symm (rightSurvivorReverse R)
  invFun := Sum.map Dart.symm (rightSurvivorReverse R)
  left_inv x := by cases x <;> simp [rightSurvivorReverse, Sum.map]
  right_inv x := by cases x <;> simp [rightSurvivorReverse, Sum.map]

/-- The exact dart correspondence respects edge reversal. -/
theorem gluedDart_reversal (d : GluedDart L R) :
    gluedDart L R (gluedReversal L R d) = (gluedDart L R d).symm := by
  cases d <;> rfl

variable [Fintype A] [Fintype B]

/-- Gluing the two pairs of distinguished endpoints removes exactly two
vertices from the sum of the original vertex counts. -/
theorem card_glued_vertices :
    Fintype.card (Fin 2 ⊕ (A ⊕ B)) + 2 =
      Fintype.card (Fin 2 ⊕ A) + Fintype.card (Fin 2 ⊕ B) := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

#print axioms gluedGraph_connected
#print axioms gluedDart_injective
#print axioms gluedDartEquiv

end PlaneTopology.PlaneEdgeGluingGraph
