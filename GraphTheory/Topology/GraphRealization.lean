import Mathlib
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Compact

/-! A graph as a topological quotient of vertices and closed edge intervals.
Endpoint identifications and reversal of the two darts are explicit. A drawing
by continuous injective arcs, with disjoint interiors avoiding vertices, induces
a closed topological embedding for every finite graph into a Hausdorff space.
The canonical coordinate drawing proves Hausdorffness and equivalence between
arc drawings and topological embeddings for finite graphs in Hausdorff targets.
This supplies the ordinary graph-realization input for the surface bridge;
it does not yet construct a surface rotation or compare Euler genera. -/
namespace SimpleGraph.TopologicalRealization
open scoped unitInterval
variable {V : Type*} (G : SimpleGraph V)

abbrev Fiber : V ⊕ G.Dart → Type
  | .inl _ => Unit
  | .inr _ => I
instance fiberTopology (c : V ⊕ G.Dart) : TopologicalSpace (Fiber G c) := by
  cases c <;> dsimp only [Fiber] <;> infer_instance
instance fiberCompact (c : V ⊕ G.Dart) : CompactSpace (Fiber G c) := by
  cases c with
  | inl v => exact inferInstanceAs (CompactSpace Unit)
  | inr d => exact inferInstanceAs (CompactSpace I)
abbrev Raw := (c : V ⊕ G.Dart) × Fiber G c

def rawVertex (v : V) : Raw G := ⟨.inl v,()⟩
def rawEdge (d : G.Dart) (t : I) : Raw G := ⟨.inr d,t⟩
inductive Gluing : Raw G → Raw G → Prop
  | zero (d : G.Dart) : Gluing (rawEdge G d 0) (rawVertex G d.fst)
  | one (d : G.Dart) : Gluing (rawEdge G d 1) (rawVertex G d.snd)
  | reverse (d : G.Dart) (t : I) :
      Gluing (rawEdge G d.symm (unitInterval.symm t)) (rawEdge G d t)

def Space := Quot (Gluing G)
instance spaceTopology : TopologicalSpace (Space G) := inferInstanceAs (TopologicalSpace (Quot (Gluing G)))
instance spaceCompact [Finite V] : CompactSpace (Space G) := by
  letI : Finite G.Dart := Finite.of_injective (fun d : G.Dart => d.toProd) Dart.toProd_injective
  exact inferInstanceAs (CompactSpace (Quot (Gluing G)))
def vertex (v : V) : Space G := Quot.mk _ (rawVertex G v)
def edge (d : G.Dart) (t : I) : Space G := Quot.mk _ (rawEdge G d t)
@[simp] theorem edge_zero (d : G.Dart) : edge G d 0 = vertex G d.fst := Quot.sound (.zero d)
@[simp] theorem edge_one (d : G.Dart) : edge G d 1 = vertex G d.snd := Quot.sound (.one d)
theorem edge_reverse (d : G.Dart) (t : I) :
    edge G d.symm (unitInterval.symm t) = edge G d t := Quot.sound (.reverse d t)

theorem point_cases (p : Space G) :
    (∃ v, p = vertex G v) ∨ ∃ d t, (0 : ℝ) < t.val ∧ t.val < 1 ∧ p = edge G d t := by
  induction p using Quot.inductionOn with
  | h x =>
    rcases x with ⟨v | d,t⟩
    · left; exact ⟨v,by cases t; rfl⟩
    · by_cases hz : t = 0
      · subst t; exact Or.inl ⟨d.fst,edge_zero G d⟩
      by_cases ho : t = 1
      · subst t; exact Or.inl ⟨d.snd,edge_one G d⟩
      right
      refine ⟨d,t,?_,?_,rfl⟩
      · have hne : t.val ≠ 0 := by simpa only [unitInterval.coe_ne_zero] using hz
        exact lt_of_le_of_ne t.property.1 (Ne.symm hne)
      · have hne : t.val ≠ 1 := by simpa only [unitInterval.coe_ne_one] using ho
        exact lt_of_le_of_ne t.property.2 hne

/-- An ordinary topological embedding of the quotient realization of a graph. -/
def EmbedsInto (S : Type*) [TopologicalSpace S] : Prop :=
  ∃ f : C(Space G,S), Topology.IsEmbedding f

variable {S : Type*} [TopologicalSpace S]
/-- Continuous injective arcs; interiors avoid vertices and distinct undirected edges.
The two darts of an edge parametrize the same arc with opposite orientations. -/
structure Drawing where
  vertex : V → S
  vertex_injective : Function.Injective vertex
  arc : G.Dart → C(I,S)
  arc_injective : ∀ d, Function.Injective (arc d)
  arc_zero : ∀ d, arc d 0 = vertex d.fst
  arc_one : ∀ d, arc d 1 = vertex d.snd
  arc_reverse : ∀ d t, arc d.symm (unitInterval.symm t) = arc d t
  interior_avoids : ∀ d t, (0 : ℝ) < t.val → t.val < 1 → ∀ v, arc d t ≠ vertex v
  interior_disjoint : ∀ d e s t, (0 : ℝ) < s.val → s.val < 1 →
    (0 : ℝ) < t.val → t.val < 1 → arc d s = arc e t → e = d ∨ e = d.symm

end SimpleGraph.TopologicalRealization

namespace SimpleGraph.TopologicalRealization.Drawing
open scoped unitInterval
variable {V : Type*} {G : SimpleGraph V} {S : Type*} [TopologicalSpace S]
  (D : Drawing G (S := S))
def rawMap : Raw G → S
  | ⟨.inl v,_⟩ => D.vertex v
  | ⟨.inr d,t⟩ => D.arc d t

theorem rawMap_continuous : Continuous D.rawMap := by
  apply continuous_sigma
  intro c
  cases c with
  | inl v => exact continuous_const
  | inr d => exact (D.arc d).continuous

theorem rawMap_gluing (a b : Raw G) (h : Gluing G a b) : D.rawMap a = D.rawMap b := by
  cases h with
  | zero d => exact D.arc_zero d
  | one d => exact D.arc_one d
  | reverse d t => exact D.arc_reverse d t

def map : Space G → S := Quot.lift D.rawMap D.rawMap_gluing
@[simp] theorem map_vertex (v : V) : D.map (TopologicalRealization.vertex G v) = D.vertex v := rfl
@[simp] theorem map_edge (d : G.Dart) (t : I) : D.map (edge G d t) = D.arc d t := rfl

theorem map_continuous : Continuous D.map := continuous_quot_lift D.rawMap_gluing D.rawMap_continuous

theorem map_injective : Function.Injective D.map := by
  intro p q hpq
  rcases point_cases G p with ⟨v,rfl⟩ | ⟨d,s,hs0,hs1,rfl⟩
  · rcases point_cases G q with ⟨w,rfl⟩ | ⟨e,t,ht0,ht1,rfl⟩
    · exact congrArg (TopologicalRealization.vertex G) (D.vertex_injective hpq)
    · exact False.elim (D.interior_avoids e t ht0 ht1 v hpq.symm)
  · rcases point_cases G q with ⟨w,rfl⟩ | ⟨e,t,ht0,ht1,rfl⟩
    · exact False.elim (D.interior_avoids d s hs0 hs1 w hpq)
    · rcases D.interior_disjoint d e s t hs0 hs1 ht0 ht1 hpq with he | he
      · subst e
        exact congrArg (edge G d) (D.arc_injective d hpq)
      · subst e
        have hrev := D.arc_reverse d (unitInterval.symm t)
        simp only [unitInterval.symm_symm] at hrev
        have heq : s = unitInterval.symm t := D.arc_injective d (hpq.trans hrev)
        rw [heq]
        exact (edge_reverse G d (unitInterval.symm t)).symm.trans (by simp)

theorem map_isClosedEmbedding [Finite V] [T2Space S] :
    Topology.IsClosedEmbedding D.map := D.map_continuous.isClosedEmbedding D.map_injective

theorem embedsInto (D : Drawing G (S := S)) [Finite V] [T2Space S] : EmbedsInto G S :=
  ⟨⟨D.map,D.map_continuous⟩,D.map_isClosedEmbedding.isEmbedding⟩

end SimpleGraph.TopologicalRealization.Drawing


namespace SimpleGraph.TopologicalRealization
open scoped unitInterval
variable {V : Type*} (G : SimpleGraph V) [DecidableEq V]

def vertexCoord (v x : V) : ℝ := if x = v then 1 else 0

def arcCoord (d : G.Dart) (t : I) (x : V) : ℝ :=
  (1-(t : ℝ))*vertexCoord d.fst x + (t : ℝ)*vertexCoord d.snd x

theorem arcCoord_fst (d : G.Dart) (t : I) : arcCoord G d t d.fst = 1-(t : ℝ) := by
  simp [arcCoord,vertexCoord,d.fst_ne_snd]
theorem arcCoord_snd (d : G.Dart) (t : I) : arcCoord G d t d.snd = (t : ℝ) := by
  simp [arcCoord,vertexCoord,d.snd_ne_fst]
theorem arcCoord_zero (d : G.Dart) : arcCoord G d 0 = vertexCoord d.fst := by
  funext x; simp [arcCoord]
theorem arcCoord_one (d : G.Dart) : arcCoord G d 1 = vertexCoord d.snd := by
  funext x; simp [arcCoord]
theorem arcCoord_reverse (d : G.Dart) (t : I) :
    arcCoord G d.symm (unitInterval.symm t) = arcCoord G d t := by
  funext x
  change (1-(1-(t : ℝ)))*vertexCoord d.snd x + (1-(t : ℝ))*vertexCoord d.fst x =
    (1-(t : ℝ))*vertexCoord d.fst x + (t : ℝ)*vertexCoord d.snd x
  ring

theorem vertexCoord_injective : Function.Injective (vertexCoord (V := V)) := by
  intro v w h
  by_contra hn
  have hh := congrFun h v
  simp [vertexCoord,hn] at hh

theorem arcCoord_injective (d : G.Dart) : Function.Injective (arcCoord G d) := by
  intro s t h
  have hh := congrFun h d.snd
  rw [arcCoord_snd,arcCoord_snd] at hh
  exact Subtype.ext hh

theorem arcCoord_avoids (d : G.Dart) (t : I) (ht0 : (0 : ℝ) < t.val) (ht1 : t.val < 1)
    (v : V) : arcCoord G d t ≠ vertexCoord v := by
  intro h
  by_cases hv : v = d.fst
  · have hh := congrFun h d.snd
    rw [arcCoord_snd] at hh
    simp only [vertexCoord,hv,if_neg d.snd_ne_fst] at hh
    linarith
  · have hh := congrFun h d.fst
    rw [arcCoord_fst] at hh
    simp only [vertexCoord,if_neg (Ne.symm hv)] at hh
    linarith

theorem arcCoord_disjoint (d e : G.Dart) (s t : I)
    (hs0 : (0 : ℝ) < s.val) (hs1 : s.val < 1)
    (h : arcCoord G d s = arcCoord G e t) : e = d ∨ e = d.symm := by
  have hf : d.fst = e.fst ∨ d.fst = e.snd := by
    by_contra hn
    push Not at hn
    have hh := congrFun h d.fst
    rw [arcCoord_fst] at hh
    have hz : arcCoord G e t d.fst = 0 := by simp [arcCoord,vertexCoord,hn.1,hn.2]
    rw [hz] at hh
    linarith
  have hs : d.snd = e.fst ∨ d.snd = e.snd := by
    by_contra hn
    push Not at hn
    have hh := congrFun h d.snd
    rw [arcCoord_snd] at hh
    have hz : arcCoord G e t d.snd = 0 := by simp [arcCoord,vertexCoord,hn.1,hn.2]
    rw [hz] at hh
    linarith
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · exact False.elim (d.fst_ne_snd (hf.trans hs.symm))
  · exact Or.inl (Dart.ext _ _ (Prod.ext hf.symm hs.symm))
  · exact Or.inr (Dart.ext _ _ (Prod.ext hs.symm hf.symm))
  · exact False.elim (d.fst_ne_snd (hf.trans hs.symm))

noncomputable def coordinateDrawing : Drawing G (S := V → ℝ) where
  vertex := vertexCoord
  vertex_injective := vertexCoord_injective
  arc d := ⟨arcCoord G d,by apply continuous_pi; intro x; unfold arcCoord; fun_prop⟩
  arc_injective := arcCoord_injective G
  arc_zero := arcCoord_zero G
  arc_one := arcCoord_one G
  arc_reverse := arcCoord_reverse G
  interior_avoids := arcCoord_avoids G
  interior_disjoint := fun d e s t hs0 hs1 _ _ h => arcCoord_disjoint G d e s t hs0 hs1 h

instance spaceT2 : T2Space (Space G) :=
  T2Space.of_injective_continuous (coordinateDrawing G).map_injective (coordinateDrawing G).map_continuous

theorem embeds_coordinates [Finite V] : EmbedsInto G (V → ℝ) := (coordinateDrawing G).embedsInto

end SimpleGraph.TopologicalRealization

namespace SimpleGraph.TopologicalRealization.Drawing
open scoped unitInterval
variable {V : Type*} {G : SimpleGraph V} {S T : Type*}
  [TopologicalSpace S] [TopologicalSpace T]

def postcompose (D : Drawing G (S := S)) (f : C(S,T)) (hf : Function.Injective f) :
    Drawing G (S := T) where
  vertex := f ∘ D.vertex
  vertex_injective := hf.comp D.vertex_injective
  arc d := f.comp (D.arc d)
  arc_injective d := hf.comp (D.arc_injective d)
  arc_zero d := congrArg f (D.arc_zero d)
  arc_one d := congrArg f (D.arc_one d)
  arc_reverse d t := congrArg f (D.arc_reverse d t)
  interior_avoids d t ht0 ht1 v h := D.interior_avoids d t ht0 ht1 v (hf h)
  interior_disjoint d e s t hs0 hs1 ht0 ht1 h :=
    D.interior_disjoint d e s t hs0 hs1 ht0 ht1 (hf h)

end SimpleGraph.TopologicalRealization.Drawing

namespace SimpleGraph.TopologicalRealization
open scoped unitInterval
variable {V : Type*} (G : SimpleGraph V) [DecidableEq V]

theorem edge_continuous (d : G.Dart) : Continuous (edge G d) := by
  have hc : Continuous (rawEdge G d) := by
    simpa only [rawEdge, fiberTopology] using
      (continuous_sigmaMk (i := Sum.inr d) («σ» := Fiber G))
  exact continuous_quot_mk.comp hc

noncomputable def spaceDrawing : Drawing G (S := Space G) where
  vertex := vertex G
  vertex_injective := by
    intro v w h
    exact vertexCoord_injective (congrArg (coordinateDrawing G).map h)
  arc d := ⟨edge G d,edge_continuous G d⟩
  arc_injective d := by
    intro s t h
    exact arcCoord_injective G d (congrArg (coordinateDrawing G).map h)
  arc_zero := edge_zero G
  arc_one := edge_one G
  arc_reverse := edge_reverse G
  interior_avoids d t ht0 ht1 v h :=
    arcCoord_avoids G d t ht0 ht1 v (congrArg (coordinateDrawing G).map h)
  interior_disjoint d e s t hs0 hs1 _ _ h :=
    arcCoord_disjoint G d e s t hs0 hs1 (congrArg (coordinateDrawing G).map h)

theorem drawing_iff_embeds {S : Type*} [TopologicalSpace S] [T2Space S] [Finite V] :
    Nonempty (Drawing G (S := S)) ↔ EmbedsInto G S := by
  constructor
  · rintro ⟨D⟩
    exact D.embedsInto
  · rintro ⟨f,hf⟩
    exact ⟨(spaceDrawing G).postcompose f hf.injective⟩

end SimpleGraph.TopologicalRealization
