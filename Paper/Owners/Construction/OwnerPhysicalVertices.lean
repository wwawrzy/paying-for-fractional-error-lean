import Paper.Owners.Construction.OwnerRouteSystem
import Paper.Preliminaries.RouteRestriction

/-! Retain precisely the owner roots and three internal witnesses per dart.
There are at most |owners|+6|edges| retained physical vertices. -/
namespace Paper.OwnerPhysicalVertices
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerRouteSystem
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable (D R : Finset V) (L : ℕ) (K : SimpleGraph A) [DecidableRel K.Adj]
variable (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
variable (hedge : ∀ a b, K.Adj a b → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)

noncomputable def internal (d : K.Dart) : Finset V :=
  {(witness G D R L K e heD hedge d).left, (witness G D R L K e heD hedge d).mid,
    (witness G D R L K e heD hedge d).right}

noncomputable def vertices : Finset V :=
  Finset.univ.image e ∪ Finset.univ.biUnion (internal G D R L K e heD hedge)

theorem root_mem (a : A) : e a ∈ vertices G D R L K e heD hedge :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)

theorem route_mem (d : K.Dart) {z : V} (hz : z ∈ (route G D R L K e heD hedge d).support) :
    z ∈ vertices G D R L K e heD hedge := by
  have hm := route_spec G D R L K e heD hedge d z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with ha | hl | hm | hr | hb
  · subst z; exact root_mem G D R L K e heD hedge d.fst
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, by simp [internal]⟩)
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, by simp [internal]⟩)
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, by simp [internal]⟩)
  · subst z; exact root_mem G D R L K e heD hedge d.snd

theorem internal_card (d : K.Dart) : (internal G D R L K e heD hedge d).card ≤ 3 := by
  let W := witness G D R L K e heD hedge d
  have h₀ := Finset.card_insert_le W.left ({W.mid, W.right} : Finset V)
  have h₁ := Finset.card_insert_le W.mid ({W.right} : Finset V)
  simp only [Finset.card_singleton] at h₁
  change ({W.left, W.mid, W.right} : Finset V).card ≤ 3
  omega

include hinj in
theorem card_bound : (vertices G D R L K e heD hedge).card ≤ Fintype.card A + 6 * K.edgeFinset.card := by
  classical
  have hu := Finset.card_union_le (Finset.univ.image e)
    (Finset.univ.biUnion (internal G D R L K e heD hedge))
  have hc : (Finset.univ.biUnion (internal G D R L K e heD hedge)).card ≤ 3 * Fintype.card K.Dart := by
    calc
      _ ≤ ∑ d : K.Dart, (internal G D R L K e heD hedge d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d : K.Dart, 3 := Finset.sum_le_sum (fun d _ => internal_card G D R L K e heD hedge d)
      _ = _ := by simp [mul_comm]
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hu
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hc
  change (vertices G D R L K e heD hedge).card ≤ _ at hu
  omega

noncomputable def restricted : GuardedRoutes.System K
    (G.induce (vertices G D R L K e heD hedge : Set V)) :=
  RouteRestriction.restrict (OwnerRouteSystem.system G D R L K e hinj heD hedge)
    (vertices G D R L K e heD hedge) (root_mem G D R L K e heD hedge)
    (fun h _ hz => route_mem G D R L K e heD hedge ⟨(_, _), h⟩ hz)

theorem restricted_labels (hL : 1 ≤ L) (v : vertices G D R L K e heD hedge) :
    ((restricted G D R L K e hinj heD hedge).labels v).card ≤ L :=
  OwnerRouteLabels.indexed_bound G D R L hL e hinj v.val
end Paper.OwnerPhysicalVertices
