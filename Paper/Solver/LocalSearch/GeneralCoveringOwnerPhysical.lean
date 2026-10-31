import Paper.Solver.LocalSearch.GeneralCoveringOwnerRoutes
import Paper.Solver.LocalSearch.GeneralCoveringOwnerGraphCount
import Paper.Preliminaries.RouteRestriction

/-! Retain represented roots and the actual three internal witnesses per
dart, then restrict the derived guarded routes to the physical induced
graph. The size coefficient follows from physical minor density; no
separator profile or executable routing endpoint is claimed. -/
namespace Paper.GeneralCoveringOwnerPhysical
open SevenFoundation GeneralCoveringTaskGeometry GeneralCoveringOwnerRoutes
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type} [Fintype A] [DecidableEq A]
variable (C : V → Finset V) (D R : Finset V) (L : ℕ) (K : SimpleGraph A) [DecidableRel K.Adj]
variable (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
variable (hedge : ∀ a b, K.Adj a b → (ownerGraph G C D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)
variable (hlocal : ∀ r ∈ R, C r ⊆ closed G r)

noncomputable def vertices : Finset V :=
  Finset.univ.image e ∪ Finset.univ.biUnion (internal G C D R L K e heD hedge)

theorem root_mem (a : A) : e a ∈ vertices G C D R L K e heD hedge :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)

theorem route_mem (d : K.Dart) {z : V}
    (hz : z ∈ (route G C D R L K e heD hedge hlocal d).support) :
    z ∈ vertices G C D R L K e heD hedge := by
  have hm := route_spec G C D R L K e heD hedge hlocal d z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with ha | hl | hm | hr | hb
  · subst z
    exact root_mem G C D R L K e heD hedge d.fst
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_univ _, by simp [internal]⟩)
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_univ _, by simp [internal]⟩)
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨d, Finset.mem_univ _, by simp [internal]⟩)
  · subst z
    exact root_mem G C D R L K e heD hedge d.snd

include hinj in
theorem card_bound : (vertices G C D R L K e heD hedge).card ≤ Fintype.card A + 6 * K.edgeFinset.card := by
  have hu := Finset.card_union_le (Finset.univ.image e)
    (Finset.univ.biUnion (internal G C D R L K e heD hedge))
  have hc : (Finset.univ.biUnion (internal G C D R L K e heD hedge)).card ≤
      3 * Fintype.card K.Dart := by
    calc
      _ ≤ ∑ d : K.Dart, (internal G C D R L K e heD hedge d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d : K.Dart, 3 :=
        Finset.sum_le_sum (fun d _ => internal_card G C D R L K e heD hedge d)
      _ = _ := by simp [mul_comm]
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hu
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hc
  change (vertices G C D R L K e heD hedge).card ≤ _ at hu
  omega

noncomputable def restricted : GuardedRoutes.System K
    (G.induce (vertices G C D R L K e heD hedge : Set V)) :=
  RouteRestriction.restrict (system G C D R L K e hinj heD hedge hlocal)
    (vertices G C D R L K e heD hedge) (root_mem G C D R L K e heD hedge)
    (fun h _ hz => route_mem G C D R L K e heD hedge hlocal ⟨(_, _), h⟩ hz)

theorem restricted_root (a : A) :
    ((restricted G C D R L K e hinj heD hedge hlocal).root a).val = e a := rfl

theorem restricted_injective :
    Function.Injective (restricted G C D R L K e hinj heD hedge hlocal).root :=
  (restricted G C D R L K e hinj heD hedge hlocal).injective

theorem restricted_labels_eq (v : ↥(vertices G C D R L K e heD hedge)) :
    (restricted G C D R L K e hinj heD hedge hlocal).labels v =
      GeneralCoveringOwnerRouteLabels.indexed G C D R L e v.val := rfl

theorem restricted_labels (hL : 1 ≤ L) (v : ↥(vertices G C D R L K e heD hedge)) :
    ((restricted G C D R L K e hinj heD hedge hlocal).labels v).card ≤ L :=
  GeneralCoveringOwnerRouteLabels.indexed_bound G C D R L hL e hinj v.val

theorem restricted_route_map {a b : A} (h : K.Adj a b) :
    ((restricted G C D R L K e hinj heD hedge hlocal).route h).map
        (SimpleGraph.Embedding.induce (vertices G C D R L K e heD hedge : Set V)).toHom =
      route G C D R L K e heD hedge hlocal ⟨(a, b), h⟩ :=
  SimpleGraph.Walk.map_induce (s := (vertices G C D R L K e heD hedge : Set V))
    (route G C D R L K e heD hedge hlocal ⟨(a, b), h⟩)
    (fun _ hz => route_mem G C D R L K e heD hedge hlocal ⟨(a, b), h⟩ hz)

theorem restricted_route_length_eq {a b : A} (h : K.Adj a b) :
    ((restricted G C D R L K e hinj heD hedge hlocal).route h).length =
      (route G C D R L K e heD hedge hlocal ⟨(a, b), h⟩).length := by
  have hh := congrArg SimpleGraph.Walk.length
    (restricted_route_map G C D R L K e hinj heD hedge hlocal h)
  simpa only [SimpleGraph.Walk.length_map] using hh

theorem restricted_route_length {a b : A} (h : K.Adj a b) :
    ((restricted G C D R L K e hinj heD hedge hlocal).route h).length ≤ 4 :=
  (restricted_route_length_eq G C D R L K e hinj heD hedge hlocal h).trans_le
    (route_length G C D R L K e heD hedge hlocal ⟨(a, b), h⟩)

include hinj hlocal in
/-- The size constant is derived from physical minor density through the
received actual-owner finite count, never supplied as an owner oracle. -/
theorem density_size (hL : 1 ≤ L) {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    ((vertices G C D R L K e heD hedge).card : ℝ) ≤
      (1 + 6 * a * ((L + 1 : ℕ) : ℝ) ^ 4) * Fintype.card A := by
  have hw := card_bound G C D R L K e hinj heD hedge
  have hw' : ((vertices G C D R L K e heD hedge).card : ℝ) ≤
      (Fintype.card A : ℝ) + 6 * (K.edgeFinset.card : ℝ) := by exact_mod_cast hw
  have hk := GeneralCoveringOwnerGraphCount.count G C D R L hL K e hinj heD hedge hlocal hden ha
  calc
    _ ≤ (Fintype.card A : ℝ) + 6 * (K.edgeFinset.card : ℝ) := hw'
    _ ≤ (Fintype.card A : ℝ) + 6 * (a * ((L + 1 : ℕ) : ℝ) ^ 4 * Fintype.card A) :=
      add_le_add (le_rfl : (Fintype.card A : ℝ) ≤ Fintype.card A)
        (mul_le_mul_of_nonneg_left hk (show (0 : ℝ) ≤ 6 by norm_num))
    _ = (1 + 6 * a * ((L + 1 : ℕ) : ℝ) ^ 4) * Fintype.card A := by ring

end Paper.GeneralCoveringOwnerPhysical

#print axioms Paper.GeneralCoveringOwnerPhysical.root_mem
#print axioms Paper.GeneralCoveringOwnerPhysical.route_mem
#print axioms Paper.GeneralCoveringOwnerPhysical.card_bound
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_root
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_injective
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_labels_eq
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_labels
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_route_map
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_route_length_eq
#print axioms Paper.GeneralCoveringOwnerPhysical.restricted_route_length
#print axioms Paper.GeneralCoveringOwnerPhysical.density_size
