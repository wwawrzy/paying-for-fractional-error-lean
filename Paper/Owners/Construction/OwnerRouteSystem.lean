import Paper.Owners.Construction.OwnerRouteWitness
import Paper.Preliminaries.GuardedRoutes

/-! Build the actual guarded physical route system for any graph represented
injectively by owner labels and augmented owner edges. -/
namespace Paper.OwnerRouteSystem
attribute [local instance] Classical.propDecidable Classical.decEq
open GuardedRoutes
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable (D R : Finset V) (L : ℕ) (K : SimpleGraph A) [DecidableRel K.Adj]
variable (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
variable (hedge : ∀ a b, K.Adj a b → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)

noncomputable def witness (d : K.Dart) : OwnerRouteWitness.Witness G D R L (e d.fst) (e d.snd) :=
  Classical.choice (OwnerRouteWitness.exists_witness G D R L (hedge _ _ d.adj))

noncomputable def route (d : K.Dart) : G.Walk (e d.fst) (e d.snd) :=
  (OwnerRouteWitness.route_exists G (witness G D R L K e heD hedge d)).choose

theorem route_spec (d : K.Dart) : ∀ z ∈ (route G D R L K e heD hedge d).support,
    z ∈ ({e d.fst, (witness G D R L K e heD hedge d).left,
      (witness G D R L K e heD hedge d).mid, (witness G D R L K e heD hedge d).right, e d.snd} : Finset V) :=
  (OwnerRouteWitness.route_exists G (witness G D R L K e heD hedge d)).choose_spec

noncomputable def system : System K G where
  root := e
  injective := hinj
  labels := OwnerRouteLabels.indexed G D R L e
  root_label a := (OwnerRouteLabels.mem_indexed G D R L e (e a) a).mpr
    (OwnerRouteLabels.root_label G D R L (heD a))
  route h := route G D R L K e heD hedge ⟨(_, _), h⟩
  guarded h v hv := by
    have hm := route_spec G D R L K e heD hedge ⟨(_, _), h⟩ v hv
    rcases OwnerRouteWitness.labels_guard G (witness G D R L K e heD hedge ⟨(_, _), h⟩) hm with ha | hb
    · exact Or.inl ((OwnerRouteLabels.mem_indexed G D R L e v _).mpr ha)
    · exact Or.inr ((OwnerRouteLabels.mem_indexed G D R L e v _).mpr hb)

theorem label_bound (hL : 1 ≤ L) (v : V) :
    ((system G D R L K e hinj heD hedge).labels v).card ≤ L :=
  OwnerRouteLabels.indexed_bound G D R L hL e hinj v
end Paper.OwnerRouteSystem
