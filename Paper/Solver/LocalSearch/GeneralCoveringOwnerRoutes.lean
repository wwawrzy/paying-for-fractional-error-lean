import Paper.Solver.LocalSearch.GeneralCoveringOwnerRouteLabels
import Paper.Preliminaries.ShortChains
import Paper.Preliminaries.GuardedRoutes

/-! Actual physical routes for the gated arbitrary-C owner graph. The
three internal witnesses remain explicit for subsequent retained-vertex
counting. No route, separator, cover or default-owner oracle is input. -/
namespace Paper.GeneralCoveringOwnerRoutes
open SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Witness (C : V → Finset V) (D R : Finset V) (L : ℕ) (a b : V) where
  left : V
  mid : V
  right : V
  a_mem : a ∈ D
  b_mem : b ∈ D
  admissible : mid ∈ CoveringSupport.admissible C R
  light : mid ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  mid_a : a ∈ GeneralCoveringOwnerSupport.support G C D R mid
  mid_b : b ∈ GeneralCoveringOwnerSupport.support G C D R mid
  left_owned : left ∈ R ∪ D
  right_owned : right ∈ R ∪ D
  left_label : GeneralCoveringOwners.owner C D R left = some a
  right_label : GeneralCoveringOwners.owner C D R right = some b
  left_closed : left ∈ closed G mid
  right_closed : right ∈ closed G mid

theorem exists_witness (C : V → Finset V) (D R : Finset V) (L : ℕ) {a b : D}
    (h : (ownerGraph G C D R L).Adj a b) : Nonempty (Witness G C D R L a.val b.val) := by
  obtain ⟨_, v, ha, hb⟩ := h
  have ha' := (mem_lightSupport G C D R L v a.val).mp ha
  have hb' := (mem_lightSupport G C D R L v b.val).mp hb
  obtain ⟨u, hu, hua⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v a.val).mp ha'.2.2
  obtain ⟨w, hw, hwb⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v b.val).mp hb'.2.2
  exact ⟨{
    left := u, mid := v, right := w, a_mem := a.property, b_mem := b.property,
    admissible := ha'.1, light := ha'.2.1, mid_a := ha'.2.2, mid_b := hb'.2.2,
    left_owned := GeneralCoveringOwners.owner_domain C D R hua,
    right_owned := GeneralCoveringOwners.owner_domain C D R hwb,
    left_label := hua, right_label := hwb, left_closed := hu, right_closed := hw }⟩

theorem route_exists {C : V → Finset V} {D R : Finset V} {L : ℕ} {a b : V}
    (W : Witness G C D R L a b) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    ∃ p : G.Walk a b, p.length ≤ 4 ∧
      ∀ z ∈ p.support, z ∈ ({a, W.left, W.mid, W.right, b} : Finset V) := by
  apply ShortChains.chain5 G a W.left W.mid W.right b
  · exact GeneralCoveringOwners.owner_star G C D R hlocal W.left_label
  · exact ((mem_closed G W.left W.mid).mp W.left_closed).elim Or.inl (fun ha => Or.inr ha.symm)
  · exact ((mem_closed G W.right W.mid).mp W.right_closed).elim (fun he => Or.inl he.symm) Or.inr
  · exact (GeneralCoveringOwners.owner_star G C D R hlocal W.right_label).elim
      (fun he => Or.inl he.symm) (fun ha => Or.inr ha.symm)

theorem labels_guard {C : V → Finset V} {D R : Finset V} {L : ℕ} {a b : V}
    (W : Witness G C D R L a b) {z : V}
    (hz : z ∈ ({a, W.left, W.mid, W.right, b} : Finset V)) :
    a ∈ GeneralCoveringOwnerRouteLabels.labels G C D R L z ∨
      b ∈ GeneralCoveringOwnerRouteLabels.labels G C D R L z := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with ha | hl | hm | hr | hb
  · subst z
    exact Or.inl (GeneralCoveringOwnerRouteLabels.root_label G C D R L W.a_mem)
  · subst z
    exact Or.inl (GeneralCoveringOwnerRouteLabels.owner_label G C D R L W.left_label)
  · subst z
    exact Or.inl (GeneralCoveringOwnerRouteLabels.light_label G C D R L W.admissible W.light W.mid_a)
  · subst z
    exact Or.inr (GeneralCoveringOwnerRouteLabels.owner_label G C D R L W.right_label)
  · subst z
    exact Or.inr (GeneralCoveringOwnerRouteLabels.root_label G C D R L W.b_mem)

variable {A : Type*} [Fintype A] [DecidableEq A]
variable (C : V → Finset V) (D R : Finset V) (L : ℕ) (K : SimpleGraph A) [DecidableRel K.Adj]
variable (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
variable (hedge : ∀ a b, K.Adj a b → (ownerGraph G C D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)
variable (hlocal : ∀ r ∈ R, C r ⊆ closed G r)

noncomputable def witness (d : K.Dart) : Witness G C D R L (e d.fst) (e d.snd) :=
  Classical.choice (exists_witness G C D R L (hedge _ _ d.adj))

noncomputable def internal (d : K.Dart) : Finset V :=
  {(witness G C D R L K e heD hedge d).left, (witness G C D R L K e heD hedge d).mid,
    (witness G C D R L K e heD hedge d).right}

theorem internal_card (d : K.Dart) : (internal G C D R L K e heD hedge d).card ≤ 3 := by
  let W := witness G C D R L K e heD hedge d
  change ({W.left, W.mid, W.right} : Finset V).card ≤ 3
  have h₁ := Finset.card_insert_le W.left ({W.mid, W.right} : Finset V)
  have h₂ := Finset.card_insert_le W.mid ({W.right} : Finset V)
  simp only [Finset.card_singleton] at h₂
  omega

noncomputable def route (d : K.Dart) : G.Walk (e d.fst) (e d.snd) :=
  (route_exists G (witness G C D R L K e heD hedge d) hlocal).choose

theorem route_spec (d : K.Dart) : ∀ z ∈ (route G C D R L K e heD hedge hlocal d).support,
    z ∈ ({e d.fst, (witness G C D R L K e heD hedge d).left,
      (witness G C D R L K e heD hedge d).mid,
      (witness G C D R L K e heD hedge d).right, e d.snd} : Finset V) :=
  (route_exists G (witness G C D R L K e heD hedge d) hlocal).choose_spec.2

theorem route_length (d : K.Dart) : (route G C D R L K e heD hedge hlocal d).length ≤ 4 :=
  (route_exists G (witness G C D R L K e heD hedge d) hlocal).choose_spec.1

theorem route_guarded (d : K.Dart) (z : V) (hz : z ∈ (route G C D R L K e heD hedge hlocal d).support) :
    e d.fst ∈ GeneralCoveringOwnerRouteLabels.labels G C D R L z ∨
      e d.snd ∈ GeneralCoveringOwnerRouteLabels.labels G C D R L z :=
  labels_guard G (witness G C D R L K e heD hedge d)
    (route_spec G C D R L K e heD hedge hlocal d z hz)

/-- All routes and guards are constructed from actual owner witnesses.
The embedding is proof-side data, not an executable partition input. -/
noncomputable def system : GuardedRoutes.System K G where
  root := e
  injective := hinj
  labels := GeneralCoveringOwnerRouteLabels.indexed G C D R L e
  root_label a := (GeneralCoveringOwnerRouteLabels.mem_indexed G C D R L e (e a) a).mpr
    (GeneralCoveringOwnerRouteLabels.root_label G C D R L (heD a))
  route h := route G C D R L K e heD hedge hlocal ⟨(_, _), h⟩
  guarded h v hv := by
    rcases route_guarded G C D R L K e heD hedge hlocal ⟨(_, _), h⟩ v hv with ha | hb
    · exact Or.inl ((GeneralCoveringOwnerRouteLabels.mem_indexed G C D R L e v _).mpr ha)
    · exact Or.inr ((GeneralCoveringOwnerRouteLabels.mem_indexed G C D R L e v _).mpr hb)

theorem label_bound (hL : 1 ≤ L) (v : V) :
    ((system G C D R L K e hinj heD hedge hlocal).labels v).card ≤ L :=
  GeneralCoveringOwnerRouteLabels.indexed_bound G C D R L hL e hinj v

end Paper.GeneralCoveringOwnerRoutes

#print axioms Paper.GeneralCoveringOwnerRoutes.exists_witness
#print axioms Paper.GeneralCoveringOwnerRoutes.route_exists
#print axioms Paper.GeneralCoveringOwnerRoutes.labels_guard
#print axioms Paper.GeneralCoveringOwnerRoutes.witness
#print axioms Paper.GeneralCoveringOwnerRoutes.internal_card
#print axioms Paper.GeneralCoveringOwnerRoutes.route
#print axioms Paper.GeneralCoveringOwnerRoutes.route_spec
#print axioms Paper.GeneralCoveringOwnerRoutes.route_length
#print axioms Paper.GeneralCoveringOwnerRoutes.route_guarded
#print axioms Paper.GeneralCoveringOwnerRoutes.system
#print axioms Paper.GeneralCoveringOwnerRoutes.label_bound
