import Paper.Owners.Construction.OwnerPhysicalVertices

/-! One guarded physical route per undirected owner edge, used in reverse
for the opposite direction. Only three extra vertices per edge are retained. -/
namespace Paper.OwnerUndirectedRoutes
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerRouteSystem
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable local instance vertexLT : DecidableLT V := fun x y => Classical.propDecidable (x < y)
variable {A : Type} [Fintype A] [DecidableEq A]
variable (D R : Finset V) (L : ℕ) (K : SimpleGraph A) [DecidableRel K.Adj]
variable (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
variable (hedge : ∀ a b, K.Adj a b → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)

noncomputable def forward : Finset K.Dart := Finset.univ.filter (fun d => e d.fst < e d.snd)

include hinj in
theorem reverse_forward (d : K.Dart) (hd : ¬e d.fst < e d.snd) :
    d.symm ∈ forward K e := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hne : e d.fst ≠ e d.snd := fun he => d.adj.ne (hinj he)
  change e d.snd < e d.fst
  exact lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm hne)

include hinj in
theorem forward_card : (forward K e).card = K.edgeFinset.card := by
  classical
  let N := Finset.univ.filter (fun d : K.Dart => ¬e d.fst < e d.snd)
  have he : (forward K e).card = N.card := by
    refine Finset.card_bij (fun d _ => d.symm) ?_ ?_ ?_
    · intro d hd
      have hh := (Finset.mem_filter.mp hd).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change ¬e d.snd < e d.fst; exact not_lt_of_ge hh.le⟩
    · intro d _ f _ hdf
      simpa only [SimpleGraph.Dart.symm_symm] using congrArg SimpleGraph.Dart.symm hdf
    · intro d hd
      exact ⟨d.symm, reverse_forward K e hinj d (Finset.mem_filter.mp hd).2,
        SimpleGraph.Dart.symm_symm d⟩
  have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset K.Dart))
    (fun d => e d.fst < e d.snd)
  change (forward K e).card+N.card = _ at hh
  rw [Finset.card_univ, SimpleGraph.dart_card_eq_twice_card_edges] at hh
  omega

noncomputable def internal (d : K.Dart) : Finset V :=
  OwnerPhysicalVertices.internal G D R L K e heD hedge d

noncomputable def vertices : Finset V :=
  Finset.univ.image e ∪ (forward K e).biUnion (internal G D R L K e heD hedge)

theorem root_mem (a : A) : e a ∈ vertices G D R L K e heD hedge :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)

theorem raw_route_mem (d : K.Dart) (hd : d ∈ forward K e) {z : V}
    (hz : z ∈ (OwnerRouteSystem.route G D R L K e heD hedge d).support) :
    z ∈ vertices G D R L K e heD hedge := by
  have hm := OwnerRouteSystem.route_spec G D R L K e heD hedge d z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4
  · subst z; exact root_mem G D R L K e heD hedge d.fst
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, by simp [internal, OwnerPhysicalVertices.internal]⟩)
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, by simp [internal, OwnerPhysicalVertices.internal]⟩)
  · subst z
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, by simp [internal, OwnerPhysicalVertices.internal]⟩)
  · subst z; exact root_mem G D R L K e heD hedge d.snd

noncomputable def route (d : K.Dart) : G.Walk (e d.fst) (e d.snd) :=
  if e d.fst < e d.snd then OwnerRouteSystem.route G D R L K e heD hedge d
  else (OwnerRouteSystem.route G D R L K e heD hedge d.symm).reverse

include hinj in
theorem route_mem (d : K.Dart) {z : V} (hz : z ∈ (route G D R L K e heD hedge d).support) :
    z ∈ vertices G D R L K e heD hedge := by
  unfold route at hz
  split_ifs at hz with hd
  · exact raw_route_mem G D R L K e heD hedge d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩) hz
  · exact raw_route_mem G D R L K e heD hedge d.symm
      (reverse_forward K e hinj d hd)
      (List.mem_reverse.mp ((SimpleGraph.Walk.support_reverse (OwnerRouteSystem.route G D R L K e heD hedge d.symm)) ▸ hz))

include hinj in
theorem card_bound : (vertices G D R L K e heD hedge).card ≤ Fintype.card A+3*K.edgeFinset.card := by
  have hu := Finset.card_union_le (Finset.univ.image e)
    ((forward K e).biUnion (internal G D R L K e heD hedge))
  have hc : ((forward K e).biUnion (internal G D R L K e heD hedge)).card ≤ 3*(forward K e).card := by
    calc
      _ ≤ ∑ d ∈ forward K e, (internal G D R L K e heD hedge d).card := Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ forward K e, 3 := Finset.sum_le_sum (fun d _ => OwnerPhysicalVertices.internal_card G D R L K e heD hedge d)
      _ = _ := by simp [mul_comm]
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ] at hu
  rw [forward_card K e hinj] at hc
  change (vertices G D R L K e heD hedge).card ≤ _ at hu
  omega

noncomputable def system : GuardedRoutes.System K G where
  root := e
  injective := hinj
  labels := OwnerRouteLabels.indexed G D R L e
  root_label a := (OwnerRouteSystem.system G D R L K e hinj heD hedge).root_label a
  route h := route G D R L K e heD hedge ⟨(_, _), h⟩
  guarded := by
    intro a b h v hv
    unfold route at hv
    split_ifs at hv with he
    · exact (OwnerRouteSystem.system G D R L K e hinj heD hedge).guarded h v hv
    · have hm : v ∈ (OwnerRouteSystem.route G D R L K e heD hedge ⟨(b,a), h.symm⟩).support := by
        exact List.mem_reverse.mp ((SimpleGraph.Walk.support_reverse (OwnerRouteSystem.route G D R L K e heD hedge ⟨(b,a), h.symm⟩)) ▸ hv)
      rcases (OwnerRouteSystem.system G D R L K e hinj heD hedge).guarded h.symm v hm with hb | ha
      · exact Or.inr hb
      · exact Or.inl ha

noncomputable def restricted : GuardedRoutes.System K
    (G.induce (vertices G D R L K e heD hedge : Set V)) :=
  RouteRestriction.restrict (system G D R L K e hinj heD hedge)
    (vertices G D R L K e heD hedge) (root_mem G D R L K e heD hedge)
    (fun h _ hz => route_mem G D R L K e hinj heD hedge ⟨(_, _), h⟩ hz)

theorem label_bound (hL : 1 ≤ L) (v : vertices G D R L K e heD hedge) :
    ((restricted G D R L K e hinj heD hedge).labels v).card ≤ L :=
  OwnerRouteLabels.indexed_bound G D R L hL e hinj v.val

end Paper.OwnerUndirectedRoutes
