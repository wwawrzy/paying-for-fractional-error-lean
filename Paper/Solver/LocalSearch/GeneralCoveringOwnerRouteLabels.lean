import Paper.Solver.LocalSearch.GeneralCoveringTaskGeometry

/-! Separator labels for actual optional C-owners. Full physical S0 is
used only at light admissible vertices. Every other vertex keeps only its
own optional label; none supplies no default identifier. Guarded routes and
physical separator/profile constructions are separate subsequent gates. -/
namespace Paper.GeneralCoveringOwnerRouteLabels
open SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def labels (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) : Finset V :=
  if v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L then
    GeneralCoveringOwnerSupport.support G C D R v
  else (GeneralCoveringOwners.owner C D R v).toFinset

theorem mem_labels (C : V → Finset V) (D R : Finset V) (L : ℕ) (v d : V) :
    d ∈ labels G C D R L v ↔
      ((v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L) ∧
        d ∈ GeneralCoveringOwnerSupport.support G C D R v) ∨
      (¬ (v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L) ∧
        GeneralCoveringOwners.owner C D R v = some d) := by
  by_cases hv : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · simp [labels, hv]
  · cases ho : GeneralCoveringOwners.owner C D R v <;> simp [labels, hv, ho, eq_comm]

theorem labels_eq_light (C : V → Finset V) (D R : Finset V) (L : ℕ) {v : V}
    (hv : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L) :
    labels G C D R L v = lightSupport G C D R L v := by
  rw [labels, if_pos hv, lightSupport, if_pos hv]

theorem labels_eq_own (C : V → Finset V) (D R : Finset V) (L : ℕ) {v : V}
    (hv : ¬ (v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L)) :
    labels G C D R L v = (GeneralCoveringOwners.owner C D R v).toFinset := by
  rw [labels, if_neg hv]

theorem nonadmissible_labels (C : V → Finset V) (D R : Finset V) (L : ℕ) {v : V}
    (hv : v ∉ CoveringSupport.admissible C R) :
    labels G C D R L v = (GeneralCoveringOwners.owner C D R v).toFinset :=
  labels_eq_own G C D R L (fun h => hv h.1)

theorem nonadmissible_some (C : V → Finset V) (D R : Finset V) (L : ℕ) {v d : V}
    (hv : v ∉ CoveringSupport.admissible C R)
    (ho : GeneralCoveringOwners.owner C D R v = some d) : labels G C D R L v = {d} := by
  rw [nonadmissible_labels G C D R L hv]
  simp only [ho, Option.toFinset_some]

theorem nongated_none (C : V → Finset V) (D R : Finset V) (L : ℕ) {v : V}
    (hv : ¬ (v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L))
    (ho : GeneralCoveringOwners.owner C D R v = none) : labels G C D R L v = ∅ := by
  rw [labels_eq_own G C D R L hv]
  simp only [ho, Option.toFinset_none]

theorem card_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (v : V) :
    (labels G C D R L v).card ≤ L := by
  by_cases hv : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · rw [labels_eq_light G C D R L hv]
    exact lightSupport_bound G C D R L v
  · rw [labels_eq_own G C D R L hv]
    have hc : (GeneralCoveringOwners.owner C D R v).toFinset.card ≤ 1 := by
      cases GeneralCoveringOwners.owner C D R v <;> simp
    exact hc.trans hL

theorem labels_subset (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) :
    labels G C D R L v ⊆ D := by
  intro d hd
  rcases (mem_labels G C D R L v d).mp hd with hl | ho
  · exact GeneralCoveringOwnerSupport.support_labels G C D R v hl.2
  · exact GeneralCoveringOwners.owner_mem C D R ho.2

theorem owner_label (C : V → Finset V) (D R : Finset V) (L : ℕ) {v d : V}
    (ho : GeneralCoveringOwners.owner C D R v = some d) : d ∈ labels G C D R L v := by
  apply (mem_labels G C D R L v d).mpr
  by_cases hv : v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · exact Or.inl ⟨hv, (GeneralCoveringOwnerSupport.mem_support G C D R v d).mpr
      ⟨v, self_mem_closed G v, ho⟩⟩
  · exact Or.inr ⟨hv, ho⟩

theorem root_label (C : V → Finset V) (D R : Finset V) (L : ℕ) {d : V} (hd : d ∈ D) :
    d ∈ labels G C D R L d :=
  owner_label G C D R L (GeneralCoveringOwners.owner_center C D R hd)

theorem light_label (C : V → Finset V) (D R : Finset V) (L : ℕ) {v d : V}
    (hv : v ∈ CoveringSupport.admissible C R) (hn : v ∉ GeneralCoveringOwnerSupport.heavy G C D R L)
    (hd : d ∈ GeneralCoveringOwnerSupport.support G C D R v) : d ∈ labels G C D R L v :=
  (mem_labels G C D R L v d).mpr (Or.inl ⟨⟨hv, hn⟩, hd⟩)

theorem lightSupport_subset (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) :
    lightSupport G C D R L v ⊆ labels G C D R L v := by
  intro d hd
  have hh := (mem_lightSupport G C D R L v d).mp hd
  exact light_label G C D R L hh.1 hh.2.1 hh.2.2

noncomputable def indexed {A : Type*} [Fintype A] (C : V → Finset V) (D R : Finset V)
    (L : ℕ) (e : A → V) (v : V) : Finset A :=
  Finset.univ.filter (fun a => e a ∈ labels G C D R L v)

theorem mem_indexed {A : Type*} [Fintype A] (C : V → Finset V) (D R : Finset V)
    (L : ℕ) (e : A → V) (v : V) (a : A) :
    a ∈ indexed G C D R L e v ↔ e a ∈ labels G C D R L v := by
  simp only [indexed, Finset.mem_filter, Finset.mem_univ, true_and]

theorem indexed_labels {A : Type*} [Fintype A] (C : V → Finset V) (D R : Finset V)
    (L : ℕ) (e : A → V) (v : V) {a : A} (ha : a ∈ indexed G C D R L e v) : e a ∈ D :=
  labels_subset G C D R L v ((mem_indexed G C D R L e v a).mp ha)

theorem indexed_bound {A : Type*} [Fintype A] (C : V → Finset V) (D R : Finset V)
    (L : ℕ) (hL : 1 ≤ L) (e : A → V) (hinj : Function.Injective e) (v : V) :
    (indexed G C D R L e v).card ≤ L := by
  have hc := Finset.card_le_card_of_injOn e
    (s := indexed G C D R L e v) (t := labels G C D R L v)
    (fun a ha => (mem_indexed G C D R L e v a).mp ha) (fun _ _ _ _ h => hinj h)
  exact hc.trans (card_bound G C D R L hL v)

end Paper.GeneralCoveringOwnerRouteLabels

#print axioms Paper.GeneralCoveringOwnerRouteLabels.mem_labels
#print axioms Paper.GeneralCoveringOwnerRouteLabels.labels_eq_light
#print axioms Paper.GeneralCoveringOwnerRouteLabels.labels_eq_own
#print axioms Paper.GeneralCoveringOwnerRouteLabels.nonadmissible_labels
#print axioms Paper.GeneralCoveringOwnerRouteLabels.nonadmissible_some
#print axioms Paper.GeneralCoveringOwnerRouteLabels.nongated_none
#print axioms Paper.GeneralCoveringOwnerRouteLabels.card_bound
#print axioms Paper.GeneralCoveringOwnerRouteLabels.labels_subset
#print axioms Paper.GeneralCoveringOwnerRouteLabels.owner_label
#print axioms Paper.GeneralCoveringOwnerRouteLabels.root_label
#print axioms Paper.GeneralCoveringOwnerRouteLabels.light_label
#print axioms Paper.GeneralCoveringOwnerRouteLabels.lightSupport_subset
#print axioms Paper.GeneralCoveringOwnerRouteLabels.mem_indexed
#print axioms Paper.GeneralCoveringOwnerRouteLabels.indexed_labels
#print axioms Paper.GeneralCoveringOwnerRouteLabels.indexed_bound
