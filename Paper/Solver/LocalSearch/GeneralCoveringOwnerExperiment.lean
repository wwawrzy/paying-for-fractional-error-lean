import Paper.Solver.LocalSearch.GeneralCoveringTaskGeometry
import Paper.Preliminaries.BlowupEdge

/-! A finite proof-side experiment for actual optional C-owners. Selected
owner stars are retained in full. Other vertices can attach only through a
sampled label in their light admissible S0. Each outcome is a physical minor;
survival probabilities and hereditary owner density are separate gates. -/
namespace Paper.GeneralCoveringOwnerExperiment
open SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def sampled {c : ℕ} (D : Finset V) (ω : V ⊕ V → Fin c) : Finset V :=
  D.filter (fun d => (ω (.inl d)).val = 0)

theorem sampled_subset {c : ℕ} (D : Finset V) (ω : V ⊕ V → Fin c) :
    sampled D ω ⊆ D := Finset.filter_subset _ _

noncomputable def pick {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) (v : V) : Option V :=
  ((lightSupport G C D R L v).sort (· ≤ ·))[(ω (.inr v)).val]?

/-- Base ownership is optional: none never supplies a default center. -/
noncomputable def label {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) (v : V) : Option V :=
  if ∃ d, GeneralCoveringOwners.owner C D R v = some d ∧ d ∈ sampled D ω then
    GeneralCoveringOwners.owner C D R v
  else
    match pick G C D R L ω v with
    | none => none
    | some d => if d ∈ sampled D ω then some d else none

theorem label_base {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v d : V}
    (ho : GeneralCoveringOwners.owner C D R v = some d) (hd : d ∈ sampled D ω) :
    label G C D R L ω v = some d := by
  have hb : ∃ e, GeneralCoveringOwners.owner C D R v = some e ∧ e ∈ sampled D ω :=
    ⟨d, ho, hd⟩
  rw [label, if_pos hb]
  exact ho

theorem label_center {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {d : V} (hd : d ∈ sampled D ω) :
    label G C D R L ω d = some d :=
  label_base G C D R L ω
    (GeneralCoveringOwners.owner_center C D R (sampled_subset D ω hd)) hd

theorem label_fiber {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {d v : V} (hd : d ∈ sampled D ω)
    (hv : v ∈ GeneralCoveringOwners.fiber C D R d) :
    label G C D R L ω v = some d :=
  label_base G C D R L ω (Finset.mem_filter.mp hv).2 hd

theorem pick_mem {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v d : V} (h : pick G C D R L ω v = some d) :
    d ∈ lightSupport G C D R L v :=
  (Finset.mem_sort (· ≤ ·)).mp (List.mem_iff_getElem?.mpr ⟨(ω (.inr v)).val, h⟩)

theorem label_cases {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v d : V} (h : label G C D R L ω v = some d) :
    (GeneralCoveringOwners.owner C D R v = some d ∧ d ∈ sampled D ω) ∨
      (v ∈ CoveringSupport.admissible C R ∧
        v ∉ GeneralCoveringOwnerSupport.heavy G C D R L ∧
        d ∈ GeneralCoveringOwnerSupport.support G C D R v ∧ d ∈ sampled D ω) := by
  by_cases hb : ∃ e, GeneralCoveringOwners.owner C D R v = some e ∧ e ∈ sampled D ω
  · rw [label, if_pos hb] at h
    obtain ⟨e, ho, he⟩ := hb
    rw [ho] at h
    have hed := Option.some.inj h
    exact Or.inl ⟨hed ▸ ho, hed ▸ he⟩
  · rw [label, if_neg hb] at h
    cases hp : pick G C D R L ω v with
    | none => simp [hp] at h
    | some e =>
      rw [hp] at h
      change (if e ∈ sampled D ω then some e else none) = some d at h
      by_cases he : e ∈ sampled D ω
      · rw [if_pos he] at h
        have hed := Option.some.inj h
        have hm := (mem_lightSupport G C D R L v e).mp (pick_mem G C D R L ω hp)
        exact Or.inr ⟨hm.1, hm.2.1, hed ▸ hm.2.2, hed ▸ he⟩
      · simp [he] at h

theorem label_sampled {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v d : V} (h : label G C D R L ω v = some d) :
    d ∈ sampled D ω :=
  (label_cases G C D R L ω h).elim And.right (fun ha => ha.2.2.2)

theorem label_owner_none_cases {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v d : V}
    (ho : GeneralCoveringOwners.owner C D R v = none)
    (h : label G C D R L ω v = some d) :
    v ∈ CoveringSupport.admissible C R ∧
      v ∉ GeneralCoveringOwnerSupport.heavy G C D R L ∧
      d ∈ GeneralCoveringOwnerSupport.support G C D R v ∧ d ∈ sampled D ω := by
  rcases label_cases G C D R L ω h with hb | ha
  · rw [ho] at hb
    cases hb.1
  · exact ha

theorem label_none_nongated {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v : V}
    (ho : GeneralCoveringOwners.owner C D R v = none)
    (hn : ¬ (v ∈ CoveringSupport.admissible C R ∧
      v ∉ GeneralCoveringOwnerSupport.heavy G C D R L)) :
    label G C D R L ω v = none := by
  cases hl : label G C D R L ω v with
  | none => rfl
  | some d =>
    exfalso
    have hc := label_owner_none_cases G C D R L ω ho hl
    exact hn ⟨hc.1, hc.2.1⟩

noncomputable def graph {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) : SimpleGraph (sampled D ω) where
  Adj a b := a ≠ b ∧ BlowupEdge.Crosses G (label G C D R L ω) a.val b.val
  symm := by rintro a b ⟨hne, u, v, hu, hv, ha⟩; exact ⟨hne.symm, v, u, hv, hu, ha.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Every sampled-label branch is connected through its retained center.
No owner map, minor, forest or density witness is supplied as input. -/
noncomputable def model {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    SimpleGraph.MinorModel (graph G C D R L ω) G where
  branchSet a := {v | label G C D R L ω v = some a.val}
  nonempty a := ⟨a.val, label_center G C D R L ω a.property⟩
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v ha hb
    exact hab (Subtype.ext (Option.some.inj (ha.symm.trans hb)))
  connected a := by
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    let root : {v // label G C D R L ω v = some a.val} :=
      ⟨a.val, label_center G C D R L ω a.property⟩
    refine ⟨root, ?_⟩
    have base : ∀ u (hu : GeneralCoveringOwners.owner C D R u = some a.val),
        ∃ hl : label G C D R L ω u = some a.val,
          (G.induce {v | label G C D R L ω v = some a.val}).Reachable root ⟨u, hl⟩ := by
      intro u hu
      have hl := label_base G C D R L ω hu a.property
      refine ⟨hl, ?_⟩
      rcases GeneralCoveringOwners.owner_star G C D R hlocal hu with he | ha
      · have hv : root = (⟨u, hl⟩ : {v // label G C D R L ω v = some a.val}) :=
          Subtype.ext he
        rw [hv]
        exact SimpleGraph.Reachable.refl _
      · exact (show (G.induce {v | label G C D R L ω v = some a.val}).Adj
          root ⟨u, hl⟩ from ha).reachable
    intro v
    rcases label_cases G C D R L ω v.property with hb | ha
    · obtain ⟨hl, hr⟩ := base v.val hb.1
      exact hr
    · obtain ⟨u, hu, hud⟩ :=
        (GeneralCoveringOwnerSupport.mem_support G C D R v.val a.val).mp ha.2.2.1
      obtain ⟨hl, hr⟩ := base u hud
      rcases (mem_closed G u v.val).mp hu with he | hadj
      · simpa only [he] using hr
      · have hadj' : (G.induce {v | label G C D R L ω v = some a.val}).Adj ⟨u, hl⟩ v :=
          hadj.symm
        exact hr.trans hadj'.reachable
  adjacent a b hab := by
    obtain ⟨_, u, v, hu, hv, ha⟩ := hab
    exact ⟨u, hu, v, hv, ha⟩

theorem retained_center {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (a : sampled D ω) : a.val ∈ (model G C D R L ω hlocal).branchSet a :=
  label_center G C D R L ω a.property

theorem isMinor {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    SimpleGraph.IsMinor (graph G C D R L ω) G := ⟨model G C D R L ω hlocal⟩

end Paper.GeneralCoveringOwnerExperiment

#print axioms Paper.GeneralCoveringOwnerExperiment.sampled_subset
#print axioms Paper.GeneralCoveringOwnerExperiment.label_base
#print axioms Paper.GeneralCoveringOwnerExperiment.label_center
#print axioms Paper.GeneralCoveringOwnerExperiment.label_fiber
#print axioms Paper.GeneralCoveringOwnerExperiment.pick_mem
#print axioms Paper.GeneralCoveringOwnerExperiment.label_cases
#print axioms Paper.GeneralCoveringOwnerExperiment.label_sampled
#print axioms Paper.GeneralCoveringOwnerExperiment.label_owner_none_cases
#print axioms Paper.GeneralCoveringOwnerExperiment.label_none_nongated
#print axioms Paper.GeneralCoveringOwnerExperiment.model
#print axioms Paper.GeneralCoveringOwnerExperiment.retained_center
#print axioms Paper.GeneralCoveringOwnerExperiment.isMinor
