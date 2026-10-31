import Paper.Owners.Construction.OwnerInteraction
import Paper.Preliminaries.FiniteCylinder
import Paper.Preliminaries.BlowupEdge

/-! A finite owner experiment: keep complete selected owner stars, and
attach remaining light vertices to one selected label from their support. -/
namespace Paper.OwnerExperiment
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem owner_star (D : Finset V) (u : V) : owner G D u = u ∨ G.Adj (owner G D u) u := by
  by_cases hu : u ∈ D
  · exact Or.inl (owner_center G D hu)
  by_cases hn : ((closed G u) ∩ D).Nonempty
  · have hm := Finset.mem_inter.mp (Finset.min'_mem ((closed G u) ∩ D) hn)
    have he : owner G D u = ((closed G u) ∩ D).min' hn := by simp [owner, hu, hn]
    rw [← he] at hm
    exact ((mem_closed G _ _).mp hm.1).elim Or.inl (fun ha => Or.inr ha.symm)
  · exact Or.inl (by simp [owner, hu, hn])

noncomputable def sampled {c : ℕ} (D : Finset V) (ω : V ⊕ V → Fin c) : Finset V :=
  D.filter (fun d => (ω (.inl d)).val = 0)

noncomputable def pick {c : ℕ} (D R : Finset V) (ω : V ⊕ V → Fin c) (v : V) : Option V :=
  ((support G D R v).sort (· ≤ ·))[(ω (.inr v)).val]?

noncomputable def label {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) (v : V) : Option V :=
  if owner G D v ∈ sampled D ω then some (owner G D v) else
    if v ∈ heavy G D R L then none else
      match pick G D R ω v with
      | none => none
      | some d => if d ∈ sampled D ω then some d else none

theorem label_base {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) {v : V}
    (hv : owner G D v ∈ sampled D ω) : label G D R L ω v = some (owner G D v) := by
  simp only [label, if_pos hv]

theorem label_center {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) {d : V}
    (hd : d ∈ sampled D ω) : label G D R L ω d = some d := by
  have hdD := (Finset.mem_filter.mp hd).1
  have he := owner_center G D hdD
  simpa only [he] using label_base G D R L ω (v := d) (by simpa only [he] using hd)

theorem pick_mem {c : ℕ} (D R : Finset V) (ω : V ⊕ V → Fin c) {v d : V}
    (h : pick G D R ω v = some d) : d ∈ support G D R v :=
  (Finset.mem_sort (· ≤ ·)).mp (List.mem_iff_getElem?.mpr ⟨(ω (.inr v)).val, h⟩)

theorem label_cases {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) {v d : V}
    (h : label G D R L ω v = some d) :
    (owner G D v = d ∧ d ∈ sampled D ω) ∨
      (v ∉ heavy G D R L ∧ d ∈ support G D R v ∧ d ∈ sampled D ω) := by
  by_cases hb : owner G D v ∈ sampled D ω
  · rw [label, if_pos hb] at h
    have he := Option.some.inj h
    exact Or.inl ⟨he, he ▸ hb⟩
  by_cases hh : v ∈ heavy G D R L
  · simp [label, hb, hh] at h
  · rw [label, if_neg hb, if_neg hh] at h
    cases hp : pick G D R ω v with
    | none => simp [hp] at h
    | some e =>
      rw [hp] at h
      change (if e ∈ sampled D ω then some e else none) = some d at h
      by_cases he : e ∈ sampled D ω
      · rw [if_pos he] at h
        have hed := Option.some.inj h
        exact Or.inr ⟨hh, hed ▸ pick_mem G D R ω hp, hed ▸ he⟩
      · simp [he] at h

def graph {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) : SimpleGraph (sampled D ω) where
  Adj a b := a ≠ b ∧ BlowupEdge.Crosses G (label G D R L ω) a.val b.val
  symm := by rintro a b ⟨hne, u, v, hu, hv, ha⟩; exact ⟨hne.symm, v, u, hv, hu, ha.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end Paper.OwnerExperiment
