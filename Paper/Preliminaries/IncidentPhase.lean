import Paper.Preliminaries.IncidentHierarchy
import Paper.Preliminaries.ListPhase

/-! A vertex decides the exact bounded-list phase from its incident family
and selection bits of co-listed vertices, supplied by a two-round protocol. -/
namespace Paper.IncidentPhase
variable {V : Type} [LinearOrder V]

def chosen (v : V) (H : Finset (Finset V)) (known : Finset V) (old : Bool) : Bool :=
  decide (old = true ∨ ∃ s ∈ H, v ∈ s ∧ (∀ u ∈ s, v ≤ u) ∧ Disjoint s known)

variable [Fintype V]
attribute [local instance] Classical.propDecidable

theorem picks_iff (H : Finset (Finset V)) (v : V) :
    v ∈ ListPhase.picks H ↔ ∃ s ∈ H, v ∈ s ∧ ∀ u ∈ s, v ≤ u := by
  constructor
  · exact ListPhase.picks_minimum H
  · rintro ⟨s, hs, hv, hmin⟩
    have hn : s.Nonempty := ⟨v, hv⟩
    let t : ↥(H.filter Finset.Nonempty) := ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩⟩
    have he : s.min' hn = v := le_antisymm (Finset.min'_le s v hv) (hmin _ (Finset.min'_mem s hn))
    apply Finset.mem_image.mpr
    exact ⟨t, Finset.mem_attach _ _, he⟩

theorem phase_iff (H : Finset (Finset V)) (D : Finset V) (v : V) :
    v ∈ ListPhase.phase H D ↔ v ∈ D ∨
      ∃ s ∈ H, v ∈ s ∧ (∀ u ∈ s, v ≤ u) ∧ Disjoint s D := by
  rw [ListPhase.phase, Finset.mem_union, picks_iff]
  simp only [SunflowerLists.uncovered, Finset.mem_filter]
  constructor
  · rintro (h | ⟨s, ⟨hs, hd⟩, hv, hm⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, hs, hv, hm, hd⟩
  · rintro (h | ⟨s, hs, hv, hm, hd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨s, ⟨hs, hd⟩, hv, hm⟩

theorem correct (H : Finset (Finset V)) (D known : Finset V) (v : V)
    (hk : ∀ s ∈ IncidentHierarchy.incident H v, ∀ u ∈ s, u ∈ known ↔ u ∈ D) :
    chosen v (IncidentHierarchy.incident H v) known (decide (v ∈ D)) =
      decide (v ∈ ListPhase.phase H D) := by
  apply Bool.eq_iff_iff.mpr
  simp only [chosen, decide_eq_true_eq, phase_iff]
  constructor
  · rintro (h | ⟨s, hs, hv, hm, hd⟩)
    · exact Or.inl h
    · refine Or.inr ⟨s, (Finset.mem_filter.mp hs).1, hv, hm, ?_⟩
      exact Finset.disjoint_left.mpr (fun u hu hD => Finset.disjoint_left.mp hd hu ((hk s hs u hu).mpr hD))
  · rintro (h | ⟨s, hs, hv, hm, hd⟩)
    · exact Or.inl h
    · have hi : s ∈ IncidentHierarchy.incident H v := Finset.mem_filter.mpr ⟨hs, hv⟩
      refine Or.inr ⟨s, hi, hv, hm, ?_⟩
      exact Finset.disjoint_left.mpr (fun u hu hK => Finset.disjoint_left.mp hd hu ((hk s hi u hu).mp hK))
end Paper.IncidentPhase
