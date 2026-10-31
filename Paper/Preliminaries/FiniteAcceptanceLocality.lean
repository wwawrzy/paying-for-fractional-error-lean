import Paper.Partitions.Local.FinitePriorityRule

/-! Acceptance needs only intersecting candidates; parts at a vertex need
only accepted candidates containing that vertex. -/
namespace Paper.FiniteAcceptanceLocality
variable {V : Type} [LinearOrder V]

theorem accepted_iff {Q : ℕ} (F H : Finset (Finset V)) (ω τ : Finset V → Fin Q)
    (U : Finset V) (hu : U ∈ F ↔ U ∈ H) (hp : ω U = τ U)
    (hf : ∀ T, ¬ Disjoint U T → (T ∈ F ↔ T ∈ H))
    (ht : ∀ T ∈ F, ¬ Disjoint U T → ω T = τ T) :
    U ∈ FinitePriorityRule.accepted F ω ↔ U ∈ FinitePriorityRule.accepted H τ := by
  simp only [FinitePriorityRule.accepted, Finset.mem_filter]
  constructor
  · rintro ⟨hU, hz, hc⟩
    refine ⟨hu.mp hU, hp ▸ hz, ?_⟩
    intro T hT hne hd
    have hTF := (hf T hd).mpr hT
    rw [← ht T hTF hd]
    exact hc T hTF hne hd
  · rintro ⟨hU, hz, hc⟩
    refine ⟨hu.mpr hU, hp.symm ▸ hz, ?_⟩
    intro T hT hne hd
    rw [ht T hT hd]
    exact hc T ((hf T hd).mp hT) hne hd

theorem removed_iff {Q : ℕ} (F H : Finset (Finset V)) (ω τ : Finset V → Fin Q) (v : V)
    (h : ∀ U, v ∈ U → (U ∈ FinitePriorityRule.accepted F ω ↔ U ∈ FinitePriorityRule.accepted H τ)) :
    v ∈ FinitePriorityRule.removed F ω ↔ v ∈ FinitePriorityRule.removed H τ := by
  simp only [FinitePriorityRule.removed, Finset.mem_biUnion]
  constructor
  · rintro ⟨U, hU, hv⟩
    exact ⟨U, (h U hv).mp hU, hv⟩
  · rintro ⟨U, hU, hv⟩
    exact ⟨U, (h U hv).mpr hU, hv⟩

theorem part_eq {Q : ℕ} (F H : Finset (Finset V)) (ω τ : Finset V → Fin Q) (v : V)
    (h : ∀ U, v ∈ U → (U ∈ FinitePriorityRule.accepted F ω ↔ U ∈ FinitePriorityRule.accepted H τ)) :
    FinitePriorityRule.part F ω v = FinitePriorityRule.part H τ v := by
  ext u
  simp only [FinitePriorityRule.part, Finset.mem_biUnion]
  constructor
  · rintro ⟨U, hU, hu⟩
    split_ifs at hu with hv
    · exact ⟨U, (h U hv).mp hU, by simpa only [if_pos hv] using hu⟩
    · exact False.elim (Finset.notMem_empty u hu)
  · rintro ⟨U, hU, hu⟩
    split_ifs at hu with hv
    · exact ⟨U, (h U hv).mpr hU, by simpa only [if_pos hv] using hu⟩
    · exact False.elim (Finset.notMem_empty u hu)
end Paper.FiniteAcceptanceLocality
