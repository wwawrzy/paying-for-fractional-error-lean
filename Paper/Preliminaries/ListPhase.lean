import Paper.Preliminaries.CoreHierarchy

/-! Actual minimum-ID selections in one bounded-list phase. -/
namespace Paper.ListPhase
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Each currently uncovered nonempty list selects its minimum identifier. -/
noncomputable def picks (H : Finset (Finset V)) : Finset V :=
  (H.filter Finset.Nonempty).attach.image (fun s => s.val.min' (Finset.mem_filter.mp s.property).2)

noncomputable def phase (H : Finset (Finset V)) (D : Finset V) : Finset V :=
  D ∪ picks (SunflowerLists.uncovered H D)

theorem picks_card_le (H : Finset (Finset V)) : (picks H).card ≤ H.card := by
  calc
    _ ≤ (H.filter Finset.Nonempty).attach.card := Finset.card_image_le
    _ = (H.filter Finset.Nonempty).card := Finset.card_attach
    _ ≤ H.card := Finset.card_filter_le _ _

theorem picks_minimum (H : Finset (Finset V)) {v : V} (hv : v ∈ picks H) :
    ∃ s ∈ H, v ∈ s ∧ ∀ u ∈ s, v ≤ u := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hv
  refine ⟨s.val, (Finset.mem_filter.mp s.property).1, Finset.min'_mem _ _, ?_⟩
  intro u hu
  exact Finset.min'_le _ _ hu

theorem phase_covers (H : Finset (Finset V)) (D : Finset V)
    (hn : ∀ s ∈ H, s.Nonempty) : ∀ s ∈ H, (s ∩ phase H D).Nonempty := by
  intro s hs
  by_cases hd : Disjoint s D
  · have hu : s ∈ SunflowerLists.uncovered H D := Finset.mem_filter.mpr ⟨hs, hd⟩
    let s' : {t // t ∈ (SunflowerLists.uncovered H D).filter Finset.Nonempty} :=
      ⟨s, Finset.mem_filter.mpr ⟨hu, hn s hs⟩⟩
    let v := s.min' (hn s hs)
    refine ⟨v, Finset.mem_inter.mpr ⟨Finset.min'_mem _ _, Finset.mem_union_right _ ?_⟩⟩
    exact Finset.mem_image.mpr ⟨s', Finset.mem_attach _ _, rfl⟩
  · obtain ⟨v, hvs, hvD⟩ := Finset.not_disjoint_iff.mp hd
    exact ⟨v, Finset.mem_inter.mpr ⟨hvs, Finset.mem_union_left _ hvD⟩⟩

theorem phase_card_le (H : Finset (Finset V)) (D : Finset V) :
    (phase H D).card ≤ D.card + (SunflowerLists.uncovered H D).card :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (picks_card_le _) _)

/-- Cost of an actual phase, once the preceding level has hit the actual cores. -/
theorem phase_cost (H : Finset (Finset V)) (D O : Finset V) (j q : ℕ) (hq : 2 ≤ q)
    (hrank : ∀ s ∈ H, s.card ≤ j)
    (hcore : ∀ C ∈ CoreHierarchy.cores H q, (C ∩ D).Nonempty)
    (hO : ∀ s ∈ H, (s ∩ O).Nonempty) :
    (phase H D).card ≤ D.card + SunflowerLists.delta j q * O.card :=
  (phase_card_le H D).trans (Nat.add_le_add_left
    (SunflowerLists.uncovered_card_le j q hq H D O hrank
      ((CoreHierarchy.hits_cores_iff H q D).mp hcore) hO) _)
end Paper.ListPhase
