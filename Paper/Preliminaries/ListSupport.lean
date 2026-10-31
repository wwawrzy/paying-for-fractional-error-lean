import Paper.Preliminaries.BoundedLists

/-! Coverage and support of the actual list algorithm, independent of its
density-based cost analysis. -/
namespace Paper.ListSupport
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem cover_hits (H : Finset (Finset V)) (q j : ℕ)
    (hrank : ∀ s ∈ H, s.card ≤ j) (hnon : ∀ s ∈ H, s.Nonempty) :
    ∀ s ∈ H, (s ∩ BoundedLists.cover H q j).Nonempty := by
  cases j with
  | zero =>
    intro s hs
    have hp := Finset.card_pos.mpr (hnon s hs)
    have hz := hrank s hs
    omega
  | succ j => exact ListPhase.phase_covers H _ hnon

theorem cover_support (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (j : ℕ) :
    ∀ v ∈ BoundedLists.cover H q j, ∃ s ∈ H, v ∈ s := by
  induction j generalizing H with
  | zero => simp [BoundedLists.cover]
  | succ j ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hpre | hpick
    · obtain ⟨C, hC, hvC⟩ := ih _ v hpre
      obtain ⟨s, hs, hCs⟩ := CoreHierarchy.core_subset_original H q hq hC
      exact ⟨s, hs, hCs hvC⟩
    · obtain ⟨s, hs, hvs, _⟩ := ListPhase.picks_minimum _ hpick
      exact ⟨s, (Finset.mem_filter.mp hs).1, hvs⟩
end Paper.ListSupport
