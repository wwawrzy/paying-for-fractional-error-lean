import Paper.Preliminaries.ListSupport
import Paper.Preliminaries.SevenFoundation

/-! Actual initialization pass: useful candidates, bounded nonempty lists,
the proved recursive list algorithm, and empty-list self-selections. -/
namespace Paper.InitializerPass
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def candidates (h : ℕ) (R : Finset V) : Finset V :=
  Finset.univ.filter (fun v => h < ((closed G v) ∩ R).card)

noncomputable def eligibleList (h : ℕ) (R : Finset V) (v : V) : Finset V :=
  (closed G v) ∩ candidates G h R

noncomputable def listed (h f : ℕ) (R : Finset V) : Finset V :=
  R.filter (fun v => (eligibleList G h R v).card ≤ f ∧ (eligibleList G h R v).Nonempty)

noncomputable def lists (h f : ℕ) (R : Finset V) : Finset (Finset V) :=
  (listed G h f R).image (eligibleList G h R)

noncomputable def emptyLists (h : ℕ) (R : Finset V) : Finset V :=
  R.filter (fun v => eligibleList G h R v = ∅)

noncomputable def selected (a h f : ℕ) (R : Finset V) : Finset V :=
  BoundedLists.cover (lists G h f R) (2 * a) f ∪ emptyLists G h R

noncomputable def residual (a h f : ℕ) (R : Finset V) : Finset V :=
  R \ covered G (selected G a h f R)

theorem lists_rank (h f : ℕ) (R : Finset V) : ∀ s ∈ lists G h f R, s.card ≤ f := by
  intro s hs
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
  exact (Finset.mem_filter.mp hv).2.1

theorem lists_nonempty (h f : ℕ) (R : Finset V) : ∀ s ∈ lists G h f R, s.Nonempty := by
  intro s hs
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
  exact (Finset.mem_filter.mp hv).2.2

theorem selected_subset (a h f : ℕ) (ha : 1 ≤ a) (R : Finset V) :
    selected G a h f R ⊆ candidates G h R ∪ R := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨s, hs, hvs⟩ := ListSupport.cover_support _ _ (by omega) _ v hv
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_union_left _ (Finset.mem_inter.mp hvs).2
  · exact Finset.mem_union_right _ (Finset.mem_filter.mp hv).1

theorem small_covered (a h f : ℕ) (R : Finset V) {v : V} (hv : v ∈ R)
    (hsmall : (eligibleList G h R v).card ≤ f) : v ∈ covered G (selected G a h f R) := by
  classical
  by_cases hn : (eligibleList G h R v).Nonempty
  · have hs : eligibleList G h R v ∈ lists G h f R :=
      Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hsmall, hn⟩, rfl⟩
    obtain ⟨u, hu⟩ := ListSupport.cover_hits _ (2 * a) f (lists_rank G h f R) (lists_nonempty G h f R) _ hs
    have hu' := Finset.mem_inter.mp hu
    have huv := (Finset.mem_inter.mp hu'.1).1
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_left _ hu'.2, (closed_symm G u v).mp huv⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    exact subset_covered G _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, he⟩))

theorem closed_inter_card (R : Finset V) (v : V) :
    ((closed G v) ∩ R).card ≤ ((G.neighborFinset v) ∩ R).card + 1 := by
  have hs : (closed G v) ∩ R ⊆ ((G.neighborFinset v) ∩ R) ∪ {v} := by
    intro u hu
    have hm := Finset.mem_inter.mp hu
    rcases (mem_closed G u v).mp hm.1 with he | ha
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr he)
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr ha, hm.2⟩)
  exact (Finset.card_le_card hs).trans (by simpa using Finset.card_union_le ((G.neighborFinset v) ∩ R) {v})

theorem surviving_neighbors (a h f : ℕ) (R : Finset V) {v : V}
    (hv : v ∈ residual G a h f R) : f ≤ ((G.neighborFinset v) ∩ candidates G h R).card := by
  have hm := Finset.mem_sdiff.mp hv
  have hn : ¬ (eligibleList G h R v).card ≤ f := fun he => hm.2 (small_covered G a h f R hm.1 he)
  have hc := closed_inter_card G (candidates G h R) v
  change ((closed G v) ∩ candidates G h R).card ≤ _ at hc
  change ¬ ((closed G v) ∩ candidates G h R).card ≤ f at hn
  omega

theorem candidate_neighbors (h : ℕ) (R : Finset V) {v : V} (hv : v ∈ candidates G h R) :
    h ≤ ((G.neighborFinset v) ∩ R).card := by
  have hm := (Finset.mem_filter.mp hv).2
  have hc := closed_inter_card G R v
  omega
end Paper.InitializerPass
