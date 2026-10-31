import Paper.Initialization.Lists.SunflowerLists

/-! Actual sunflower-core hierarchy: rank reduction and local incident-family
information. Paper label: lem:cores and list algorithm. -/
namespace Paper.CoreHierarchy
attribute [local instance] Classical.propDecidable
open Sunflower
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem core_subset_member (F : Finset (Finset V)) (C : Finset V) (hcard : 2 ≤ F.card)
    (hsun : IsSunflower F C) {s : Finset V} (hs : s ∈ F) : C ⊆ s := by
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  by_cases hsa : s = a
  · subst s
    rw [← hsun a ha b hb hne]
    exact Finset.inter_subset_left
  · rw [← hsun a ha s hs (Ne.symm hsa)]
    exact Finset.inter_subset_right

noncomputable def cores (H : Finset (Finset V)) (q : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun C => C.Nonempty ∧ ∃ F ⊆ H, F.card = q ∧ IsSunflower F C)

theorem mem_cores (H : Finset (Finset V)) (q : ℕ) (C : Finset V) :
    C ∈ cores H q ↔ C.Nonempty ∧ ∃ F ⊆ H, F.card = q ∧ IsSunflower F C := by
  simp only [cores, Finset.mem_filter, Finset.mem_univ, true_and]

theorem cores_mono {H K : Finset (Finset V)} (q : ℕ) (h : H ⊆ K) : cores H q ⊆ cores K q := by
  intro C hC
  obtain ⟨hn, F, hF, hq, hsun⟩ := (mem_cores H q C).mp hC
  exact (mem_cores K q C).mpr ⟨hn, F, hF.trans h, hq, hsun⟩

theorem core_subset_original (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q)
    {C : Finset V} (hC : C ∈ cores H q) : ∃ s ∈ H, C ⊆ s := by
  obtain ⟨_, F, hF, hqF, hsun⟩ := (mem_cores H q C).mp hC
  have hcard : 2 ≤ F.card := by omega
  have hn : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨s, hs⟩ := hn
  exact ⟨s, hF hs, core_subset_member F C hcard hsun hs⟩

theorem core_rank_lt (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (j : ℕ)
    (hrank : ∀ s ∈ H, s.card ≤ j) {C : Finset V} (hC : C ∈ cores H q) : C.card < j := by
  obtain ⟨_, F, hF, hqF, hsun⟩ := (mem_cores H q C).mp hC
  have hcard : 2 ≤ F.card := by omega
  obtain ⟨s, hs, t, ht, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  have hCs := core_subset_member F C hcard hsun hs
  have hCt := core_subset_member F C hcard hsun ht
  by_contra hn
  have hscard : s.card ≤ C.card := (hrank s (hF hs)).trans (le_of_not_gt hn)
  have htcard : t.card ≤ C.card := (hrank t (hF ht)).trans (le_of_not_gt hn)
  have he1 : C = s := Finset.eq_of_subset_of_card_le hCs hscard
  have he2 : C = t := Finset.eq_of_subset_of_card_le hCt htcard
  exact hne (he1.symm.trans he2)

theorem core_rank_le (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (j : ℕ)
    (hrank : ∀ s ∈ H, s.card ≤ j) : ∀ C ∈ cores H q, C.card ≤ j - 1 := by
  intro C hC
  have h := core_rank_lt H q hq j hrank hC
  omega

/-- All witnesses of a core containing v are themselves incident with v.
Thus local computation needs exactly the original incident family. -/
theorem incident_cores (H : Finset (Finset V)) (q : ℕ) (hq : 2 ≤ q) (v : V) (C : Finset V) :
    C ∈ cores H q ∧ v ∈ C ↔ C ∈ cores (H.filter (fun s => v ∈ s)) q ∧ v ∈ C := by
  constructor
  · rintro ⟨hC, hv⟩
    obtain ⟨hn, F, hF, hqF, hsun⟩ := (mem_cores H q C).mp hC
    have hcard : 2 ≤ F.card := by omega
    refine ⟨(mem_cores _ q C).mpr ⟨hn, F, ?_, hqF, hsun⟩, hv⟩
    intro s hs
    exact Finset.mem_filter.mpr ⟨hF hs, core_subset_member F C hcard hsun hs hv⟩
  · rintro ⟨hC, hv⟩
    exact ⟨cores_mono q (Finset.filter_subset _ _) hC, hv⟩

theorem hits_cores_iff (H : Finset (Finset V)) (q : ℕ) (D : Finset V) :
    (∀ C ∈ cores H q, (C ∩ D).Nonempty) ↔ SunflowerLists.HitsCores H q D := by
  constructor
  · intro h F hF hq C hsun hn
    exact h C ((mem_cores H q C).mpr ⟨hn, F, hF, hq, hsun⟩)
  · intro h C hC
    obtain ⟨hn, F, hF, hq, hsun⟩ := (mem_cores H q C).mp hC
    exact h F hF hq C hsun hn
end Paper.CoreHierarchy
