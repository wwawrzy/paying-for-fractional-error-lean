import Paper.Certificates.Counting.Sunflower

/-! Bound uncovered short lists after hitting every nonempty sunflower core.
Paper label: lem:sunflower. -/
namespace Paper.SunflowerLists
attribute [local instance] Classical.propDecidable
open Sunflower
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def delta (j q : ℕ) : ℕ := ∑ i ∈ Finset.range j, i.factorial * (q - 1) ^ i

theorem sunflower_mono {H K : Finset (Finset V)} {q : ℕ} (hHK : H ⊆ K)
    (h : HasSunflower H q) : HasSunflower K q := by
  obtain ⟨F, hF, hq, C, hC⟩ := h
  exact ⟨F, hF.trans hHK, hq, C, hC⟩

theorem rank_bound (j q : ℕ) (hq : 2 ≤ q) (H : Finset (Finset V))
    (hrank : ∀ s ∈ H, s.card < j) (hn : ¬ HasSunflower H q) : H.card ≤ delta j q := by
  classical
  have hcounts : ∀ i ∈ Finset.range j, (H.filter (fun s => s.card = i)).card ≤
      i.factorial * (q - 1) ^ i := by
    intro i _
    by_contra hle
    have hs := exists_of_card_gt i q hq (H.filter (fun s => s.card = i))
      (fun s hs => (Finset.mem_filter.mp hs).2) (lt_of_not_ge hle)
    exact hn (sunflower_mono (Finset.filter_subset _ _) hs)
  have hf : H.filter (fun s => s.card ∈ Finset.range j) = H :=
    Finset.filter_true_of_mem (fun s hs => Finset.mem_range.mpr (hrank s hs))
  have hc := Finset.sum_card_fiberwise_eq_card_filter H (Finset.range j) (fun s => s.card)
  rw [hf] at hc
  rw [← hc]
  exact Finset.sum_le_sum hcounts

noncomputable def uncovered (H : Finset (Finset V)) (D : Finset V) : Finset (Finset V) :=
  H.filter (fun s => Disjoint s D)

def HitsCores (H : Finset (Finset V)) (q : ℕ) (D : Finset V) : Prop :=
  ∀ F ⊆ H, F.card = q → ∀ C, IsSunflower F C → C.Nonempty → (C ∩ D).Nonempty

/-- Deleting a common vertex turns too many remaining incident lists into a
sunflower; restoring it would give a nonempty core missed by D. -/
theorem uncovered_degree_le (j q : ℕ) (hq : 2 ≤ q) (H : Finset (Finset V)) (D : Finset V)
    (hrank : ∀ s ∈ H, s.card ≤ j) (hcores : HitsCores H q D) (v : V) :
    ((uncovered H D).filter (fun s => v ∈ s)).card ≤ delta j q := by
  classical
  let Hv := (uncovered H D).filter (fun s => v ∈ s)
  let E := Hv.image (fun s => s.erase v)
  have hfilter : Hv.filter (fun s => v ∈ s) = Hv :=
    Finset.filter_true_of_mem (fun s hs => (Finset.mem_filter.mp hs).2)
  have hn : ¬ HasSunflower E q := by
    intro he
    have he' : HasSunflower ((Hv.filter (fun s => v ∈ s)).image (fun s => s.erase v)) q := by
      rw [hfilter]
      exact he
    obtain ⟨F, hF, hqF, C, hsun⟩ := lift_erase Hv v q he'
    obtain ⟨s, hs, t, ht, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
    have hst := hsun s hs t ht hne
    have hvC : v ∈ C := hst ▸ Finset.mem_inter.mpr
      ⟨(Finset.mem_filter.mp (hF hs)).2, (Finset.mem_filter.mp (hF ht)).2⟩
    have hFH : F ⊆ H := fun u hu =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp (hF hu)).1).1
    obtain ⟨z, hz⟩ := hcores F hFH hqF C hsun ⟨v, hvC⟩
    have hzC := (Finset.mem_inter.mp hz).1
    have hzD := (Finset.mem_inter.mp hz).2
    have hCsub : C ⊆ s := by rw [← hst]; exact Finset.inter_subset_left
    have hsD : Disjoint s D :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp (hF hs)).1).2
    exact Finset.disjoint_left.mp hsD (hCsub hzC) hzD
  have hr : ∀ s ∈ E, s.card < j := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have htv := (Finset.mem_filter.mp ht).2
    have htH := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
    have hr := hrank t htH
    have hc := Finset.card_erase_add_one htv
    omega
  have hinj : Set.InjOn (fun s => s.erase v) (Hv : Set (Finset V)) := by
    intro s hs t ht he
    have he' := congrArg (insert v) he
    simpa only [Finset.insert_erase (Finset.mem_filter.mp hs).2,
      Finset.insert_erase (Finset.mem_filter.mp ht).2] using he'
  have hc : E.card = Hv.card := Finset.card_image_of_injOn hinj
  rw [← hc]
  exact rank_bound j q hq E hr hn

/-- Every uncovered list is charged to a member of an actual hitting set. -/
theorem uncovered_card_le (j q : ℕ) (hq : 2 ≤ q) (H : Finset (Finset V))
    (D O : Finset V) (hrank : ∀ s ∈ H, s.card ≤ j) (hcores : HitsCores H q D)
    (hO : ∀ s ∈ H, (s ∩ O).Nonempty) :
    (uncovered H D).card ≤ delta j q * O.card := by
  have hl : (uncovered H D).card ≤ ∑ v ∈ O,
      ((uncovered H D).filter (fun s => v ∈ s)).card := by
    rw [← FloatingCore.incidence_sum (fun s : Finset V => s) (uncovered H D) O]
    calc
      _ = ∑ _s ∈ uncovered H D, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s hs => Nat.succ_le_of_lt
        (Finset.card_pos.mpr (hO s (Finset.mem_filter.mp hs).1)))
  calc
    _ ≤ _ := hl
    _ ≤ ∑ _v ∈ O, delta j q := Finset.sum_le_sum
      (fun v _ => uncovered_degree_le j q hq H D hrank hcores v)
    _ = _ := by simp [mul_comm]
end Paper.SunflowerLists
