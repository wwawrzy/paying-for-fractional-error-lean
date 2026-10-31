import Paper.Certificates.Counting.FloatingCore

/-! Finite sunflower combinatorics for bounded-list initialization.
This module is independent of the fractional solver theorem. -/
namespace Paper.Sunflower
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def IsSunflower (F : Finset (Finset V)) (C : Finset V) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, s ≠ t → s ∩ t = C

def HasSunflower (H : Finset (Finset V)) (q : ℕ) : Prop :=
  ∃ F ⊆ H, F.card = q ∧ ∃ C, IsSunflower F C

def Packing (F : Finset (Finset V)) : Prop :=
  ∀ s ∈ F, ∀ t ∈ F, s ≠ t → Disjoint s t

theorem packing_has_sunflower (H F : Finset (Finset V)) (q : ℕ)
    (hF : F ⊆ H) (hp : Packing F) (hq : q ≤ F.card) : HasSunflower H q := by
  obtain ⟨D, hDF, hcard⟩ := Finset.exists_subset_card_eq hq
  refine ⟨D, hDF.trans hF, hcard, ∅, ?_⟩
  intro s hs t ht hne
  exact Finset.disjoint_iff_inter_eq_empty.mp (hp s (hDF hs) t (hDF ht) hne)

/-- A maximal disjoint subfamily has a union intersecting every nonempty set. -/
theorem maximal_packing (H : Finset (Finset V)) :
    ∃ F ⊆ H, Packing F ∧
      ∀ s ∈ H, s.Nonempty → (s ∩ F.biUnion id).Nonempty := by
  classical
  let P := H.powerset.filter Packing
  have hP : P.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro s hs
    exact False.elim (Finset.notMem_empty s hs)
  obtain ⟨F, hFP, hmax⟩ := Finset.exists_max_image P Finset.card hP
  have hFH : F ⊆ H := Finset.mem_powerset.mp (Finset.mem_filter.mp hFP).1
  have hpack : Packing F := (Finset.mem_filter.mp hFP).2
  refine ⟨F, hFH, hpack, ?_⟩
  intro s hs hsnon
  by_contra hn
  have hdis : Disjoint s (F.biUnion id) := by
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    exact Finset.not_nonempty_iff_eq_empty.mp hn
  have hsnot : s ∉ F := by
    intro hsF
    obtain ⟨v, hv⟩ := hsnon
    exact Finset.disjoint_left.mp hdis hv (Finset.mem_biUnion.mpr ⟨s, hsF, hv⟩)
  have hins : Packing (insert s F) := by
    intro u hu v hv hne
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact False.elim (hne hv.symm)
      · exact hdis.mono_right (fun x hx => Finset.mem_biUnion.mpr ⟨v, hv, hx⟩)
    · rcases Finset.mem_insert.mp hv with hv | hv
      · subst v
        exact (hdis.mono_right (show u ⊆ F.biUnion id from
          fun x hx => Finset.mem_biUnion.mpr ⟨u, hu, hx⟩)).symm
      · exact hpack u hu v hv hne
  have hinsP : insert s F ∈ P := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset hs hFH), hins⟩
  have hcard := hmax (insert s F) hinsP
  rw [Finset.card_insert_of_notMem hsnot] at hcard
  omega

/-- Restoring a common deleted element lifts an actual sunflower family. -/
theorem lift_erase (H : Finset (Finset V)) (v : V) (q : ℕ)
    (h : HasSunflower ((H.filter (fun s => v ∈ s)).image (fun s => s.erase v)) q) :
    HasSunflower H q := by
  classical
  obtain ⟨F, hF, hq, C, hsun⟩ := h
  have hnot : ∀ s ∈ F, v ∉ s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (hF hs)
    exact Finset.notMem_erase v t
  have hinj : Set.InjOn (fun s => insert v s) (F : Set (Finset V)) := by
    intro s hs t ht he
    have he' := congrArg (fun s : Finset V => s.erase v) he
    simpa only [Finset.erase_insert (hnot s hs), Finset.erase_insert (hnot t ht)] using he'
  refine ⟨F.image (fun s => insert v s), ?_, ?_, insert v C, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp (hF ht)
    have hvu := (Finset.mem_filter.mp hu).2
    rw [← he, Finset.insert_erase hvu]
    exact (Finset.mem_filter.mp hu).1
  · rw [Finset.card_image_of_injOn hinj, hq]
  · intro s hs t ht hne
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
    have hst : s' ≠ t' := fun he => hne (congrArg (insert v) he)
    have he : insert v s' ∩ insert v t' = insert v (s' ∩ t') := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      tauto
    rw [he, hsun s' hs' t' ht' hst]

set_option maxHeartbeats 2000000 in
/-- The finite Erdos-Rado bound for uniform set families, including empty cores. -/
theorem exists_of_card_gt (n q : ℕ) (hq : 2 ≤ q) (H : Finset (Finset V))
    (huniform : ∀ s ∈ H, s.card = n)
    (hcard : n.factorial * (q - 1) ^ n < H.card) : HasSunflower H q := by
  classical
  induction n generalizing H with
  | zero =>
    have hs : H ⊆ {∅} := by
      intro s hs
      exact Finset.mem_singleton.mpr (Finset.card_eq_zero.mp (huniform s hs))
    have hc := Finset.card_le_card hs
    simp only [Finset.card_singleton] at hc
    simp only [Nat.factorial_zero, pow_zero, mul_one] at hcard
    omega
  | succ n ih =>
    obtain ⟨F, hFH, hpack, hcover⟩ := maximal_packing H
    by_cases hqF : q ≤ F.card
    · exact packing_has_sunflower H F q hFH hpack hqF
    have hFcard : F.card ≤ q - 1 := by omega
    let U := F.biUnion id
    have hU : U.card ≤ (n + 1) * (q - 1) := by
      calc
        _ ≤ ∑ s ∈ F, s.card := Finset.card_biUnion_le
        _ = (n + 1) * F.card := by
          rw [Finset.sum_congr rfl (fun s hs => huniform s (hFH hs))]
          simp [mul_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ hFcard
    let B := n.factorial * (q - 1) ^ n
    have hex : ∃ v ∈ U, B < (H.filter (fun s => v ∈ s)).card := by
      by_contra hn
      push Not at hn
      have hinc : H.card ≤ ∑ v ∈ U, (H.filter (fun s => v ∈ s)).card := by
        rw [← FloatingCore.incidence_sum (fun s : Finset V => s) H U]
        calc
          _ = ∑ _s ∈ H, 1 := by simp
          _ ≤ _ := Finset.sum_le_sum (fun s hs => by
            apply Nat.succ_le_of_lt
            apply Finset.card_pos.mpr
            exact hcover s hs (Finset.card_pos.mp (by rw [huniform s hs]; omega)))
      have hbound : H.card ≤ (n + 1).factorial * (q - 1) ^ (n + 1) := by
        calc
          _ ≤ ∑ v ∈ U, (H.filter (fun s => v ∈ s)).card := hinc
          _ ≤ ∑ _v ∈ U, B := Finset.sum_le_sum (fun v hv => hn v hv)
          _ = U.card * B := by simp [mul_comm]
          _ ≤ ((n + 1) * (q - 1)) * B := Nat.mul_le_mul_right B hU
          _ = _ := by dsimp [B]; rw [Nat.factorial_succ, pow_succ]; ring
      omega
    obtain ⟨v, hvU, hv⟩ := hex
    let Hv := H.filter (fun s => v ∈ s)
    let H' := Hv.image (fun s => s.erase v)
    have hinj : Set.InjOn (fun s => s.erase v) (Hv : Set (Finset V)) := by
      intro s hs t ht he
      have hs' := (Finset.mem_filter.mp hs).2
      have ht' := (Finset.mem_filter.mp ht).2
      have hi := congrArg (insert v) he
      simpa only [Finset.insert_erase hs', Finset.insert_erase ht'] using hi
    have hsize : H'.card = Hv.card := Finset.card_image_of_injOn hinj
    have huni : ∀ s ∈ H', s.card = n := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      have he := Finset.card_erase_add_one (Finset.mem_filter.mp ht).2
      rw [huniform t (Finset.mem_filter.mp ht).1] at he
      omega
    have hsflower : HasSunflower H' q := ih H' huni (by rw [hsize]; exact hv)
    exact lift_erase H v q hsflower

end Paper.Sunflower
