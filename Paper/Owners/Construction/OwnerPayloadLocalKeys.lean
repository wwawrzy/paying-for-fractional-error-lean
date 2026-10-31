import Paper.Owners.Construction.OwnerPayloadInputs

/-! Exact keys and consistent payloads after the two middle physical
gathers. Candidate dictionaries have≤L keys on the actual task network. -/
namespace Paper.OwnerPayloadLocalKeys
open BroadcastModel SevenFoundation
variable {V A : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem actual_mem (D R : Finset V) (L : ℕ) (v k : V) :
    k ∈ OwnerInteraction.actualSupport G D R L v ↔
      ∃ r ∈ closed G v, r ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D r = k := by
  unfold OwnerInteraction.actualSupport
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  simp only [Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨r, ⟨hr, hrem⟩, he⟩
    exact ⟨r, hr, hrem, he⟩
  · rintro ⟨r, hr, hrem, he⟩
    exact ⟨r, ⟨hr, hrem⟩, he⟩

theorem candidate_keys {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.keys (OwnerPayloadRoute.candidate G C P (OwnerPayloadInputs.expected G D R L active f) v) =
      OwnerInteraction.actualSupport G D R L v ∩ active := by
  rw [OwnerPayloadRoute.candidate, TaggedGather.keys_correct G C P 1 _
    (OwnerPayloadInputs.first_size G P _) v]
  ext k
  rw [Finset.mem_biUnion, Finset.mem_inter, actual_mem G D R L v k]
  constructor
  · rintro ⟨r, hr, hk⟩
    obtain ⟨hrem, he, ha⟩ := (OwnerPayloadInputs.first_keys_iff G P D R hcover L active f r k).mp hk
    exact ⟨⟨r, hr, hrem, he⟩, ha⟩
  · rintro ⟨⟨r, hr, hrem, he⟩, ha⟩
    exact ⟨r, hr, (OwnerPayloadInputs.first_keys_iff G P D R hcover L active f r k).mpr ⟨hrem, he, ha⟩⟩

theorem candidate_bound {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    (TaggedDictionary.keys (OwnerPayloadRoute.candidate G C P (OwnerPayloadInputs.expected G D R L active f) v)).card ≤ L := by
  rw [candidate_keys G C P D R hcover L active f v]
  exact (Finset.card_le_card Finset.inter_subset_left).trans (OwnerInteraction.support_bound G D R L v)

theorem candidate_consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (v : V) :
    TaggedDictionary.Consistent f (OwnerPayloadRoute.candidate G C P (OwnerPayloadInputs.expected G D R L active f) v) :=
  TaggedGather.consistent G C P 1 _ f (OwnerPayloadInputs.first_consistent G P D R hcover L active f) v

theorem demand_keys {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (r : V) :
    TaggedDictionary.keys (OwnerPayloadRoute.demand G C P L (OwnerPayloadInputs.expected G D R L active f) r) =
      (closed G r).biUnion (fun v => OwnerInteraction.actualSupport G D R L v ∩ active) := by
  rw [OwnerPayloadRoute.demand, TaggedGather.keys_correct G C P L _
    (candidate_bound G C P D R hcover L active f) r]
  have hh : (fun v => TaggedDictionary.keys (OwnerPayloadRoute.candidate G C P (OwnerPayloadInputs.expected G D R L active f) v)) =
      fun v => OwnerInteraction.actualSupport G D R L v ∩ active := funext (candidate_keys G C P D R hcover L active f)
  rw [hh]

theorem demand_consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (D R : Finset V)
    (hcover : R ⊆ covered G D) (L : ℕ) (active : Finset V) (f : V → A) (r : V) :
    TaggedDictionary.Consistent f (OwnerPayloadRoute.demand G C P L (OwnerPayloadInputs.expected G D R L active f) r) :=
  TaggedGather.consistent G C P L _ f (candidate_consistent G C P D R hcover L active f) r
end Paper.OwnerPayloadLocalKeys
