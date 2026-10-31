import Paper.Owners.Construction.OwnerPayloadRoute

/-! Proof-only input identification and first-hop keys. The global objects
here describe actual private inputs; none is an argument to router code. -/
namespace Paper.OwnerPayloadInputs
open BroadcastModel SevenFoundation
variable {V A : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def expected (D R : Finset V) (L : ℕ) (active : Finset V) (f : V → A) (u : V) :
    OwnerPayloadRoute.Input V A := ⟨OwnerMetadataCorrect.expected G D R L u, decide (u ∈ active), f u⟩

theorem first_correct {w : ℕ} (P : BitCode A w) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L : ℕ) (active : Finset V) (f : V → A) (r : V) :
    OwnerPayloadRoute.first G P (expected G D R L active f) r =
      if r ∈ OwnerInteraction.remaining G D R L then
        if OwnerSupport.owner G D r ∈ active then some (OwnerSupport.owner G D r, f (OwnerSupport.owner G D r)) else none
      else none :=
  OwnerPayloadRead.correct G P D R hcover L active f _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) r

theorem first_size {w : ℕ} (P : BitCode A w) (s : V → OwnerPayloadRoute.Input V A) (r : V) :
    (TaggedDictionary.keys (OwnerPayloadRoute.first G P s r).toList).card ≤ 1 := by
  cases h : OwnerPayloadRoute.first G P s r <;> simp [h, TaggedDictionary.keys]

theorem first_keys {w : ℕ} (P : BitCode A w) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L : ℕ) (active : Finset V) (f : V → A) (r : V) :
    TaggedDictionary.keys (OwnerPayloadRoute.first G P (expected G D R L active f) r).toList =
      if r ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D r ∈ active then
        {OwnerSupport.owner G D r} else ∅ := by
  rw [first_correct G P D R hcover L active f r]
  by_cases hr : r ∈ OwnerInteraction.remaining G D R L <;>
    by_cases ha : OwnerSupport.owner G D r ∈ active <;> simp [hr, ha, TaggedDictionary.keys]

theorem first_keys_iff {w : ℕ} (P : BitCode A w) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L : ℕ) (active : Finset V) (f : V → A) (r k : V) :
    k ∈ TaggedDictionary.keys (OwnerPayloadRoute.first G P (expected G D R L active f) r).toList ↔
      r ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D r = k ∧ k ∈ active := by
  rw [first_keys G P D R hcover L active f r]
  by_cases h : r ∈ OwnerInteraction.remaining G D R L ∧ OwnerSupport.owner G D r ∈ active
  · rw [if_pos h, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨h.1, rfl, h.2⟩
    · rintro ⟨_, he, _⟩
      exact he.symm
  · rw [if_neg h]
    simp only [Finset.notMem_empty]
    constructor
    · intro hh
      exact False.elim hh
    · rintro ⟨hr, he, hk⟩
      exact h ⟨hr, he.symm ▸ hk⟩

theorem first_consistent {w : ℕ} (P : BitCode A w) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L : ℕ) (active : Finset V) (f : V → A) (r : V) :
    TaggedDictionary.Consistent f (OwnerPayloadRoute.first G P (expected G D R L active f) r).toList := by
  intro p hp
  rw [first_correct G P D R hcover L active f r] at hp
  split_ifs at hp
  · simp only [Option.toList_some, List.mem_singleton] at hp
    subst p
    rfl
  · simp at hp
  · simp at hp
end Paper.OwnerPayloadInputs
