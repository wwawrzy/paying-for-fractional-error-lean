import Paper.Preliminaries.TaggedDictionary
import Paper.Preliminaries.SevenFoundation

/-! One actual bounded dictionary broadcast. Its received list may be large
and contain repeated keys; no payload order/equality assumption is needed. -/
namespace Paper.TaggedGather
open BroadcastModel SevenFoundation
variable {V A : Type} [LinearOrder V]

def collect (N : Finset V) (own : List (V × A)) (msg : N → List (V × A)) : List (V × A) :=
  own ++ N.sort.attach.flatMap (fun u => msg ⟨u.val, (Finset.mem_sort (· ≤ ·)).mp u.property⟩)

theorem mem_collect (N : Finset V) (own : List (V × A)) (msg : N → List (V × A)) (p : V × A) :
    p ∈ collect N own msg ↔ p ∈ own ∨ ∃ u : N, p ∈ msg u := by
  simp only [collect, List.mem_append, List.mem_flatMap]
  constructor
  · rintro (hp | ⟨u, _, hp⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨⟨u.val, (Finset.mem_sort (· ≤ ·)).mp u.property⟩, hp⟩
  · rintro (hp | ⟨u, hp⟩)
    · exact Or.inl hp
    · exact Or.inr ⟨⟨u.val, (Finset.mem_sort (· ≤ ·)).mpr u.property⟩, List.mem_attach _ _, hp⟩

theorem keys_collect (N : Finset V) (own : List (V × A)) (msg : N → List (V × A)) :
    TaggedDictionary.keys (collect N own msg) = TaggedDictionary.keys own ∪ N.attach.biUnion (fun u => TaggedDictionary.keys (msg u)) := by
  ext k
  simp only [TaggedDictionary.mem_keys, mem_collect, Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨p, hp | ⟨u, hp⟩, hk⟩
    · exact Or.inl ⟨p, hp, hk⟩
    · exact Or.inr ⟨u, p, hp, hk⟩
  · rintro (⟨p, hp, hk⟩ | ⟨u, p, hp, hk⟩)
    · exact ⟨p, Or.inl hp, hk⟩
    · exact ⟨p, Or.inr ⟨u, hp⟩, hk⟩

def round (K : ℕ) : Round V (List (V × A)) (List (V × A)) {l : List (V × A) // l.length ≤ K} where
  send _ _ xs := TaggedDictionary.bounded K xs
  update _ N own msg := collect N (TaggedDictionary.bounded K own).val (fun u => (msg u).val)

def program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) : Program V (List (V × A)) (List (V × A)) :=
  .broadcast (K * (b + w + 1)) (ListPacket.bounded (PacketCode.product C P) K) (round K)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem origin {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) (xs : V → List (V × A))
    (v : V) (p : V × A) (hp : p ∈ (program C P K).run G xs v) : ∃ u ∈ closed G v, p ∈ xs u := by
  change p ∈ collect (G.neighborFinset v) (TaggedDictionary.bounded K (xs v)).val
    (fun u => (TaggedDictionary.bounded K (xs u.val)).val) at hp
  rcases (mem_collect _ _ _ p).mp hp with hp | ⟨u, hp⟩
  · exact ⟨v, self_mem_closed G v, TaggedDictionary.bounded_mem K (xs v) p hp⟩
  · exact ⟨u.val, (mem_closed G u.val v).mpr (Or.inr
      ((SimpleGraph.mem_neighborFinset G v u.val).mp u.property)), TaggedDictionary.bounded_mem K (xs u.val) p hp⟩

theorem consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) (xs : V → List (V × A))
    (f : V → A) (hs : ∀ u, TaggedDictionary.Consistent f (xs u)) (v : V) :
    TaggedDictionary.Consistent f ((program C P K).run G xs v) := by
  intro p hp
  obtain ⟨u, _, hu⟩ := origin G C P K xs v p hp
  exact hs u p hu

theorem keys_correct {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) (xs : V → List (V × A))
    (hs : ∀ u, (TaggedDictionary.keys (xs u)).card ≤ K) (v : V) :
    TaggedDictionary.keys ((program C P K).run G xs v) = (closed G v).biUnion (fun u => TaggedDictionary.keys (xs u)) := by
  change TaggedDictionary.keys (collect (G.neighborFinset v) (TaggedDictionary.bounded K (xs v)).val
    (fun u => (TaggedDictionary.bounded K (xs u.val)).val)) = _
  rw [keys_collect]
  simp only [TaggedDictionary.keys_bounded_eq K _ (hs _)]
  ext k
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach, true_and, mem_closed]
  constructor
  · rintro (hk | ⟨u, hk⟩)
    · exact ⟨v, Or.inl rfl, hk⟩
    · exact ⟨u.val, Or.inr ((SimpleGraph.mem_neighborFinset G v u.val).mp u.property), hk⟩
  · rintro ⟨u, he | ha, hk⟩
    · subst u
      exact Or.inl hk
    · exact Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr ha⟩, hk⟩

theorem rounds {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) : (program C P K).rounds = 1 := rfl

theorem maxBits {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) :
    (program C P K).maxBits = K * (b + w + 1) := rfl
end Paper.TaggedGather
