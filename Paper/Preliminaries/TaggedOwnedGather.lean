import Paper.Preliminaries.TaggedGather

/-! Actual owner-labelled bounded dictionary broadcast, used for the last
routing hop. Only the designated owner's receiver accepts a report. -/
namespace Paper.TaggedOwnedGather
open BroadcastModel SevenFoundation
variable {V A : Type} [LinearOrder V]

structure Input (V A : Type) where
  owner : V
  active : Bool
  payloads : List (V × A)

def accept (v owner : V) (active : Bool) (xs : List (V × A)) : List (V × A) :=
  if active && decide (owner = v) then xs else []

theorem mem_accept (v owner : V) (active : Bool) (xs : List (V × A)) (p : V × A) :
    p ∈ accept v owner active xs ↔ active = true ∧ owner = v ∧ p ∈ xs := by
  cases active <;> by_cases h : owner = v <;> simp [accept, h]

def round (K : ℕ) : Round V (Input V A) (List (V × A)) ((V × Bool) × {l : List (V × A) // l.length ≤ K}) where
  send _ _ s := ((s.owner, s.active), TaggedDictionary.bounded K s.payloads)
  update v N own msg := TaggedGather.collect N
    (accept v own.owner own.active (TaggedDictionary.bounded K own.payloads).val)
    (fun u => accept v (msg u).1.1 (msg u).1.2 (msg u).2.val)

def program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) :
    Program V (Input V A) (List (V × A)) :=
  .broadcast ((b + 1) + K * (b + w + 1))
    (PacketCode.product C.pairBool (ListPacket.bounded (PacketCode.product C P) K)) (round K)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem origin {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) (s : V → Input V A)
    (v : V) (p : V × A) (hp : p ∈ (program C P K).run G s v) :
    ∃ u ∈ closed G v, (s u).active = true ∧ (s u).owner = v ∧ p ∈ (s u).payloads := by
  change p ∈ TaggedGather.collect (G.neighborFinset v)
    (accept v (s v).owner (s v).active (TaggedDictionary.bounded K (s v).payloads).val)
    (fun u => accept v (s u.val).owner (s u.val).active (TaggedDictionary.bounded K (s u.val).payloads).val) at hp
  rcases (TaggedGather.mem_collect _ _ _ p).mp hp with hp | ⟨u, hp⟩
  · obtain ⟨ha, ho, hp⟩ := (mem_accept _ _ _ _ p).mp hp
    exact ⟨v, self_mem_closed G v, ha, ho, TaggedDictionary.bounded_mem K _ p hp⟩
  · obtain ⟨ha, ho, hp⟩ := (mem_accept _ _ _ _ p).mp hp
    exact ⟨u.val, (mem_closed G u.val v).mpr (Or.inr
      ((SimpleGraph.mem_neighborFinset G v u.val).mp u.property)), ha, ho, TaggedDictionary.bounded_mem K _ p hp⟩

theorem consistent {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) (s : V → Input V A)
    (f : V → A) (hs : ∀ u, TaggedDictionary.Consistent f (s u).payloads) (v : V) :
    TaggedDictionary.Consistent f ((program C P K).run G s v) := by
  intro p hp
  obtain ⟨u, _, _, _, hp⟩ := origin G C P K s v p hp
  exact hs u p hp

theorem delivers {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) (s : V → Input V A)
    (v u : V) (hu : u ∈ closed G v) (ha : (s u).active = true) (ho : (s u).owner = v)
    (hsize : (TaggedDictionary.keys (s u).payloads).card ≤ K) (k : V)
    (hk : k ∈ TaggedDictionary.keys (s u).payloads) :
    k ∈ TaggedDictionary.keys ((program C P K).run G s v) := by
  have hk' : k ∈ TaggedDictionary.keys (TaggedDictionary.bounded K (s u).payloads).val := by
    rw [TaggedDictionary.keys_bounded_eq K _ hsize]
    exact hk
  obtain ⟨p, hp, hpk⟩ := (TaggedDictionary.mem_keys _ k).mp hk'
  apply (TaggedDictionary.mem_keys _ k).mpr
  refine ⟨p, ?_, hpk⟩
  change p ∈ TaggedGather.collect (G.neighborFinset v)
    (accept v (s v).owner (s v).active (TaggedDictionary.bounded K (s v).payloads).val)
    (fun w => accept v (s w.val).owner (s w.val).active (TaggedDictionary.bounded K (s w.val).payloads).val)
  apply (TaggedGather.mem_collect _ _ _ p).mpr
  rcases (mem_closed G u v).mp hu with he | hadj
  · subst u
    exact Or.inl ((mem_accept _ _ _ _ p).mpr ⟨ha, ho, hp⟩)
  · exact Or.inr ⟨⟨u, (SimpleGraph.mem_neighborFinset G v u).mpr hadj⟩, (mem_accept _ _ _ _ p).mpr ⟨ha, ho, hp⟩⟩

theorem rounds {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) : (program C P K).rounds = 1 := rfl

theorem maxBits {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (K : ℕ) :
    (program C P K).maxBits = (b + 1) + K * (b + w + 1) := rfl
end Paper.TaggedOwnedGather
