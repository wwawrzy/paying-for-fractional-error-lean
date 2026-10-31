import Paper.Preliminaries.TaggedGather
import Paper.Owners.Construction.OwnerMetadataCorrect

/-! First actual routing hop: each remaining demand reads the current
payload of its owner from that owner's one physical broadcast. Message
needs only the sender's active bit and payload, since physical senders have
known identifiers. Self-owned demands read their own private payload. -/
namespace Paper.OwnerPayloadRead
open BroadcastModel SevenFoundation
variable {V A : Type} [LinearOrder V]

structure Input (V A : Type) where
  owner : V
  remaining : Bool
  active : Bool
  payload : A

def read (v : V) (N : Finset V) (s : Input V A) (msg : N → Bool × A) : Option (V × A) :=
  if s.remaining then
    if s.owner = v then if s.active then some (s.owner, s.payload) else none
    else if h : s.owner ∈ N then if (msg ⟨s.owner, h⟩).1 then some (s.owner, (msg ⟨s.owner, h⟩).2) else none
    else none
  else none

def round : Round V (Input V A) (Option (V × A)) (Bool × A) where
  send _ _ s := (s.active, s.payload)
  update v N s msg := read v N s msg

def program {w : ℕ} (P : BitCode A w) : Program V (Input V A) (Option (V × A)) :=
  .broadcast (1 + w) (PacketCode.product BitCode.bool P) round

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {w : ℕ} (P : BitCode A w) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L : ℕ) (active : Finset V) (f : V → A) (s : V → Input V A)
    (ho : ∀ u, (s u).owner = OwnerSupport.owner G D u)
    (hr : ∀ u, (s u).remaining = decide (u ∈ OwnerInteraction.remaining G D R L))
    (ha : ∀ u, (s u).active = decide (u ∈ active)) (hp : ∀ u, (s u).payload = f u) (r : V) :
    (program P).run G s r = if r ∈ OwnerInteraction.remaining G D R L then
      if OwnerSupport.owner G D r ∈ active then some (OwnerSupport.owner G D r, f (OwnerSupport.owner G D r)) else none
      else none := by
  change read r (G.neighborFinset r) (s r) (fun u => ((s u.val).active, (s u.val).payload)) = _
  unfold read
  rw [hr r]
  by_cases hrem : r ∈ OwnerInteraction.remaining G D R L
  · simp only [decide_eq_true hrem, ↓reduceIte, if_pos hrem]
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    have hrR : r ∈ R := by
      have hh := hrem
      rw [OwnerInteraction.remaining, hinst] at hh
      exact (Finset.mem_sdiff.mp hh).1
    have hh := @OwnerSupport.owner_of_covered V _ _ G _ D r
    rw [hinst] at hh
    have howned := (hh (hcover hrR)).2
    rw [ho r]
    by_cases he : OwnerSupport.owner G D r = r
    · rw [if_pos he, ha r, hp r, he]
      by_cases hh : r ∈ active <;> simp [hh]
    · have hn : OwnerSupport.owner G D r ∈ G.neighborFinset r := by
        exact (SimpleGraph.mem_neighborFinset G r _).mpr ((howned.resolve_left he).symm)
      rw [if_neg he, dif_pos hn]
      rw [ha _, hp _]
      by_cases hh : OwnerSupport.owner G D r ∈ active <;> simp [hh]
  · simp only [decide_eq_false hrem, Bool.false_eq_true, ↓reduceIte, if_neg hrem]

theorem rounds {w : ℕ} (P : BitCode A w) : (program (V := V) P).rounds = 1 := rfl

theorem maxBits {w : ℕ} (P : BitCode A w) : (program (V := V) P).maxBits = 1 + w := rfl
end Paper.OwnerPayloadRead
