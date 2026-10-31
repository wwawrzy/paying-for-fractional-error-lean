import Paper.Preliminaries.ListPacket
import Paper.Communication.GossipKnowledge

/-! A real graph-independent receiver-independent broadcast round for
bounded list gossip. All sent packets have a proved fixed bit width. -/
namespace Paper.BoundedGossipRound
open BroadcastModel
variable {V A : Type} [LinearOrder V] [DecidableEq A]

def flatten (N : Finset V) (f : N → List A) : List A := (N.attach.sort (· ≤ ·)).flatMap f

theorem mem_flatten (N : Finset V) (f : N → List A) (a : A) :
    a ∈ flatten N f ↔ ∃ u : N, a ∈ f u := by
  simp only [flatten, List.mem_flatMap, Finset.mem_sort, Finset.mem_attach, true_and]

def round (B : ℕ) : Round V (List A) (List A) {l : List A // l.length ≤ B} where
  send _ _ s := ListPacket.truncate B s
  update _ N s incoming := (s ++ flatten N (fun u => (incoming u).val)).dedup

def program {b : ℕ} (C : BitCode A b) (B : ℕ) : Program V (List A) (List A) :=
  .broadcast (B * (b + 1)) (ListPacket.bounded C B) (round B)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem eval_finset (B : ℕ) (s : V → List A) (hs : ∀ v, (s v).length ≤ B) (v : V) :
    (eval G (round B) s v).toFinset = (s v).toFinset ∪
      (G.neighborFinset v).biUnion (fun u => (s u).toFinset) := by
  classical
  change ((s v ++ flatten (G.neighborFinset v) (fun u => (ListPacket.truncate B (s u.val)).val)).dedup).toFinset = _
  simp_rw [ListPacket.truncate_eq B _ (hs _)]
  ext a
  simp only [List.mem_toFinset, List.mem_dedup, List.mem_append, mem_flatten,
    Finset.mem_union, Finset.mem_biUnion]
  constructor
  · rintro (ha | ⟨u, ha⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨u.val, u.property, ha⟩
  · rintro (ha | ⟨u, hu, ha⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨⟨u, hu⟩, ha⟩

theorem eval_nodup (B : ℕ) (s : V → List A) (v : V) : (eval G (round B) s v).Nodup := by
  exact List.nodup_dedup _
end Paper.BoundedGossipRound
