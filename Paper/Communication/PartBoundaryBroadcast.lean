import Paper.Preliminaries.DisjointPartLabels
import Paper.Owners.Construction.BoundaryOwners
import Paper.Preliminaries.ListPacket

/-! One real bounded-list broadcast detects exactly the boundary owners
of any actual finite disjoint partition. Empty labels mark inactive nodes. -/
namespace Paper.PartBoundaryBroadcast
open BroadcastModel
variable {V : Type} [LinearOrder V]

def round (k : ℕ) : Round V (Finset V) Bool {l : List V // l.length ≤ k} where
  send _ _ s := ListPacket.truncate k (s.sort (· ≤ ·))
  update _ N s incoming := decide (s.Nonempty ∧ ∃ u : N,
    (incoming u).val.toFinset.Nonempty ∧ s ≠ (incoming u).val.toFinset)

def program {b : ℕ} (C : BitCode V b) (k : ℕ) : Program V (Finset V) Bool :=
  .broadcast (k * (b + 1)) (ListPacket.bounded C k) (round k)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (S : Finset V) (k : ℕ) (P : SmallParts.Data G S k) (v : V) :
    (program C k).run G (DisjointPartLabels.label P.parts) v =
      decide (v ∈ BoundaryOwners.vertices G S P.parts) := by
  have hd : ∀ u, (ListPacket.truncate k ((DisjointPartLabels.label P.parts u).sort (· ≤ ·))).val.toFinset =
      DisjointPartLabels.label P.parts u := by
    intro u
    rw [ListPacket.truncate_eq k _ (by rw [Finset.length_sort]; exact DisjointPartLabels.size G S k P u),
      Finset.sort_toFinset]
  change decide ((DisjointPartLabels.label P.parts v).Nonempty ∧ ∃ u : G.neighborFinset v,
    (ListPacket.truncate k ((DisjointPartLabels.label P.parts u.val).sort (· ≤ ·))).val.toFinset.Nonempty ∧
      DisjointPartLabels.label P.parts v ≠
        (ListPacket.truncate k ((DisjointPartLabels.label P.parts u.val).sort (· ≤ ·))).val.toFinset) = _
  simp only [hd, DisjointPartLabels.nonempty_iff G S k P]
  rw [decide_eq_decide]
  simp only [BoundaryOwners.vertices, Set.mem_toFinset, SimpleGraph.mem_support, PartCut.graph]
  constructor
  · rintro ⟨hv, u, hu, hne⟩
    refine ⟨u.val, (G.mem_neighborFinset v u.val).mp u.property, hv, hu, ?_⟩
    intro hsame
    exact hne ((DisjointPartLabels.same_iff G S k P v u.val hv hu).mpr hsame)
  · rintro ⟨u, ha, hv, hu, hsame⟩
    refine ⟨hv, ⟨u, (G.mem_neighborFinset v u).mpr ha⟩, hu, ?_⟩
    intro he
    exact hsame ((DisjointPartLabels.same_iff G S k P v u hv hu).mp he)

theorem rounds {b : ℕ} (C : BitCode V b) (k : ℕ) : (program C k).rounds = 1 := rfl

theorem maxBits {b : ℕ} (C : BitCode V b) (k : ℕ) : (program C k).maxBits = k * (b + 1) := rfl
end Paper.PartBoundaryBroadcast
