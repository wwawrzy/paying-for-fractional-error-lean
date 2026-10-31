import Paper.Owners.Construction.BroadcastRouting
import Paper.Preliminaries.PacketCode
import Paper.Preliminaries.ParentElection

/-! A rank-directed transfer round. A sender broadcasts one target header
and its current mass to all neighbors. Only the named parent retains it.
The sender clears the transferred mass; all other local mass is kept. -/
namespace Paper.TreeAggregateRound
open BroadcastModel BroadcastRouting
variable {V A : Type} [DecidableEq V] [AddCommMonoid A]

abbrev State (V A : Type) (D : ℕ) := ParentElection.Node V D × A

def packet {D : ℕ} (r : ℕ) (s : State V A D) : Option (V × A) :=
  if s.1.rank.val = r then s.1.parent.map (fun u => (u, s.2)) else none

def keep {D : ℕ} (r : ℕ) (s : State V A D) : A :=
  if s.1.rank.val = r ∧ s.1.parent.isSome then 0 else s.2

def round (D r : ℕ) : Round V (State V A D) (State V A D) (Option (V × A)) where
  send _ _ s := packet r s
  update v _ s incoming := (s.1, keep r s + ∑ w, payload v (incoming w))

def program {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D r : ℕ) :
    Program V (State V A D) (State V A D) :=
  .broadcast (b + c + 1) (PacketCode.product C F).option (round D r)

theorem packet_some {D r : ℕ} {s : State V A D} {u : V} {a : A}
    (h : packet r s = some (u, a)) :
    s.1.rank.val = r ∧ s.1.parent = some u ∧ a = s.2 := by
  unfold packet at h
  split at h
  · rename_i hr
    cases hp : s.1.parent with
    | none => simp [hp] at h
    | some w =>
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨hr, congrArg some h.1, h.2.symm⟩
  · contradiction

theorem local_conservation {D : ℕ} (r : ℕ) (s : State V A D) :
    keep r s + mass (packet r s) = s.2 := by
  by_cases hr : s.1.rank.val = r
  · cases hp : s.1.parent <;> simp [keep, packet, hr, hp, mass]
  · simp [keep, packet, hr, mass]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem eval_node (D r : ℕ) (s : V → State V A D) (v : V) :
    (eval G (round D r) s v).1 = (s v).1 := rfl

theorem eval_mass (D r : ℕ) (s : V → State V A D) (v : V) :
    (eval G (round D r) s v).2 = keep r (s v) +
      received G (fun w => packet r (s w)) v := by
  change keep r (s v) + ∑ w : G.neighborFinset v, payload v (packet r (s w)) = _
  congr 1
  exact Finset.sum_coe_sort (G.neighborFinset v) (fun w : V => payload v (packet r (s w)))

theorem conservation (D r : ℕ) (s : V → State V A D)
    (hedge : ∀ v u, (s v).1.parent = some u → G.Adj v u) :
    ∑ v, (eval G (round D r) s v).2 = ∑ v, (s v).2 := by
  simp only [eval_mass, Finset.sum_add_distrib]
  rw [BroadcastRouting.conservation G (fun w => packet r (s w))
    (fun v u a h => hedge v u (packet_some h).2.1)]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => local_conservation r (s v))
end Paper.TreeAggregateRound
