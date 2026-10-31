import Paper.Preliminaries.TreeAggregateQuiet

/-! Actual rank-directed aggregation of any bounded-code commutative-monoid
payload. Exactly D broadcast rounds transfer every active vertex's mass to
the elected root, including on physical graphs of unbounded degree. -/
namespace Paper.TreeAggregate
open BroadcastModel BroadcastRouting TreeAggregateRound TreeAggregateQuiet
variable {V A : Type} [LinearOrder V] [AddCommMonoid A]

def program {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    ℕ → Program V (State V A D) (State V A D)
  | 0 => .local fun _ _ s => s
  | r + 1 => .seq (TreeAggregateRound.program C F D (r + 1)) (program C F D r)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {D : ℕ} {active : V → Bool} {root : V} {nodes : V → ParentElection.Node V D}

theorem invariant {b c : ℕ} (C : BitCode V b) (F : BitCode A c)
    (h : LeaderTreeCorrect.Spec G active D root nodes)
    (r : ℕ) (s : V → State V A D) (hs : ∀ v, (s v).1 = nodes v)
    (hq : Quiet active nodes r s) :
    (∀ v, ((program C F D r).run G s v).1 = nodes v) ∧
    Quiet active nodes 0 ((program C F D r).run G s) ∧
    (∑ v, ((program C F D r).run G s v).2) = ∑ v, (s v).2 := by
  induction r generalizing s with
  | zero => exact ⟨hs, hq, rfl⟩
  | succ r ih =>
    let t := eval G (round D (r + 1)) s
    have ht : ∀ v, (t v).1 = nodes v := hs
    have hqt : Quiet active nodes r t := TreeAggregateQuiet.step G h r s hs hq
    obtain ⟨hn, hq', hsum⟩ := ih t ht hqt
    refine ⟨hn, hq', hsum.trans ?_⟩
    apply TreeAggregateRound.conservation G
    intro v u hp
    rw [hs v] at hp
    exact h.parent_edge v u hp

theorem correct {b c : ℕ} (C : BitCode V b) (F : BitCode A c)
    (h : LeaderTreeCorrect.Spec G active D root nodes) (weights : V → A)
    (hz : ∀ v, active v = false → weights v = 0) :
    (∀ v, ((program C F D D).run G (fun u => (nodes u, weights u)) v).1 = nodes v) ∧
    ((program C F D D).run G (fun u => (nodes u, weights u)) root).2 = ∑ v, weights v ∧
    (∀ v, v ≠ root → ((program C F D D).run G (fun u => (nodes u, weights u)) v).2 = 0) := by
  have hq : Quiet active nodes D (fun u => (nodes u, weights u)) := by
    intro v hv
    rcases hv with hv | hv
    · exact hz v hv
    · cases ha : active v with
      | false => exact hz v ha
      | true => exact False.elim (Nat.not_lt_of_ge (h.rank_bound v ha) hv)
  obtain ⟨hn, hq', hsum⟩ := invariant G C F h D (fun u => (nodes u, weights u)) (fun _ => rfl) hq
  have hzero : ∀ v, v ≠ root →
      ((program C F D D).run G (fun u => (nodes u, weights u)) v).2 = 0 := by
    intro v hv
    cases ha : active v with
    | false => exact hq' v (Or.inl ha)
    | true =>
      obtain ⟨u, hu⟩ := h.parent_exists v ha hv
      have hh := h.parent_rank v u hu
      exact hq' v (Or.inr (by omega))
  refine ⟨hn, ?_, hzero⟩
  rw [Finset.sum_eq_single root] at hsum
  · exact hsum
  · intro v _ hv
    exact hzero v hv
  · simp

theorem rounds {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D r : ℕ) :
    (program C F D r).rounds = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [program, Program.rounds, TreeAggregateRound.program, ih]; omega

theorem maxBits {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D r : ℕ) :
    (program C F D r).maxBits ≤ b + c + 1 := by
  induction r with
  | zero => exact Nat.zero_le _
  | succ r ih => exact max_le (le_refl _) ih
end Paper.TreeAggregate
