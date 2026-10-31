import Paper.Communication.BoundedGossipRound

/-! A concrete R-round bounded-bit gossip program, with actual run
semantics. The fixed list capacity never drops information on bounded
degree inputs with bounded initial local payloads. -/
namespace Paper.BoundedGossip
open BroadcastModel
variable {V A : Type} [LinearOrder V] [DecidableEq A]

def program {b : ℕ} (C : BitCode A b) (Δ M R : ℕ) : Program V (List A) (List A) :=
  (BoundedGossipRound.program C (M * (Δ + 1) ^ R)).iterate R

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def state {b : ℕ} (C : BitCode A b) (B : ℕ) (initial : V → List A) (r : ℕ) : V → List A :=
  ((BoundedGossipRound.program C B).iterate r).run G initial

theorem state_succ {b : ℕ} (C : BitCode A b) (B : ℕ) (initial : V → List A) (r : ℕ) :
    state G C B initial (r + 1) = eval G (BoundedGossipRound.round B) (state G C B initial r) := rfl

set_option maxHeartbeats 1000000 in
theorem invariant {b : ℕ} (C : BitCode A b) (Δ M R : ℕ) (initial : V → List A)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hinit : ∀ v, (initial v).length ≤ M)
    (hnodup : ∀ v, (initial v).Nodup) (r : ℕ) (hr : r ≤ R) :
    let B := M * (Δ + 1) ^ R
    (∀ v, (state G C B initial r v).Nodup) ∧
      (∀ v, (state G C B initial r v).toFinset =
        GossipKnowledge.knowledge G (fun u => (initial u).toFinset) r v) ∧
      ∀ v, (state G C B initial r v).length ≤ B := by
  dsimp only
  let B := M * (Δ + 1) ^ R
  let initialSet := fun u => (initial u).toFinset
  have hinitSet : ∀ v, (initialSet v).card ≤ M := by
    intro v
    change (initial v).toFinset.card ≤ M
    rw [List.toFinset_card_of_nodup (hnodup v)]
    exact hinit v
  have hbound : ∀ j ≤ R, ∀ v, (GossipKnowledge.knowledge G initialSet j v).card ≤ B := by
    intro j hj v
    exact (GossipKnowledge.card_bound G initialSet Δ M hdeg hinitSet j v).trans
      (Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by omega) hj))
  have hlength (j : ℕ) (hj : j ≤ R) (s : V → List A)
      (heq : ∀ v, (s v).toFinset = GossipKnowledge.knowledge G initialSet j v)
      (hn : ∀ v, (s v).Nodup) : ∀ v, (s v).length ≤ B := by
    intro v
    have hc := hbound j hj v
    rw [← heq v, List.toFinset_card_of_nodup (hn v)] at hc
    exact hc
  revert hr
  induction r with
  | zero =>
    intro hr
    exact ⟨hnodup, fun _ => rfl, hlength 0 hr initial (fun _ => rfl) hnodup⟩
  | succ r ih =>
    intro hr
    have hi := ih (by omega)
    have hiEq : ∀ u, (state G C B initial r u).toFinset = GossipKnowledge.knowledge G initialSet r u := hi.2.1
    have hn : ∀ v, (state G C B initial (r + 1) v).Nodup := by
      intro v
      rw [state_succ]
      exact BoundedGossipRound.eval_nodup G B _ v
    have heq : ∀ v, (state G C B initial (r + 1) v).toFinset =
        GossipKnowledge.knowledge G initialSet (r + 1) v := by
      intro v
      rw [state_succ]
      calc
        _ = (state G C B initial r v).toFinset ∪
            (G.neighborFinset v).biUnion (fun u => (state G C B initial r u).toFinset) :=
          BoundedGossipRound.eval_finset G B _ hi.2.2 v
        _ = _ := by simp only [hiEq, GossipKnowledge.knowledge]
    exact ⟨hn, heq, hlength (r + 1) hr _ heq hn⟩

theorem correct {b : ℕ} (C : BitCode A b) (Δ M R : ℕ) (initial : V → List A)
    (hdeg : ∀ v, G.degree v ≤ Δ) (hinit : ∀ v, (initial v).length ≤ M)
    (hnodup : ∀ v, (initial v).Nodup) :
    (∀ v, ((program C Δ M R).run G initial v).toFinset =
      GossipKnowledge.knowledge G (fun u => (initial u).toFinset) R v) ∧
      (program (V := V) C Δ M R).rounds = R ∧
        (program (V := V) C Δ M R).maxBits ≤ M * (Δ + 1) ^ R * (b + 1) := by
  refine ⟨(invariant G C Δ M R initial hdeg hinit hnodup R le_rfl).2.1, ?_, ?_⟩
  · simp only [program, Program.iterate_rounds, BoundedGossipRound.program, Program.rounds, mul_one]
  · exact Program.iterate_maxBits (BoundedGossipRound.program (V := V) C _) R
end Paper.BoundedGossip
