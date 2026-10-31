import Paper.Solver.Density.CappedSilentExecution

/-! Cache entries outside a program's slots and local receiver neighborhood
remain unchanged, independently of readiness or arithmetic parameters. -/
namespace Paper.PrefixBroadcast.Program
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cachedRun_outside_unconditional {In Out : Type} (quiet : V → Bool)
    (P : Program V In Out) (s : V → In) (cache : Cache V) (offset : ℕ)
    (v u : V) (i : ℕ)
    (hout : i < offset ∨ offset + P.rounds ≤ i ∨ ¬ (v = u ∨ G.Adj v u)) :
    (P.cachedRun G quiet s cache offset).2 v u i = cache v u i := by
  induction P generalizing cache offset with
  | «local» f => rfl
  | broadcast P =>
    have hn : ¬ (i = offset ∧ (v = u ∨ G.Adj v u)) := by
      rintro ⟨he, ha⟩
      change i < offset ∨ offset + 1 ≤ i ∨ ¬ (v = u ∨ G.Adj v u) at hout
      rcases hout with h | h | h
      · omega
      · omega
      · exact h ha
    exact if_neg hn
  | seq P Q ihP ihQ =>
    change i < offset ∨ offset + (P.rounds + Q.rounds) ≤ i ∨
      ¬ (v = u ∨ G.Adj v u) at hout
    have hqo : i < offset + P.rounds ∨ offset + P.rounds + Q.rounds ≤ i ∨
        ¬ (v = u ∨ G.Adj v u) := by
      rcases hout with h | h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)
    have hpo : i < offset ∨ offset + P.rounds ≤ i ∨ ¬ (v = u ∨ G.Adj v u) := by
      rcases hout with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr h)
    exact (ihQ (s := (P.cachedRun G quiet s cache offset).1)
      (cache := (P.cachedRun G quiet s cache offset).2)
      (offset := offset + P.rounds) hqo).trans (ihP (s := s) (cache := cache) (offset := offset) hpo)
end Paper.PrefixBroadcast.Program

namespace Paper.Density.CappedSilentExecution
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Slots outside the six-round phase and unrelated sender records stay empty. -/
theorem inactive_cache (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) (v u : V) (i : ℕ)
    (hout : 6 ≤ i ∨ ¬ (v = u ∨ G.Adj v u)) :
    (run G cap m rho n).memory v u i = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((CappedOutputRegister.phase cap m rho).cachedRun G
      (run G cap m rho n).quiet (run G cap m rho n).values
      (run G cap m rho n).memory 0).2 v u i = []
    rw [PrefixBroadcast.Program.cachedRun_outside_unconditional G]
    · exact ih
    · simpa only [Nat.zero_add, CappedOutputRegister.phase_rounds] using Or.inr hout
end Paper.Density.CappedSilentExecution

#print axioms Paper.PrefixBroadcast.Program.cachedRun_outside_unconditional
#print axioms Paper.Density.CappedSilentExecution.inactive_cache

