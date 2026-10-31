import Paper.Optimality.Treewidth.Pathwidth
import Paper.Optimality.Treewidth.CliqueMinor
import Paper.Optimality.LowerBounds.TreewidthLocalLower

/-! The same actual path-power executions witness sharp LOCAL lower bounds
inside pathwidth classes and every excluded-complete-minor class. -/
namespace Paper.ClassLocalLower

open SimpleGraph SevenFoundation PathPowerTreewidth TreewidthLocalLower

/-- Exact-order deterministic LOCAL obstruction, against integral domination.
The order is chosen before the program, so the code may know that order. -/
def Witness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : ℕ) (c : ℝ) : Prop :=
  ∀ P : PortLocal.Program Unit Bool, P.rounds ≤ T →
    (∀ N : PortLocal.Network (Fin n), N.Compatible G →
      ∀ ids : Fin n → ℕ, Function.Injective ids →
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n) → dominates G (output N P ids)) →
    ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → ℕ),
      N.Compatible G ∧ Function.Injective ids ∧
      Finset.univ.image ids = Finset.Icc 1 n ∧
      c * G.dominationNumber < (output N P ids).card

theorem pathwidth (r T : ℕ) (c : ℝ) (hc : c < 2 * r + 1) :
    ∃ n : ℕ, 0 < n ∧ Pathwidth.width (graph n r) ≤ r ∧ Witness (graph n r) T c := by
  obtain ⟨n, hn, _, hbad⟩ := TreewidthLocalLower.exact_lower r T c hc
  exact ⟨n, hn, Pathwidth.pathPower_width n r, hbad⟩

theorem excluded_clique (h T : ℕ) (hh : 3 ≤ h) (c : ℝ) (hc : c < 2 * h - 3) :
    ∃ n : ℕ, 0 < n ∧ (graph n (h - 2)).IsKMinorFree h ∧
      Witness (graph n (h - 2)) T c := by
  have hcast : ((h - 2 : ℕ) : ℝ) = (h : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ h by omega)]
    norm_num
  have hcoef : c < 2 * ((h - 2 : ℕ) : ℝ) + 1 := by linarith
  obtain ⟨n, hn, htw, hbad⟩ := TreewidthLocalLower.exact_lower (h - 2) T c hcoef
  exact ⟨n, hn, CliqueMinorTreewidth.excluded htw (by omega), hbad⟩

end Paper.ClassLocalLower

#print axioms Paper.ClassLocalLower.pathwidth
#print axioms Paper.ClassLocalLower.excluded_clique
