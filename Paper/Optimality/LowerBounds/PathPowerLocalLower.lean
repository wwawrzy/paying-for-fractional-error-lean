import Paper.Preliminaries.PathPowerGap
import Paper.Preliminaries.LineLocalWindow

namespace Paper.PathPowerLocalLower
open LineLocalWindow PathPowerTreewidth SevenFoundation

/-- Finite-round lower bound for actual unrestricted per-port executions with
canonical signed ports. The code may be chosen for exact n; identifiers are
1,...,n, the graph has treewidth at most t, and no order-invariance is assumed.
A generic standard-port compiler is a separate model comparison obligation. -/
theorem lower (t T : ℕ) (c : ℝ) (hc : 0 ≤ c) (hct : c < 2*t+1) :
    ∃ n : ℕ, 0 < n ∧ (graph n t).treeWidth ≤ t ∧
      ∀ P : LineLocal.Program t Unit Bool, P.rounds ≤ T →
        (∀ ids : Fin n → ℕ, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          dominates (graph n t) (Finset.univ.filter (fun v => output P ids v = true))) →
        ∃ ids : Fin n → ℕ, Function.Injective ids ∧
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) ∧
          c * (graph n t).dominationNumber < (Finset.univ.filter (fun v => output P ids v = true)).card := by
  obtain ⟨n, hn, hwindow⟩ := PathPowerGap.window_lower_bound t (t*(T+1)) c hc hct
  refine ⟨n, hn, treeWidth_le n t, ?_⟩
  intro P hP hdom
  obtain ⟨ids, hinj, hIDs, hbad⟩ := hwindow (rule P (t*(T+1)))
  refine ⟨ids, hinj, hIDs, ?_⟩
  exact hbad (output P ids) (agrees P _ (by unfold LineLocal.Program.radius; nlinarith) ids)
    (hdom ids hinj hIDs)

end Paper.PathPowerLocalLower
