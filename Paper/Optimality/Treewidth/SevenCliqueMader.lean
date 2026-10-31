import Paper.External.Mader1968
import GraphTheory.SimpleGraph.Minor.Density
import Paper.Endpoints.Rounding.MinorDensityKT0

/-! The K₇ branch of sc:optimal, conditional on the independently reviewed
Mader axiom. All adapters and the actual KT0 algorithm are Lean proofs.
The existing finite-order K₇ proofs remain independent of this axiom. -/
namespace Paper.SevenCliqueMader
open SimpleGraph SevenFoundation BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (hG : G.IsKMinorFree 7) (hV : 5 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 5 * Fintype.card V - 15 := by
  have h := External.Mader1968.k7_edge_bound G hG hV
  omega

theorem weak_bound (hG : G.IsKMinorFree 7) : G.edgeFinset.card ≤ 5 * Fintype.card V := by
  by_cases hV : 5 ≤ Fintype.card V
  · exact (edge_bound G hG hV).trans (Nat.sub_le _ _)
  · have hsmall : ∀ n : ℕ, n ≤ 4 → n.choose 2 ≤ 5 * n := by
      intro n hn
      interval_cases n <;> decide
    exact G.card_edgeFinset_le_card_choose_two.trans (hsmall _ (by omega))

theorem minor_density (hG : G.IsKMinorFree 7) : MinorDensity.Bound G 5 := by
  intro A _ _ J _ hm
  exact_mod_cast weak_bound J (IsHMinorFree.minor hG hm)

theorem exact_KT0 :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsKMinorFree 7 → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ 11 * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  obtain ⟨p, hp⟩ := MinorDensityKT0.exact_minor_density 5 (by decide)
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  have hd : MinorDensity.Bound G ((5 : ℚ) : ℝ) := by simpa using minor_density G hG
  have hresult := hp G hd ports C
  norm_num at hresult
  exact hresult

end Paper.SevenCliqueMader
