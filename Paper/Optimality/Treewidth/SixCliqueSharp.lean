import Paper.Optimality.Treewidth.SixCliqueSixNeighbors
import Paper.Optimality.Treewidth.SixCliqueSevenNeighbors
import GraphTheory.SimpleGraph.Minor.Density
import Paper.Endpoints.Rounding.MinorDensityKT0

/-! Actual K6-free extremal density and the coefficient-nine broadcast
endpoint. Both possible least degrees of the global affine counterexample
are excluded by proved component and separator projections. -/
namespace Paper.SixCliqueSharp

open SimpleGraph SevenFoundation BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (hG : G.IsKMinorFree 6) (hV : 4 ≤ Fintype.card V) :
    G.edgeFinset.card ≤ 4 * Fintype.card V - 10 := by
  classical
  by_contra hn
  obtain ⟨W, _, _, H, _, hm, hH, horder, he, hc, hd, hminimal, hsep,
      v, hvmin, hcases⟩ := SixCliqueGlobalReduction.extract G hG hV (by omega)
  rcases hcases with h6 | h7
  · exact SixCliqueSixNeighbors.impossible H hH horder hsep v h6 (hc v)
  · exact SixCliqueSevenNeighbors.impossible H hH horder he
      (fun z => (by decide : 4 ≤ 6).trans (hd z)) hminimal hsep v h7 (hc v)

theorem weak_bound (hG : G.IsKMinorFree 6) : G.edgeFinset.card ≤ 4 * Fintype.card V := by
  by_cases hV : 4 ≤ Fintype.card V
  · exact (edge_bound G hG hV).trans (Nat.sub_le _ _)
  · have hsmall : ∀ n : ℕ, n ≤ 3 → n.choose 2 ≤ 4 * n := by
      intro n hn
      interval_cases n <;> decide
    exact G.card_edgeFinset_le_card_choose_two.trans (hsmall _ (by omega))

theorem minor_density (hG : G.IsKMinorFree 6) : MinorDensity.Bound G 4 := by
  intro A _ _ J _ hm
  exact_mod_cast weak_bound J (IsHMinorFree.minor hG hm)

theorem exact_KT0 :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsKMinorFree 6 → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ 9 * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  obtain ⟨p, hp⟩ := MinorDensityKT0.exact_minor_density 4 (by decide)
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  have hd : MinorDensity.Bound G ((4 : ℚ) : ℝ) := by simpa using minor_density G hG
  have hresult := hp G hd ports C
  norm_num at hresult
  exact hresult

end Paper.SixCliqueSharp

#print axioms Paper.SixCliqueSharp.edge_bound
#print axioms Paper.SixCliqueSharp.weak_bound
#print axioms Paper.SixCliqueSharp.minor_density
#print axioms Paper.SixCliqueSharp.exact_KT0
