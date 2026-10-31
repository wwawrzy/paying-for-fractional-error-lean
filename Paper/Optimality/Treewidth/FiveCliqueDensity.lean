import Paper.Optimality.Treewidth.CliqueDenseCore
import Paper.Optimality.Treewidth.CliqueFourElimination
import GraphTheory.SimpleGraph.Minor.Density
import Paper.Endpoints.Rounding.MinorDensityKT0

/-! Sharp K5-minor-free density. A dense contraction core would have three
common neighbors per edge, forcing minimum degree three in every nonempty
neighborhood. That neighborhood excludes K4 and hence has a proved vertex
of degree at most two: a contradiction. -/
namespace Paper.FiveCliqueDensity

open SimpleGraph SevenFoundation BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (hG : G.IsKMinorFree 5) : G.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  by_cases hV : 0 < Fintype.card V
  · by_contra hbound
    have hdense : 3 * Fintype.card V ≤ G.edgeFinset.card := by omega
    obtain ⟨W, _, _, H, _, hW, _, hpositive, hcn, hm⟩ :=
      CliqueDenseCore.extract G 3 (by decide) hV hdense
    letI : Nonempty W := Fintype.card_pos_iff.mp hW
    have hH : H.IsKMinorFree 5 := IsHMinorFree.minor hG hm
    let v : W := Classical.arbitrary W
    have hN : 0 < Fintype.card (H.neighborSet v) := by
      rw [H.card_neighborSet_eq_degree]
      exact hpositive v
    letI : Nonempty (H.neighborSet v) := Fintype.card_pos_iff.mp hN
    obtain ⟨w, hw⟩ := CliqueFourElimination.low_degree (H.induce (H.neighborSet v))
      (CliqueDenseCore.neighborhood_excludes_four H hH v)
    have hthree := commonNeighbors_implies_induced_degree H v 3 w (hcn v w w.property)
    omega
  · have hc : Fintype.card V = 0 := by omega
    have hd := hG.edgeFinset_card_le G
    rw [hc, Nat.mul_zero] at hd
    omega

theorem minor_density (hG : G.IsKMinorFree 5) : MinorDensity.Bound G 3 := by
  intro A _ _ J _ hm
  exact_mod_cast edge_bound J (IsHMinorFree.minor hG hm)

theorem exact_KT0 :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsKMinorFree 5 → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ 7 * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  obtain ⟨p, hp⟩ := MinorDensityKT0.exact_minor_density 3 (by decide)
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  have hd : MinorDensity.Bound G ((3 : ℚ) : ℝ) := by simpa using minor_density G hG
  have hresult := hp G hd ports C
  norm_num at hresult
  exact hresult

end Paper.FiveCliqueDensity

#print axioms Paper.FiveCliqueDensity.edge_bound
#print axioms Paper.FiveCliqueDensity.minor_density
#print axioms Paper.FiveCliqueDensity.exact_KT0
