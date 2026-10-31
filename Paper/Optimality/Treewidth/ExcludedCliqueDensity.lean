import Paper.Optimality.Treewidth.SmallCliqueDensity
import Paper.Optimality.Treewidth.FiveCliqueDensity
import Paper.Optimality.Treewidth.SixCliqueSharp
import Paper.Optimality.Treewidth.SevenCliqueMader
import Paper.External.CliqueDensity
/-! The complete excluded-clique upper-bound branch of sc:optimal, 3≤t≤9.
The K3–K6 cases have core-only proofs; K7–K9 use only their explicitly
reviewed literature assumptions. The actual algorithm and its communication
bounds follow from the proved density-to-KT0 construction. -/
namespace Paper.ExcludedCliqueDensity
open SimpleGraph SevenFoundation BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 9) (hG : G.IsKMinorFree h) :
    G.edgeFinset.card ≤ (h - 2) * Fintype.card V := by
  interval_cases h
  · simpa using SmallCliqueDensity.edge_bound G 3 (by decide) (by decide) hG
  · simpa using SmallCliqueDensity.edge_bound G 4 (by decide) (by decide) hG
  · simpa using FiveCliqueDensity.edge_bound G hG
  · simpa using SixCliqueSharp.weak_bound G hG
  · simpa using SevenCliqueMader.weak_bound G hG
  · simpa using External.CliqueDensity.k8_edge_bound G hG
  · simpa using External.CliqueDensity.k9_edge_bound G hG

theorem minor_density (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 9) (hG : G.IsKMinorFree h) :
    MinorDensity.Bound G ((h - 2 : ℕ) : ℝ) := by
  intro A _ _ J _ hm
  have hJ : J.IsKMinorFree h := IsHMinorFree.minor hG hm
  exact_mod_cast edge_bound J h hlo hhi hJ

theorem exact_KT0 (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 9) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsKMinorFree h → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (MinorDensityKT0.output G ports C p) ∧
          ((MinorDensityKT0.output G ports C p).card : ℝ) ≤ (2 * (h : ℝ) - 3) * fractionalNumber G ∧
          (MinorDensityKT0.program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (MinorDensityKT0.program C p).maxBits ≤
              max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  have hpos : (1 : ℚ) ≤ (h - 2 : ℕ) := by exact_mod_cast (show 1 ≤ h - 2 by omega)
  obtain ⟨p, hp⟩ := MinorDensityKT0.exact_minor_density ((h - 2 : ℕ) : ℚ) hpos
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  have hd : MinorDensity.Bound G (((h - 2 : ℕ) : ℚ) : ℝ) := by
    simpa only [Rat.cast_natCast] using minor_density G h hlo hhi hG
  have hresult := hp G hd ports C
  have hcoef : 2 * (((h - 2 : ℕ) : ℚ) : ℝ) + 1 = 2 * (h : ℝ) - 3 := by
    rw [Rat.cast_natCast, Nat.cast_sub (show 2 ≤ h by omega)]
    norm_num
    ring
  simpa only [hcoef] using hresult

end Paper.ExcludedCliqueDensity
