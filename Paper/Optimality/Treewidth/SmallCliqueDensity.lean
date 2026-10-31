import GraphTheory.SimpleGraph.Minor.Density
import Paper.Preliminaries.MinorDensity
import Paper.Endpoints.Rounding.MinorDensityKT0

/-! Sharp density for the first two excluded-clique classes, recovered from
the proved average-degree minor theorem, rather than its looser wrapper. -/
namespace Paper.SmallCliqueDensity

open SimpleGraph SevenFoundation BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edge_bound (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 4) (hG : G.IsKMinorFree h) :
    G.edgeFinset.card ≤ (h - 2) * Fintype.card V := by
  by_cases hV : 0 < Fintype.card V
  · have hd := IsKMinorFree.two_mul_edges_lt G h (by omega) hV hG
    interval_cases h <;> norm_num at hd ⊢ <;> omega
  · have hc : Fintype.card V = 0 := by omega
    have hd := hG.edgeFinset_card_le G
    rw [hc, Nat.mul_zero] at hd
    omega

theorem minor_density (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 4) (hG : G.IsKMinorFree h) :
    MinorDensity.Bound G ((h - 2 : ℕ) : ℝ) := by
  intro A _ _ J _ hm
  have hJ : J.IsKMinorFree h := IsHMinorFree.minor hG hm
  exact_mod_cast edge_bound J h hlo hhi hJ

theorem exact_KT0 (h : ℕ) (hlo : 3 ≤ h) (hhi : h ≤ 4) :
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

end Paper.SmallCliqueDensity

#print axioms Paper.SmallCliqueDensity.edge_bound
#print axioms Paper.SmallCliqueDensity.minor_density
#print axioms Paper.SmallCliqueDensity.exact_KT0
