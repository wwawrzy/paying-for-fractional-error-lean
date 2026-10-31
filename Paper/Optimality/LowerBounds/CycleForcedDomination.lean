import Paper.Endpoints.Rounding.WeightedBudget
import Paper.Preliminaries.PathPowerDomination
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Domination forced by selected cycle segments

The boundary is the actual neighborhood outside the forced selected set.
Only its later estimate by two vertices per selected segment is left to
the ordered cycle-segment geometry. No desired domination count is assumed.
-/
namespace Paper.CycleForcedDomination

open SimpleGraph SevenFoundation
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem covered_card_le (hclosed : ∀ v, (closed G v).card ≤ 3) (S : Finset V) :
    (covered G S).card ≤ 3 * S.card := by
  calc
    _ ≤ ∑ v ∈ S, (closed G v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, (3 : ℕ) := Finset.sum_le_sum (fun v _ => hclosed v)
    _ = _ := by simp [Nat.mul_comm]

/-- Vertices outside the closed forced neighborhood must be dominated by
the other selected vertices. The exact outside boundary is charged once. -/
theorem forced_count (hclosed : ∀ v, (closed G v).card ≤ 3)
    (D F : Finset V) (hD : dominates G D) (hF : F ⊆ D) :
    Fintype.card V + 2 * F.card ≤ 3 * D.card + (covered G F \ F).card := by
  have hall : (Finset.univ : Finset V) ⊆ covered G F ∪ covered G (D \ F) := by
    intro v _
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (hD v)
    by_cases huF : u ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨u, huF, hvu⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, huF⟩, hvu⟩)
  have hcover : Fintype.card V ≤ (covered G F).card + 3 * (D \ F).card := by
    calc
      _ = (Finset.univ : Finset V).card := Finset.card_univ.symm
      _ ≤ (covered G F ∪ covered G (D \ F)).card := Finset.card_le_card hall
      _ ≤ (covered G F).card + (covered G (D \ F)).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (covered_card_le G hclosed (D \ F)) _
  have hb := Finset.card_sdiff_add_card_eq_card (subset_covered G F)
  have hd := Finset.card_sdiff_add_card_eq_card hF
  omega

theorem cycle_closed_card (n : ℕ) (v : Fin (n + 3)) :
    (closed (cycleGraph (n + 3)) v).card = 3 := by
  rw [WeightedBudget.closed_card, cycleGraph_degree_three_le]

theorem cycle_forced_count (n : ℕ) (D F : Finset (Fin (n + 3)))
    (hD : dominates (cycleGraph (n + 3)) D) (hF : F ⊆ D) :
    n + 3 + 2 * F.card ≤ 3 * D.card + (covered (cycleGraph (n + 3)) F \ F).card := by
  simpa only [Fintype.card_fin] using forced_count (cycleGraph (n + 3))
    (fun v => (cycle_closed_card n v).le) D F hD hF

/-- The already proved path cover also dominates the cycle; it gives the
ceil(N/3) comparison used in the quantitative contradiction. -/
theorem cycle_dominationNumber_upper (n : ℕ) :
    (cycleGraph n).dominationNumber ≤ n ⌈/⌉ 3 := by
  have hpath : PathPowerTreewidth.graph n 1 ≤ pathGraph n := by
    intro u v huv
    rw [pathGraph_adj]
    have hne : u.val ≠ v.val := fun h => huv.1 (Fin.ext h)
    have hh := huv.2
    omega
  have hcycle : PathPowerTreewidth.graph n 1 ≤ cycleGraph n := hpath.trans pathGraph_le_cycleGraph
  have hdom := PathPowerDomination.code_dominates n 1
  have hs : (cycleGraph n).IsDominatingSetFinset (PathPowerDomination.code n 1) := by
    intro v
    obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp (hdom v)
    rcases (mem_closed _ _ _).mp hvw with he | ha
    · exact Or.inl (he ▸ hw)
    · exact Or.inr ⟨w, hw, (hcycle ha).symm⟩
  exact hs.dominationNumber_le.trans (by simpa using PathPowerDomination.code_card n 1)

theorem cycle_dominationNumber_real_upper (n : ℕ) :
    ((cycleGraph n).dominationNumber : ℝ) ≤ ((n : ℝ) + 2) / 3 := by
  have hc : 3 * (n ⌈/⌉ 3) ≤ n + 2 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hn := (Nat.mul_le_mul_left 3 (cycle_dominationNumber_upper n)).trans hc
  have hr : 3 * ((cycleGraph n).dominationNumber : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast hn
  linarith

/-- The genuine forced-region geometry suffices to reproduce the paper's
5N/12 bound whenever bad segments occupy at least half the cycle. -/
theorem packed_forced_count (n T s : ℕ) (hT : 1 ≤ T)
    (D F : Finset (Fin (n + 3))) (hD : dominates (cycleGraph (n + 3)) D) (hFD : F ⊆ D)
    (hFcard : F.card = 2 * T * s)
    (hboundary : (covered (cycleGraph (n + 3)) F \ F).card ≤ 2 * s)
    (hhalf : n + 3 ≤ 8 * T * s) :
    5 * (n + 3) ≤ 12 * D.card := by
  have hc := cycle_forced_count n D F hD hFD
  rw [hFcard] at hc
  have hTs := Nat.mul_le_mul_right s hT
  simp only [Nat.one_mul] at hTs
  nlinarith only [hc, hboundary, hhalf, hTs]

/-- The explicit large-N threshold makes 5N/12 strictly exceed every
(1+epsilon)-approximation with epsilon below one quarter. -/
theorem approximation_contradiction (N d γ : ℕ) (ε : ℝ) (hε : 0 < ε) (hquarter : ε < 1 / 4)
    (hlarge : 8 * (1 + ε) / (1 - 4 * ε) < N)
    (hd : 5 * N ≤ 12 * d) (hγ : (γ : ℝ) ≤ ((N : ℝ) + 2) / 3) :
    (1 + ε) * γ < d := by
  have hp : (0 : ℝ) < 1 - 4 * ε := by linarith
  have hN := (div_lt_iff₀ hp).mp hlarge
  have hdR : 5 * (N : ℝ) ≤ 12 * (d : ℝ) := by exact_mod_cast hd
  have hγR := mul_le_mul_of_nonneg_left hγ (show (0 : ℝ) ≤ 1 + ε by linarith)
  nlinarith only [hN, hdR, hγR]

theorem packed_not_approximate (n T s : ℕ) (hT : 1 ≤ T)
    (D F : Finset (Fin (n + 3))) (hD : dominates (cycleGraph (n + 3)) D) (hFD : F ⊆ D)
    (hFcard : F.card = 2 * T * s)
    (hboundary : (covered (cycleGraph (n + 3)) F \ F).card ≤ 2 * s)
    (hhalf : n + 3 ≤ 8 * T * s) (ε : ℝ) (hε : 0 < ε) (hquarter : ε < 1 / 4)
    (hlarge : 8 * (1 + ε) / (1 - 4 * ε) < (n + 3 : ℕ)) :
    (1 + ε) * (cycleGraph (n + 3)).dominationNumber < (D.card : ℝ) :=
  approximation_contradiction (n + 3) D.card (cycleGraph (n + 3)).dominationNumber ε hε hquarter
    hlarge (packed_forced_count n T s hT D F hD hFD hFcard hboundary hhalf)
    (cycle_dominationNumber_real_upper (n + 3))

end Paper.CycleForcedDomination

#print axioms Paper.CycleForcedDomination.forced_count
#print axioms Paper.CycleForcedDomination.cycle_forced_count
#print axioms Paper.CycleForcedDomination.cycle_dominationNumber_upper
#print axioms Paper.CycleForcedDomination.cycle_dominationNumber_real_upper
#print axioms Paper.CycleForcedDomination.packed_forced_count
#print axioms Paper.CycleForcedDomination.approximation_contradiction
#print axioms Paper.CycleForcedDomination.packed_not_approximate
