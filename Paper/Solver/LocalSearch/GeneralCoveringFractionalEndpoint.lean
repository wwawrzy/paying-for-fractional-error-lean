import Paper.Solver.LocalSearch.GeneralCoveringInitializedFrameAverage
import Paper.Solver.LocalSearch.GeneralCoveringFrameAverageResources
import Paper.Averaging.Tasks.FiniteAverage

/-! Graph-uniform arbitrary-covering fractional endpoint. Every coordinate is
the own bounded natural numerator of an actual deterministic program over
one positive public denominator. The original supported LP, original input,
and public parameter order are preserved through exact finite averaging. -/
namespace Paper.GeneralCoveringFractionalEndpoint
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringInitializedFrameAverage.Input V B

noncomputable def runtime {ids : ℕ} (I : BitCode V ids) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B) :=
  GeneralCoveringInitializedFrameAverage.program I
    (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
    (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
    p.L p.Δ p.A B k t b n p.q hB

variable [Fintype V]

private theorem mean_feasible {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (I : CoverInstance V) (y : Ω → V → ℝ) (hy : ∀ ω, feasible I (y ω)) :
    feasible I (FiniteAverage.vector y) := by
  refine ⟨FiniteAverage.nonneg y (fun ω v => (hy ω).1 v), ?_, ?_⟩
  · intro v hv
    have hz : ∑ ω, y ω v = 0 := Finset.sum_eq_zero (fun ω _ => (hy ω).2.1 v hv)
    exact (congrArg (fun z : ℝ => z / Fintype.card Ω) hz).trans (zero_div _)
  · intro r hr
    rw [FiniteAverage.sum_eq]
    apply (le_div_iff₀ (FiniteAverage.card_pos (Ω := Ω))).mpr
    have hs := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => (hy ω).2.2 r hr)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul] using hs

private theorem mean_cost {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (I : CoverInstance V) (y : Ω → V → ℝ) :
    cost I (FiniteAverage.vector y) = (∑ ω, cost I (y ω)) / Fintype.card Ω := by
  unfold cost FiniteAverage.vector
  simp only [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
  rw [Finset.sum_comm]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def solution {ids : ℕ} (I : BitCode V ids) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) : ℝ :=
  (((runtime I p t k b n hB).runEncoded G s v).1.val : ℝ) /
    GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q

/-- Positive public denominator, independent of graph and original input. -/
theorem denominator_pos {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (k b n : ℕ) :
    0 < GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q :=
  GeneralCoveringOwnerFrameAverage.denominator_pos p.L p.Δ k b n p.q (by have := p.q_pos; omega)

theorem numerator_bounded {ids : ℕ} (I : BitCode V ids) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((runtime I p t k b n hB).runEncoded G s v).1.val ≤
      GeneralCoveringOwnerFrameAverage.numeratorBound p.L p.Δ p.A B k b n p.q :=
  Nat.le_of_lt_succ (Fin.isLt _)

theorem rounds {ids : ℕ} (I : BitCode V ids) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B) :
    (runtime I p t k b n hB).rounds =
      GeneralCoveringInitializerFractional.scale a * (5 + 2 * GeneralCoveringInitializerFractional.listThreshold a) +
        18 + 4 * GeneralCoveringOwnerFrameTaskInputs.outerRadius k n +
        RecursiveSearch.roundBound (4 * k) p.A (GeneralCoveringTaskFractionalSolve.numeratorBound p.A B k p.q) :=
  GeneralCoveringFrameAverageResources.rounds I
    (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
    (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
    p.L p.Δ p.A B k t b n p.q hB

theorem logarithmic_bits {ids : ℕ} (I : BitCode V ids) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (N c : ℕ) (hids : ids ≤ c * Nat.clog 2 (N + 2)) :
    (runtime I p t k b n hB).maxBits ≤
      GeneralCoveringFrameAverageResources.coefficient (GeneralCoveringInitializerFractional.listThreshold a)
        p.L p.Δ p.A B k b n p.q c * Nat.clog 2 (N + 2) :=
  GeneralCoveringFrameAverageResources.logarithmic_bits I
    (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
    (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
    p.L p.Δ p.A B k t b n p.q hB N c hids

set_option maxHeartbeats 1000000 in
/-- Public numeric choices precede every graph, ID codec and original private
input. The cost guarantee concerns the original supported fractional LP. -/
theorem parameters (a : ℝ) (ha : 1 ≤ a) (B : ℕ) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters a B ε, ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G a → ∀ {ids : ℕ} (I : BitCode V ids) (s : V → Input V B)
        (d : GeneralCoveringInitializedFrameAverage.Original G s),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (s v).2.val) →
        let K := GeneralCoveringFractionalCorrect.coverInstance d.R d.cover (fun v => (s v).2)
        let x := solution G I p t k b n hB s
        feasible K x ∧ cost K x ≤ (1 + ε) *
          GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((s v).2.val : ℝ)) ∧
          approximates K (1 + ε) x := by
  obtain ⟨p, t, k, b, n, ht, hk, hp⟩ :=
    GeneralCoveringInitializedRandomFractionalExpectation.parameters a ha B hB ε hε
  refine ⟨p, t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hden ids I s d hc
  let input := fun v => (s v).1
  let c := fun v => (s v).2
  let β₀ := GeneralCoveringInitializedRandomFractionalExpectation.zeroCoins V p.Δ k b n
  let d₀ := GeneralCoveringInitializedFrameAverage.randomOriginal G d β₀
  have hs := hp G hden I input c d₀ hc
  let K := GeneralCoveringFractionalCorrect.coverInstance d.R d.cover c
  let y := fun β : V → ActiveFiniteBitPartition.Bits p.Δ k b n =>
    GeneralCoveringInitializedRandomFractionalExpectation.solution G I p t k b n hB input c β
  have hstate (β : V → ActiveFiniteBitPartition.Bits p.Δ k b n) :
      GeneralCoveringInitializedRandomFractionalExpectation.state input c β =
        GeneralCoveringInitializedFrameAverage.state s β := rfl
  have hx : solution G I p t k b n hB s = FiniteAverage.vector y := by
    funext v
    have hm := GeneralCoveringInitializedFrameAverage.mean G I
      (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
      (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
      p.L p.Δ p.A k hk t ht b n p.q (by have := p.q_pos; omega) hB s d v
    dsimp only [solution, runtime, FiniteAverage.vector, y,
      GeneralCoveringInitializedRandomFractionalExpectation.solution,
      GeneralCoveringInitializedRandomFractionalExpectation.run,
      GeneralCoveringInitializedRandomFractionalExpectation.runtime]
    simp only [hstate]
    exact hm
  have hf : feasible K (FiniteAverage.vector y) := mean_feasible K y (fun β => (hs.2.1 β).1)
  have he : cost K (FiniteAverage.vector y) =
      GeneralCoveringInitializedRandomFractionalExpectation.expectedCost G I p t k b n hB input c :=
    mean_cost K y
  have hb : cost K (FiniteAverage.vector y) ≤ (1 + ε) *
      GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) :=
    he.trans_le hs.2.2.1
  dsimp only
  rw [hx]
  refine ⟨hf, hb, hf, ?_⟩
  intro z hz
  have hmin := GeneralCoveringNormalizedFractional.budget_bound d.cover d.R c d.rows z hz
    (cost K z) le_rfl
  exact hb.trans (mul_le_mul_of_nonneg_left hmin (by linarith))

end Paper.GeneralCoveringFractionalEndpoint

#print axioms Paper.GeneralCoveringFractionalEndpoint.denominator_pos
#print axioms Paper.GeneralCoveringFractionalEndpoint.numerator_bounded
#print axioms Paper.GeneralCoveringFractionalEndpoint.rounds
#print axioms Paper.GeneralCoveringFractionalEndpoint.logarithmic_bits
#print axioms Paper.GeneralCoveringFractionalEndpoint.parameters
