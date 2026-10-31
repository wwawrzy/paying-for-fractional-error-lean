import Paper.Solver.LocalSearch.GeneralCoveringInitializedRandomFractional
import Paper.Solver.LocalSearch.GeneralCoveringFractionalErrorBudget
import Paper.Solver.LocalSearch.GeneralCoveringRandomBoundaryBound

/-! Analysis of the UNCHANGED actual initialized random fractional runtime.
One SAME public-V beta source is used for execution, charged partitions and
all finite means. Public witnesses precede graph/private input. Expected
boundary and pointwise cost contracts are DERIVED,never oracle inputs.
No distributed deterministic averaging/final denominator or full A claim. -/
namespace Paper.GeneralCoveringInitializedRandomFractionalExpectation
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Coins := GeneralCoveringTaskRandomPhysicalMarks.Coins

def zeroCoins (V : Type) (Δ k b n : ℕ) : V → Coins Δ k b n := fun _ _ _ => false

def state {B Δ k b n : ℕ} (input : V → GeneralCoveringInitializerRun.Input V)
    (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) : V → GeneralCoveringInitializedRandomFractional.Input V B Δ k b n :=
  fun v => (input v, (c v, β v))

/-- Only instantiate received public numeric parameters; no new program body. -/
noncomputable def runtime {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B) :=
  GeneralCoveringInitializedRandomFractional.program ids
    (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
    (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
    p.L p.Δ p.A B k p.q t b n hB

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def centers {bits : ℕ} (ids : BitCode V bits) (a : ℝ)
    (input : V → GeneralCoveringInitializerRun.Input V) := GeneralCoveringFractionalErrorBudget.centers G ids a input

/-- Original interpretation at zero coins carries NO output property. Its
private C/R facts extend to every beta because only saved coins change. -/
noncomputable def atCoins {B Δ k b n : ℕ} (input : V → GeneralCoveringInitializerRun.Input V)
    (c : V → Fin (B + 1))
    (d : GeneralCoveringInitializedRandomFractional.Original G (state input c (zeroCoins V Δ k b n)))
    (β : V → Coins Δ k b n) : GeneralCoveringInitializedRandomFractional.Original G (state input c β) where
  cover := d.cover
  targets := d.targets
  R := d.R
  incidence := d.incidence
  local_rows := d.local_rows
  rows := d.rows
  residual := d.residual
  candidates := d.candidates
  inverse := d.inverse

noncomputable def run {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β : V → Coins p.Δ k b n) :=
  (runtime ids p t k b n hB).runEncoded G (state input c β)

noncomputable def solution {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β : V → Coins p.Δ k b n) (v : V) : ℝ :=
  ((run G ids p t k b n hB input c β v).1.1.1 : ℝ) / p.q

noncomputable def cost {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β : V → Coins p.Δ k b n) : ℝ :=
  CoveringOptimum.objective (fun v => ((c v).val : ℝ)) (solution G ids p t k b n hB input c β)

/-- Mathematical finite mean,not an executable averaging operation. -/
noncomputable def expectedCost {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) : ℝ :=
  (∑ β : V → Coins p.Δ k b n, cost G ids p t k b n hB input c β) / Fintype.card (V → Coins p.Δ k b n)

theorem source_card_pos (Δ k b n : ℕ) : 0 < Fintype.card (V → Coins Δ k b n) :=
  Fintype.card_pos_iff.mpr ⟨zeroCoins V Δ k b n⟩

theorem source_card_empty [IsEmpty V] (Δ k b n : ℕ) : Fintype.card (V → Coins Δ k b n) = 1 := by
  letI : Unique (V → Coins Δ k b n) := {
    default := zeroCoins V Δ k b n
    uniq := fun _ => funext (fun v => isEmptyElim v) }
  exact Fintype.card_unique

theorem centers_eq {bits : ℕ} (ids : BitCode V bits) (a : ℝ) {B Δ k b n : ℕ}
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β : V → Coins Δ k b n) :
    GeneralCoveringInitializedRandomFractional.centers G ids
      (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
      (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
      (state input c β) = centers G ids a input := by
  delta GeneralCoveringInitializedRandomFractional.centers centers GeneralCoveringFractionalErrorBudget.centers state
  rfl

theorem centers_independent {bits : ℕ} (ids : BitCode V bits) (a : ℝ) {B Δ k b n : ℕ}
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β γ : V → Coins Δ k b n) :
    GeneralCoveringInitializedRandomFractional.centers G ids
      (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
      (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a) (state input c β) =
    GeneralCoveringInitializedRandomFractional.centers G ids
      (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
      (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a) (state input c γ) :=
  (centers_eq G ids a input c β).trans (centers_eq G ids a input c γ).symm

noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- SAME charged partition and beta,identified at cardinality without
changing the dependent Low type or its equality/graph instances. -/
theorem boundary_card {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hk : 0 < k)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1))
    (d : GeneralCoveringInitializedRandomFractional.Original G (state input c (zeroCoins V p.Δ k b n)))
    (β : V → Coins p.Δ k b n) :
    (GeneralCoveringInitializedRandomFractional.boundary G ids
      (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
      (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
      p.L p.Δ k hk t (atCoins G input c d β)).card =
    (GeneralCoveringRandomBoundaryBound.boundary G d.cover (centers G ids a input) d.R p.L p.Δ k hk t b n β).card := by
  delta GeneralCoveringInitializedRandomFractional.boundary GeneralCoveringRandomFractionalPhysical.boundary
    GeneralCoveringRandomBoundaryBound.boundary GeneralCoveringInitializedRandomFractional.centers
    centers GeneralCoveringFractionalErrorBudget.centers state atCoins
  rfl

/-- Received actual uniform initializer bounds,including genuine covering
and admissibility. No center/cardinality benchmark is supplied. -/
theorem center_bound {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (t k b n : ℕ) (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1))
    (d : GeneralCoveringInitializedRandomFractional.Original G (state input c (zeroCoins V p.Δ k b n)))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (c v).val) :
    GeneralCoveringInitializerPass.Covers d.cover d.R (centers G ids a input) ∧
    centers G ids a input ⊆ CoveringSupport.admissible d.cover d.R ∧
    ((centers G ids a input).card : ℝ) ≤ GeneralCoveringFractionalErrorBudget.K a *
      GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) ∧
    (∑ v ∈ centers G ids a input, ((c v).val : ℝ)) ≤ (B : ℝ) * GeneralCoveringFractionalErrorBudget.K a *
      GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) := by
  have hb := (GeneralCoveringInitializerFractional.uniform_parameters a ha).2.2.1
  have hi := GeneralCoveringInitializedRandomFractional.initializer_spec G ids
    (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
    (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a) hb d
  have hu := GeneralCoveringInitializedRandomFractional.uniform_bounds G ids ha hden d hc
  simpa only [GeneralCoveringInitializedRandomFractional.centers, centers, GeneralCoveringFractionalErrorBudget.centers,
    GeneralCoveringFractionalErrorBudget.K, state] using And.intro hi.1 (And.intro hi.2 hu)

/-- Every actual initialized outcome,for arbitrary public-V beta. -/
theorem pointwise {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (hB : 1 ≤ B) (t k b n : ℕ) (ht : 0 < t) (hk : 0 < k)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1))
    (d : GeneralCoveringInitializedRandomFractional.Original G (state input c (zeroCoins V p.Δ k b n)))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (c v).val) (β : V → Coins p.Δ k b n) :
    SevenFoundation.feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover c) (solution G ids p t k b n hB input c β) ∧
    (∀ v, v ∉ CoveringSupport.admissible d.cover d.R → (run G ids p t k b n hB input c β v).1.1.1 = 0) ∧
    cost G ids p t k b n hB input c β ≤
      (1 + p.xi) * GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover (centers G ids a input) d.R p.L).card +
      2 * (B : ℝ) * (((GeneralCoveringOwnerVirtualPrepare.high G d.cover (centers G ids a input) d.R p.L p.Δ).card : ℝ) +
        (GeneralCoveringRandomBoundaryBound.boundary G d.cover (centers G ids a input) d.R p.L p.Δ k hk t b n β).card) ∧
    (∀ v, (run G ids p t k b n hB input c β v).1.1.1 ≤ GeneralCoveringFractionalErrorBudget.outputBound p k) ∧
    (∀ v, (p.q : ℝ) * solution G ids p t k b n hB input c β v = (run G ids p t k b n hB input c β v).1.1.1) := by
  have hb := (GeneralCoveringInitializerFractional.uniform_parameters a ha).2.2.1
  have hd := GeneralCoveringFractionalErrorBudget.solver_density G p hden
  have hs := GeneralCoveringInitializedRandomFractional.spec G ids
    (ib := GeneralCoveringInitializerFractional.listBound a) (ih := GeneralCoveringInitializerFractional.candidateThreshold a)
    (ifreq := GeneralCoveringInitializerFractional.listThreshold a) (it := GeneralCoveringInitializerFractional.scale a)
    (L := p.L) (a := p.A) hB hb hk ht p.q_pos (state input c β) (atCoins G input c d β)
    p.density_pos hd p.xi p.accuracy hc
  have hsupport := GeneralCoveringInitializedRandomFractional.support G ids
    (ib := GeneralCoveringInitializerFractional.listBound a) (ih := GeneralCoveringInitializerFractional.candidateThreshold a)
    (ifreq := GeneralCoveringInitializerFractional.listThreshold a) (it := GeneralCoveringInitializerFractional.scale a)
    (L := p.L) (a := p.A) hB hb hk ht p.q_pos (state input c β) (atCoins G input c d β)
    p.density_pos hd p.xi p.accuracy hc
  have hout := And.intro hs.1 (And.intro hsupport (And.intro hs.2.1 (And.intro hs.2.2.1 hs.2.2.2.1)))
  simpa only [run, solution, cost, runtime, state, atCoins, centers, GeneralCoveringFractionalErrorBudget.centers,
    GeneralCoveringInitializedRandomFractional.centers, GeneralCoveringInitializedRandomFractional.boundary,
    GeneralCoveringRandomFractionalPhysical.boundary, GeneralCoveringRandomBoundaryBound.boundary,
    GeneralCoveringFractionalErrorBudget.outputBound] using hout

theorem cost_nonneg {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) (β : V → Coins p.Δ k b n) :
    0 ≤ cost G ids p t k b n hB input c β := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem expectedCost_nonneg {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) :
    0 ≤ expectedCost G ids p t k b n hB input c :=
  div_nonneg (Finset.sum_nonneg (fun β _ => cost_nonneg G ids p t k b n hB input c β)) (Nat.cast_nonneg _)

theorem expectedCost_empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1)) :
    expectedCost G ids p t k b n hB input c = 0 := by
  simp only [expectedCost, cost, CoveringOptimum.objective, Finset.univ_eq_empty, Finset.sum_empty,
    Finset.sum_const_zero, zero_div]

/-- Numeric/source witnesses chosen BEFORE every graph and original input.
The public beta law,actual partition,and runtime are identical in all terms. -/
theorem parameters (a : ℝ) (ha : 1 ≤ a) (B : ℕ) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters a B ε, ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G a → ∀ {bits : ℕ} (ids : BitCode V bits)
        (input : V → GeneralCoveringInitializerRun.Input V) (c : V → Fin (B + 1))
        (d : GeneralCoveringInitializedRandomFractional.Original G (state input c (zeroCoins V p.Δ k b n))),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (c v).val) →
        ((centers G ids a input).card : ℝ) ≤ GeneralCoveringFractionalErrorBudget.K a *
          GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) ∧
        (∀ β : V → Coins p.Δ k b n,
          SevenFoundation.feasible (GeneralCoveringFractionalCorrect.coverInstance d.R d.cover c) (solution G ids p t k b n hB input c β) ∧
          (∀ v, v ∉ CoveringSupport.admissible d.cover d.R → (run G ids p t k b n hB input c β v).1.1.1 = 0) ∧
          (∀ v, (run G ids p t k b n hB input c β v).1.1.1 ≤ GeneralCoveringFractionalErrorBudget.outputBound p k) ∧
          (∀ v, (p.q : ℝ) * solution G ids p t k b n hB input c β v = (run G ids p t k b n hB input c β v).1.1.1)) ∧
        expectedCost G ids p t k b n hB input c ≤ (1 + ε) *
          GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) ∧
        (GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ)) = 0 →
          expectedCost G ids p t k b n hB input c = 0) ∧
        (d.R = ∅ → (∀ β v, (run G ids p t k b n hB input c β v).1.1.1 = 0) ∧ expectedCost G ids p t k b n hB input c = 0) := by
  obtain ⟨p⟩ := GeneralCoveringFractionalErrorBudget.parameters_exists a ha B hB ε hε
  obtain ⟨t, k, b, n, ht, hk, hp⟩ := GeneralCoveringRandomBoundaryBound.parameters a (zero_le_one.trans ha)
    p.L p.L_pos p.Δ p.η p.η_pos
  refine ⟨p, t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hden bits ids input c d hc
  let D := centers G ids a input
  let Ω := V → Coins p.Δ k b n
  -- Equality only for the finite PUBLIC source,never for vertices or Low.
  letI : DecidableEq Ω := Classical.decEq Ω
  let parts := fun β : Ω => GeneralCoveringTaskRandomPhysicalMarks.partition G d.cover D d.R p.L hk t β
  let τ := GeneralCoveringNormalizedFractional.supportedNumber d.cover d.R (fun v => ((c v).val : ℝ))
  have hb := (hp G hden d.cover D d.R d.local_rows ids).2.2.2
  have hmean : GeneralCoveringFractionalErrorBudget.mean (Finset.univ : Finset Ω)
      (fun β => ((GeneralCoveringFractionalErrorBudget.boundary G d.cover D d.R p.L p.Δ k (parts β)).card : ℝ)) ≤
      2 * p.η * (D.card : ℝ) := by
    simpa only [GeneralCoveringFractionalErrorBudget.mean, Finset.card_univ, GeneralCoveringFractionalErrorBudget.boundary,
      GeneralCoveringRandomBoundaryBound.meanBoundary, GeneralCoveringRandomBoundaryBound.boundary, parts] using hb
  have hrepair : ∀ β ∈ (Finset.univ : Finset Ω), cost G ids p t k b n hB input c β ≤
      (1 + p.xi) * τ + (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover D d.R p.L).card +
      2 * (B : ℝ) * (((GeneralCoveringOwnerVirtualPrepare.high G d.cover D d.R p.L p.Δ).card : ℝ) +
        (GeneralCoveringFractionalErrorBudget.boundary G d.cover D d.R p.L p.Δ k (parts β)).card) := by
    intro β _
    have hb := (pointwise G ids p ha hden hB t k b n ht hk input c d hc β).2.2.1
    simpa only [GeneralCoveringFractionalErrorBudget.boundary, GeneralCoveringRandomBoundaryBound.boundary, parts] using hb
  have hm := GeneralCoveringFractionalErrorBudget.finite_mean G ids d.cover d.targets ha hden B p d.R d.local_rows d.rows
    d.incidence c hc input d.residual d.candidates d.inverse (Finset.univ : Finset Ω)
    (Finset.univ_nonempty_iff.mpr ⟨zeroCoins V p.Δ k b n⟩) k parts (fun β => cost G ids p t k b n hB input c β) hmean hrepair
  have hcost : expectedCost G ids p t k b n hB input c ≤ (1 + ε) * τ := by
    simpa only [expectedCost, GeneralCoveringFractionalErrorBudget.mean, Finset.card_univ] using hm
  have hz (he : τ = 0) : expectedCost G ids p t k b n hB input c = 0 :=
    le_antisymm (by simpa only [he, mul_zero] using hcost) (expectedCost_nonneg G ids p t k b n hB input c)
  have hinit := center_bound G ids p ha hden t k b n input c d hc
  refine ⟨hinit.2.2.1, ?_, hcost, hz, ?_⟩
  · intro β
    have hs := pointwise G ids p ha hden hB t k b n ht hk input c d hc β
    exact ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
  · intro he
    constructor
    · intro β v
      exact (pointwise G ids p ha hden hB t k b n ht hk input c d hc β).2.1 v (by simp [he, CoveringSupport.admissible])
    · apply hz
      dsimp only [τ]
      rw [he]
      exact GeneralCoveringNormalizedFractional.supportedNumber_empty d.cover _

/-- Inherited resources for the SAME received runtime. No mean is executed. -/
theorem runtime_resources {bits : ℕ} (ids : BitCode V bits) {a ε : ℝ} {B : ℕ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a B ε) (t k b n : ℕ) (hB : 1 ≤ B)
    (c : ℕ) (hids : bits ≤ c * Nat.clog 2 (Fintype.card V + 2)) :
    (runtime ids p t k b n hB).rounds =
      RecursiveSearch.roundBound (4 * k) p.A (GeneralCoveringTaskFractionalSolve.numeratorBound p.A B k p.q) +
        4 * (n * (3 * k + 1) + 1) + GeneralCoveringInitializerFractional.scale a *
          (5 + 2 * GeneralCoveringInitializerFractional.listThreshold a) + 18 ∧
    (runtime ids p t k b n hB).maxBits ≤ GeneralCoveringInitializedRandomFractional.bitCoefficient
      (GeneralCoveringInitializerFractional.listThreshold a) p.L p.Δ p.A B k p.q b n c * Nat.clog 2 (Fintype.card V + 2) := by
  exact ⟨GeneralCoveringInitializedRandomFractional.rounds ids
    (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
    (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
    p.L p.Δ p.A B k p.q t b n hB,
    GeneralCoveringInitializedRandomFractional.logarithmic_bits ids
      (GeneralCoveringInitializerFractional.listBound a) (GeneralCoveringInitializerFractional.candidateThreshold a)
      (GeneralCoveringInitializerFractional.listThreshold a) (GeneralCoveringInitializerFractional.scale a)
      p.L p.Δ p.A B k p.q t b n hB c hids⟩

end Paper.GeneralCoveringInitializedRandomFractionalExpectation

#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.source_card_pos
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.source_card_empty
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.centers_eq
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.centers_independent
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.atCoins
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.boundary_card
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.center_bound
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.pointwise
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.cost_nonneg
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.expectedCost_nonneg
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.expectedCost_empty_physical
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.parameters
#print axioms Paper.GeneralCoveringInitializedRandomFractionalExpectation.runtime_resources
