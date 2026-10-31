import Paper.Solver.LocalSearch.GeneralCoveringInitializerSupported
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalRepair
import Paper.Solver.LocalSearch.LocalSolverMath

/-! Graph-uniform epsilon allocation for the ORIGINAL supported covering LP.
The real initializer coefficient K(a) is retained exactly. Numeric choices
precede the graph; actual D comes from the unchanged encoded initializer.
Finite-mean composition has explicit SAME-boundary mean and pointwise Repair
cost premises. No random producer,averaging program or final endpoint is
constructed or assumed here. No division by tau,optimizer or center oracle. -/
namespace Paper.GeneralCoveringFractionalErrorBudget
open BroadcastModel SevenFoundation
open scoped BigOperators

noncomputable def K (a : ℝ) : ℝ := GeneralCoveringInitializerFractional.uniformCoefficient a

theorem K_pos (a : ℝ) (ha : 1 ≤ a) : 0 < K a :=
  GeneralCoveringInitializerSupported.uniformCoefficient_pos a ha

/-- A positive public natural divisor; no graph/outcome is part of the choice. -/
theorem public_cutoff (c base ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 1 ≤ n ∧ base ≤ (n : ℝ) ∧ c / n ≤ ε / 4 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max 1 base) (4 * c / ε))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt ((le_max_left 1 base).trans (le_max_left _ _)) hn
  have hnN : 1 ≤ n := by exact_mod_cast (le_of_lt hn1)
  have hn0 : (0 : ℝ) < n := by linarith
  have hb : base ≤ (n : ℝ) := (le_max_right 1 base).trans ((le_max_left _ _).trans (le_of_lt hn))
  have hc : 4 * c ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp ((le_max_right _ _).trans (le_of_lt hn))
  refine ⟨n, hnN, hb, (div_le_iff₀ hn0).mpr ?_⟩
  nlinarith

/-- Only public numeric choices/proofs,with REAL K(a),never a graph certificate. -/
structure Parameters (a : ℝ) (B : ℕ) (ε : ℝ) where
  A : ℕ
  density_pos : 1 ≤ A
  density_bound : a ≤ (A : ℝ)
  xi : ℝ
  xi_pos : 0 < xi
  solver_share : xi ≤ ε / 4
  q : ℕ
  q_pos : 1 ≤ q
  accuracy : 2 * (A : ℝ) / q ≤ xi
  L : ℕ
  L_pos : 1 ≤ L
  L_density : 4 * a ≤ (L : ℝ)
  Δ : ℕ
  Δ_pos : 0 < Δ
  η : ℝ
  η_pos : 0 < η
  heavy_share : (B : ℝ) * (2 * a) * K a / L ≤ ε / 4
  high_share : (2 * (B : ℝ)) * (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4) * K a / Δ ≤ ε / 4
  boundary_share : (2 * (B : ℝ)) * (2 * η) * K a ≤ ε / 4

/-- Four epsilon/4 budgets fixed BEFORE any graph or original private input. -/
theorem parameters_exists (a : ℝ) (ha : 1 ≤ a) (B : ℕ) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (Parameters a B ε) := by
  let A := Nat.ceil a
  have hAa : a ≤ (A : ℝ) := Nat.le_ceil a
  have hA : 1 ≤ A := by exact_mod_cast ha.trans hAa
  let xi := ε / 4
  have hxi : 0 < xi := div_pos hε (by norm_num)
  obtain ⟨L, hL, hLa, hh⟩ := public_cutoff ((B : ℝ) * (2 * a) * K a) (4 * a) ε hε
  obtain ⟨Δ, hΔ, _, hq⟩ := public_cutoff ((2 * (B : ℝ)) * (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4) * K a) 1 ε hε
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hK0 : 0 < K a := K_pos a ha
  let η := ε / (16 * (B : ℝ) * K a)
  have hden : (0 : ℝ) < 16 * (B : ℝ) * K a := by positivity
  have hη : 0 < η := div_pos hε hden
  have he : η * (16 * (B : ℝ) * K a) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  refine ⟨{
    A := A
    density_pos := hA
    density_bound := hAa
    xi := xi
    xi_pos := hxi
    solver_share := le_rfl
    q := LocalSolverMath.denominator A xi
    q_pos := LocalSolverMath.denominator_pos A xi
    accuracy := LocalSolverMath.denominator_accuracy A xi hxi
    L := L
    L_pos := hL
    L_density := hLa
    Δ := Δ
    Δ_pos := (by omega)
    η := η
    η_pos := hη
    heavy_share := hh
    high_share := hq
    boundary_share := ?_ }⟩
  nlinarith [he]

/-- Analysis-only public numeric choice,independent of every future graph. -/
noncomputable def parameters (a : ℝ) (ha : 1 ≤ a) (B : ℕ) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) : Parameters a B ε :=
  Classical.choice (parameters_exists a ha B hB ε hε)

theorem real_accuracy {a ε : ℝ} {B : ℕ} (p : Parameters a B ε) : 2 * a / p.q ≤ p.xi := by
  have hq : (0 : ℝ) ≤ p.q := Nat.cast_nonneg _
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left p.density_bound
    (show (0 : ℝ) ≤ 2 by norm_num)) hq).trans p.accuracy

/-- Resource input for the later SAME-q actual repaired numerator program. -/
def outputBound {a ε : ℝ} {B : ℕ} (p : Parameters a B ε) (k : ℕ) : ℕ :=
  max 1 p.L * GeneralCoveringTaskFractionalSolve.numeratorBound p.A B k p.q + p.q

/-- Count-to-cost conversion uses a public positive divisor,NEVER tau. -/
theorem count_budget {N τ X K w c den ε : ℝ}
    (hτ : 0 ≤ τ) (hw : 0 ≤ w) (hc : 0 ≤ c) (hd : 0 < den)
    (hN : N ≤ K * τ) (hcount : den * X ≤ c * N) (hbudget : w * c * K / den ≤ ε / 4) :
    w * X ≤ (ε / 4) * τ := by
  have hX : X ≤ c * N / den := (le_div_iff₀ hd).mpr (by
    calc
      X * den = den * X := mul_comm _ _
      _ ≤ c * N := hcount)
  calc
    _ ≤ w * (c * N / den) := mul_le_mul_of_nonneg_left hX hw
    _ ≤ w * (c * (K * τ) / den) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN hc) hd.le) hw
    _ = (w * c * K / den) * τ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget hτ

theorem boundary_budget {a ε τ N : ℝ} {B : ℕ} (p : Parameters a B ε)
    (hτ : 0 ≤ τ) (hN : N ≤ K a * τ) :
    2 * (B : ℝ) * (2 * p.η * N) ≤ (ε / 4) * τ := by
  have hw : 0 ≤ (2 * (B : ℝ)) * (2 * p.η) :=
    mul_nonneg (by positivity) (mul_nonneg (by norm_num) p.η_pos.le)
  calc
    _ = ((2 * (B : ℝ)) * (2 * p.η)) * N := by ring
    _ ≤ ((2 * (B : ℝ)) * (2 * p.η)) * (K a * τ) := mul_le_mul_of_nonneg_left hN hw
    _ = ((2 * (B : ℝ)) * (2 * p.η) * K a) * τ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right p.boundary_share hτ

theorem scalar_composition {y τ xi H Q Z B ε : ℝ}
    (hy : y ≤ (1 + xi) * τ + B * H + 2 * B * (Q + Z))
    (hs : xi * τ ≤ (ε / 4) * τ) (hh : B * H ≤ (ε / 4) * τ)
    (hq : 2 * B * Q ≤ (ε / 4) * τ) (hz : 2 * B * Z ≤ (ε / 4) * τ) :
    y ≤ (1 + ε) * τ := by nlinarith

noncomputable def mean {Ω : Type} [DecidableEq Ω] (S : Finset Ω) (f : Ω → ℝ) : ℝ :=
  (∑ ω ∈ S, f ω) / S.card

theorem mean_mono {Ω : Type} [DecidableEq Ω] (S : Finset Ω) (f g : Ω → ℝ)
    (h : ∀ ω ∈ S, f ω ≤ g ω) : mean S f ≤ mean S g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (Nat.cast_nonneg _)

theorem mean_affine {Ω : Type} [DecidableEq Ω] (S : Finset Ω) (hS : S.Nonempty) (A w : ℝ) (b : Ω → ℝ) :
    mean S (fun ω => A + w * b ω) = A + w * mean S b := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hS).ne'
  simp only [mean, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  field_simp [hn] <;> ring

theorem mean_empty {Ω : Type} [DecidableEq Ω] (f : Ω → ℝ) : mean ∅ f = 0 := by simp [mean]

variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact actual encoded initializer,with only its accepted public choices. -/
noncomputable def centers {bits : ℕ} (ids : BitCode V bits) (a : ℝ) (s : V → GeneralCoveringInitializerRun.Input V) : Finset V :=
  GeneralCoveringInitializerSupported.output G ids (GeneralCoveringInitializerFractional.listBound a)
    (GeneralCoveringInitializerFractional.candidateThreshold a) (GeneralCoveringInitializerFractional.listThreshold a)
    (GeneralCoveringInitializerFractional.scale a) s

/-- The natural solver density is certified from the physical bound,not an oracle. -/
theorem solver_density {a ε : ℝ} {B : ℕ} (p : Parameters a B ε) (hden : MinorDensity.Bound G a) :
    MinorDensity.Bound G (p.A : ℝ) := by
  intro W _ _ J _ hm
  exact (hden W J hm).trans (mul_le_mul_of_nonneg_right p.density_bound (Nat.cast_nonneg _))

theorem repair_numeric_bound {a ε : ℝ} {B : ℕ} (p : Parameters a B ε) {bits : ℕ} (ids : BitCode V bits)
    (k : ℕ) (hB : 1 ≤ B) (s : V → GeneralCoveringTaskFractionalRepair.NativeInput V B) (v : V) :
    ((GeneralCoveringTaskFractionalRepair.program ids p.L p.Δ p.A B k p.q hB).runEncoded G s v).1 ≤ outputBound p k :=
  GeneralCoveringTaskFractionalRepair.output_bound G ids p.L p.Δ p.A B k p.q hB s v

/-- All four budgets for the actual encoded initializer. Neither D nor its
cardinality/LP bound is an input oracle. The original C rows are used. -/
theorem initialized {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a ε : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ) (p : Parameters a B ε)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → Fin (B + 1))
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ (c v).val)
    (s : V → GeneralCoveringInitializerRun.Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    let D := centers G ids a s
    let τ := GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ))
    GeneralCoveringInitializerPass.Covers C R D ∧ D ⊆ CoveringSupport.admissible C R ∧
    0 ≤ τ ∧ (D.card : ℝ) ≤ K a * τ ∧ p.xi * τ ≤ (ε / 4) * τ ∧
    (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G C D R p.L).card ≤ (ε / 4) * τ ∧
    2 * (B : ℝ) * (GeneralCoveringOwnerVirtualPrepare.high G C D R p.L p.Δ).card ≤ (ε / 4) * τ ∧
    2 * (B : ℝ) * (2 * p.η * (D.card : ℝ)) ≤ (ε / 4) * τ := by
  let D := centers G ids a s
  let τ := GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ))
  have hs := GeneralCoveringInitializerSupported.uniform_fin_spec G ids C targets ha hden B
    R hlocal hrows hinc c hcOne s hR hC hTargets
  have hcard : (D.card : ℝ) ≤ K a * τ := hs.2.2.1
  have hτ : 0 ≤ τ := GeneralCoveringInitializerSupported.supported_nonneg C R
    (fun v => ((c v).val : ℝ)) hrows (fun v _ => Nat.cast_nonneg _)
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hLp : (0 : ℝ) < p.L := by exact_mod_cast (show 0 < p.L by have := p.L_pos; omega)
  have hΔp : (0 : ℝ) < p.Δ := by exact_mod_cast p.Δ_pos
  have hh := GeneralCoveringHeavyCount.count G C D R p.L hlocal ha p.L_density hden
  have hq := GeneralCoveringOwnerHighCount.count G C D R p.L p.Δ p.L_pos hlocal ha0 hden
  refine ⟨hs.1, hs.2.1, hτ, hcard, mul_le_mul_of_nonneg_right p.solver_share hτ, ?_, ?_,
    boundary_budget p hτ hcard⟩
  · exact count_budget (w := (B : ℝ)) (c := 2 * a)
      hτ (Nat.cast_nonneg B) (by positivity) hLp hcard hh p.heavy_share
  · exact count_budget (w := 2 * (B : ℝ)) (c := 2 * a * ((p.L + 1 : ℕ) : ℝ) ^ 4)
      hτ (by positivity) (by positivity) hΔp hcard hq p.high_share

/-- Empty original R or zero original supported LP forces the actual
initializer output empty, by the cardinal inequality, without dividing by
tau or selecting any vertex. This also permits an empty physical type. -/
theorem degenerate {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a ε : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ) (p : Parameters a B ε)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → Fin (B + 1))
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ (c v).val)
    (s : V → GeneralCoveringInitializerRun.Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v)
    (he : R = ∅ ∨ GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ)) = 0) :
    centers G ids a s = ∅ ∧ GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ)) = 0 := by
  have hs := initialized G ids C targets ha hden B p R hlocal hrows hinc c hcOne s hR hC hTargets
  dsimp only at hs
  have hz : GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ)) = 0 := by
    rcases he with rfl | hz
    · exact GeneralCoveringNormalizedFractional.supportedNumber_empty C _
    · exact hz
  have hcard : ((centers G ids a s).card : ℝ) ≤ 0 := by
    simpa only [hz, mul_zero] using hs.2.2.2.1
  have hc : (centers G ids a s).card = 0 := by
    exact_mod_cast le_antisymm hcard (Nat.cast_nonneg (centers G ids a s).card)
  exact ⟨Finset.card_eq_zero.mp hc, hz⟩

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (GeneralCoveringTaskGeometry.ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _
noncomputable local instance lowAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (GeneralCoveringTaskGeometry.graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Exactly the boundary used by TaskFractionalRepair for THIS low partition.
This is analysis data, not a claim that a partition producer has executed. -/
noncomputable def boundary (C : V → Finset V) (D R : Finset V) (L Δ k : ℕ)
    (P : SmallParts.Data (GeneralCoveringTaskGeometry.graph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) Finset.univ k) :=
  BoundaryOwners.vertices (GeneralCoveringTaskGeometry.graph G C D R L
    (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) Finset.univ P.parts

/-- Conditional finite-mean composition for the SAME actual boundary and
actual initialized D. The boundary-mean and pointwise repair-cost contracts
are explicit intermediate analysis premises. No averaging/random program
or original-R runtime endpoint is asserted by this theorem. -/
theorem finite_mean {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    {a ε : ℝ} (ha : 1 ≤ a) (hden : MinorDensity.Bound G a) (B : ℕ) (p : Parameters a B ε)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → Fin (B + 1))
    (hcOne : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ (c v).val)
    (s : V → GeneralCoveringInitializerRun.Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v)
    {Ω : Type} [DecidableEq Ω] (S : Finset Ω) (hS : S.Nonempty) (k : ℕ) :
    let D := centers G ids a s
    let τ := GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ))
    ∀ (P : Ω → SmallParts.Data (GeneralCoveringTaskGeometry.graph G C D R p.L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R p.L p.Δ)) Finset.univ k) (cost : Ω → ℝ),
    mean S (fun ω => ((boundary G C D R p.L p.Δ k (P ω)).card : ℝ)) ≤ 2 * p.η * (D.card : ℝ) →
    (∀ ω ∈ S, cost ω ≤ (1 + p.xi) * τ +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G C D R p.L).card +
      2 * (B : ℝ) * (((GeneralCoveringOwnerVirtualPrepare.high G C D R p.L p.Δ).card : ℝ) +
        (boundary G C D R p.L p.Δ k (P ω)).card)) →
    mean S cost ≤ (1 + ε) * τ := by
  dsimp only
  intro P cost hboundary hrepair
  let D := centers G ids a s
  let τ := GeneralCoveringNormalizedFractional.supportedNumber C R (fun v => ((c v).val : ℝ))
  let H : ℝ := (GeneralCoveringOwnerSupport.heavy G C D R p.L).card
  let Q : ℝ := (GeneralCoveringOwnerVirtualPrepare.high G C D R p.L p.Δ).card
  let b : Ω → ℝ := fun ω => (boundary G C D R p.L p.Δ k (P ω)).card
  let A := (1 + p.xi) * τ + (B : ℝ) * H + 2 * (B : ℝ) * Q
  have hb : mean S b ≤ 2 * p.η * (D.card : ℝ) := hboundary
  have hc : ∀ ω ∈ S, cost ω ≤ A + (2 * (B : ℝ)) * b ω := by
    intro ω hω
    calc
      _ ≤ (1 + p.xi) * τ + (B : ℝ) * H + 2 * (B : ℝ) * (Q + b ω) := hrepair ω hω
      _ = _ := by dsimp only [A]; ring
  have hm : mean S cost ≤ A + (2 * (B : ℝ)) * mean S b :=
    (mean_mono S cost _ hc).trans_eq (mean_affine S hS A (2 * (B : ℝ)) b)
  have hi := initialized G ids C targets ha hden B p R hlocal hrows hinc c hcOne s hR hC hTargets
  dsimp only at hi
  obtain ⟨_, _, _, _, hsolver, hheavy, hhigh, hboundaryBudget⟩ := hi
  have hz : 2 * (B : ℝ) * mean S b ≤ (ε / 4) * τ :=
    (mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 2 * (B : ℝ) by positivity)).trans hboundaryBudget
  apply scalar_composition (xi := p.xi) (H := H) (Q := Q) (Z := mean S b) (B := (B : ℝ))
    (τ := τ) (ε := ε) _ hsolver hheavy hhigh hz
  calc
    _ ≤ A + (2 * (B : ℝ)) * mean S b := hm
    _ = _ := by dsimp only [A]; ring

/-- Empty averaging domain is handled separately from the normalized mean
of a nonempty family. No nonexistent outcome is chosen. -/
theorem empty_mean_bound {Ω : Type} [DecidableEq Ω] (cost : Ω → ℝ) {ε τ : ℝ}
    (hε : 0 < ε) (hτ : 0 ≤ τ) : mean ∅ cost ≤ (1 + ε) * τ := by
  rw [mean_empty]
  exact mul_nonneg (by linarith) hτ

/-- In particular a zero supported LP forces every allocated nonnegative
charge to vanish. No positivity of tau is required anywhere above. -/
theorem zero_charge {X τ ε : ℝ} (hτ : τ = 0) (hX : 0 ≤ X) (h : X ≤ (ε / 4) * τ) : X = 0 := by
  rw [hτ, mul_zero] at h
  exact le_antisymm h hX

end Paper.GeneralCoveringFractionalErrorBudget

#print axioms Paper.GeneralCoveringFractionalErrorBudget.K_pos
#print axioms Paper.GeneralCoveringFractionalErrorBudget.public_cutoff
#print axioms Paper.GeneralCoveringFractionalErrorBudget.parameters_exists
#print axioms Paper.GeneralCoveringFractionalErrorBudget.parameters
#print axioms Paper.GeneralCoveringFractionalErrorBudget.real_accuracy
#print axioms Paper.GeneralCoveringFractionalErrorBudget.count_budget
#print axioms Paper.GeneralCoveringFractionalErrorBudget.boundary_budget
#print axioms Paper.GeneralCoveringFractionalErrorBudget.scalar_composition
#print axioms Paper.GeneralCoveringFractionalErrorBudget.mean_mono
#print axioms Paper.GeneralCoveringFractionalErrorBudget.mean_affine
#print axioms Paper.GeneralCoveringFractionalErrorBudget.mean_empty
#print axioms Paper.GeneralCoveringFractionalErrorBudget.solver_density
#print axioms Paper.GeneralCoveringFractionalErrorBudget.repair_numeric_bound
#print axioms Paper.GeneralCoveringFractionalErrorBudget.initialized
#print axioms Paper.GeneralCoveringFractionalErrorBudget.degenerate
#print axioms Paper.GeneralCoveringFractionalErrorBudget.finite_mean
#print axioms Paper.GeneralCoveringFractionalErrorBudget.empty_mean_bound
#print axioms Paper.GeneralCoveringFractionalErrorBudget.zero_charge

