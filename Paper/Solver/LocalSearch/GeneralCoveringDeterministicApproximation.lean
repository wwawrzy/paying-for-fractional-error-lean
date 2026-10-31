import Paper.Solver.LocalSearch.GeneralCoveringPhysicalBoundaryBound
import Paper.Solver.LocalSearch.GeneralCoveringInitializerFractional

/-! Deterministic integral approximation by the unchanged initialized physical
program. Public parameters precede the graph and private data. Only the
initializer's NUMERIC uniform choices are used from the fractional module;
all benchmarks below are arbitrary original admissible integral C-covers. -/
namespace Paper.GeneralCoveringDeterministicApproximation
open BroadcastModel SevenFoundation
open scoped BigOperators

/-- Numeric initializer hypotheses only; no graph, cover or output certificate. -/
structure Initialization (a : ℕ) where
  b : ℕ
  h : ℕ
  f : ℕ
  U : ℕ
  hb : 1 ≤ b
  hU : 1 ≤ U
  twice_density : 2 * (a : ℝ) ≤ U
  candidate_threshold : U + 4 * U * U ≤ h
  list_threshold : U + 4 * U * U * U ≤ f
  capacity : (a : ℝ) * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b

noncomputable def Initialization.factor {a : ℕ} (i : Initialization a) : ℕ :=
  GeneralCoveringInitializerRunBounds.constant i.b i.h i.f i.U + 1

theorem Initialization.factor_pos {a : ℕ} (i : Initialization a) : 0 < i.factor := Nat.succ_pos _

theorem initialization_exists (a : ℕ) (ha : 1 ≤ a) : Nonempty (Initialization a) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hp := GeneralCoveringInitializerFractional.uniform_parameters (a : ℝ) ha'
  exact ⟨{
    b := GeneralCoveringInitializerFractional.listBound a
    h := GeneralCoveringInitializerFractional.candidateThreshold a
    f := GeneralCoveringInitializerFractional.listThreshold a
    U := GeneralCoveringInitializerFractional.scale a
    hb := hp.2.2.1
    hU := hp.1
    twice_density := hp.2.1
    candidate_threshold := le_refl _
    list_threshold := le_refl _
    capacity := hp.2.2.2 }⟩

/-- The real numbers select public naturals in proofs only. -/
structure Parameters (a : ℕ) where
  init : Initialization a
  L : ℕ
  Δ : ℕ
  k : ℕ
  t : ℕ
  T : ℕ
  hk : 0 < k
  ht : 0 < t

abbrev program {V : Type} [LinearOrder V] {bits : ℕ} (ids : BitCode V bits)
    (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B) :=
  GeneralCoveringInitializedPhysical.program ids q.init.b q.init.h q.init.f q.init.U
    q.L q.Δ a q.k q.t q.T B hB

abbrev output {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B)
    (x : V → GeneralCoveringInitializedPhysical.Input V B) :=
  GeneralCoveringInitializedPhysical.output G ids q.init.b q.init.h q.init.f q.init.U
    q.L q.Δ a q.k q.t q.T B hB x

/-- Pure scalar selection: the divisor is a public positive natural. -/
theorem public_cutoff (c base ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 1 ≤ n ∧ base ≤ (n : ℝ) ∧ c / n ≤ ε / 3 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max 1 base) (3 * c / ε))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt ((le_max_left 1 base).trans (le_max_left _ _)) hn
  have hnN : 1 ≤ n := by exact_mod_cast (le_of_lt hn1)
  have hn0 : (0 : ℝ) < n := by linarith
  have hb : base ≤ (n : ℝ) :=
    (le_max_right 1 base).trans ((le_max_left _ _).trans (le_of_lt hn))
  have hc : 3 * c ≤ (n : ℝ) * ε :=
    (div_le_iff₀ hε).mp ((le_max_right _ _).trans (le_of_lt hn))
  refine ⟨n, hnN, hb, (div_le_iff₀ hn0).mpr ?_⟩
  nlinarith

/-- Three separately proved epsilon/3 budgets, fixed before every graph. -/
theorem error_budgets (a B K : ℕ) (hB : 1 ≤ B) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ∃ L Δ : ℕ, ∃ η : ℝ, 1 ≤ L ∧ 4 * (a : ℝ) ≤ L ∧ 0 < Δ ∧ 0 < η ∧
      (B : ℝ) * (2 * a) * K / L ≤ ε / 3 ∧
      (2 * (B : ℝ)) * (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4) * K / Δ ≤ ε / 3 ∧
      (2 * (B : ℝ)) * (2 * η) * K ≤ ε / 3 := by
  obtain ⟨L, hL, hLa, hheavy⟩ := public_cutoff ((B : ℝ) * (2 * a) * K) (4 * a) ε hε
  obtain ⟨Δ, hΔ, _, hhigh⟩ := public_cutoff
    ((2 * (B : ℝ)) * (2 * a * ((L + 1 : ℕ) : ℝ) ^ 4) * K) 1 ε hε
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  let η := ε / (12 * (B : ℝ) * K)
  have hden : (0 : ℝ) < 12 * (B : ℝ) * K := by positivity
  have hη : 0 < η := div_pos hε hden
  have he : η * (12 * (B : ℝ) * K) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
  refine ⟨L, Δ, η, hL, hLa, by omega, hη, hheavy, hhigh, ?_⟩
  nlinarith [he]

/-- Graph-free conversion of a count bound and a public coefficient budget. -/
theorem count_budget {N M X K w c den ε : ℝ}
    (hM : 0 ≤ M) (hw : 0 ≤ w) (hc : 0 ≤ c) (hd : 0 < den)
    (hN : N ≤ K * M) (hcount : den * X ≤ c * N) (hbudget : w * c * K / den ≤ ε / 3) :
    w * X ≤ (ε / 3) * M := by
  have hX : X ≤ c * N / den := (le_div_iff₀ hd).mpr (by
    calc
      X * den = den * X := mul_comm _ _
      _ ≤ c * N := hcount)
  calc
    _ ≤ w * (c * N / den) := mul_le_mul_of_nonneg_left hX hw
    _ ≤ w * (c * (K * M) / den) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN hc) (le_of_lt hd)) hw
    _ = (w * c * K / den) * M := by ring
    _ ≤ (ε / 3) * M := mul_le_mul_of_nonneg_right hbudget hM

theorem additive_to_approximation {y m p q z B ε : ℝ}
    (hy : y ≤ m + B * p + 2 * B * (q + z))
    (hp : B * p ≤ (ε / 3) * m) (hq : 2 * B * q ≤ (ε / 3) * m)
    (hz : 2 * B * z ≤ (ε / 3) * m) : y ≤ (1 + ε) * m := by
  nlinarith

section Graph
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact guarantee about the actual unchanged program's selected output. -/
structure Specification {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B)
    (ε : ℝ) (x : V → GeneralCoveringInitializedPhysical.Input V B)
    (d : GeneralCoveringInitializedPhysical.Original G q.k q.t B x) : Prop where
  admissible : output G ids a B q hB x ⊆ CoveringSupport.admissible d.cover d.R
  covers : GeneralCoveringNormalizedIntegral.Covers d.cover d.R (output G ids a B q hB x)
  competitive : ∀ W : Finset V, W ⊆ CoveringSupport.admissible d.cover d.R →
    GeneralCoveringNormalizedIntegral.Covers d.cover d.R W →
    ((∑ v ∈ output G ids a B q hB x, (x v).2.val : ℕ) : ℝ) ≤
      (1 + ε) * ((∑ v ∈ W, (x v).2.val : ℕ) : ℝ)

/-- Actual initializer cardinal against EVERY original admissible integral
cover, using positivity only on original admissible candidates. -/
theorem centers_cost {a k t B bits : ℕ} (ids : BitCode V bits) (i : Initialization a)
    {x : V → GeneralCoveringInitializedPhysical.Input V B}
    (d : GeneralCoveringInitializedPhysical.Original G k t B x)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val)
    (W : Finset V) (hWad : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (GeneralCoveringInitializedPhysical.centers G ids i.b i.h i.f i.U B x).card ≤
      i.factor * (∑ v ∈ W, (x v).2.val) := by
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast (show 0 ≤ a by omega)
  have hn := GeneralCoveringInitializerRunBounds.selected_card G d.cover i.b i.h i.f i.U i.U
    i.hb i.hU i.hU i.candidate_threshold i.list_threshold ha0 i.twice_density i.twice_density
    hden i.capacity d.R W hW d.local_rows
  have hcenters := GeneralCoveringInitializedPhysical.centers_selected
    (b := i.b) (h := i.h) (f := i.f) (U := i.U) G ids i.hb d
  rw [← hcenters] at hn
  have hf : GeneralCoveringInitializerRunBounds.constant i.b i.h i.f i.U ≤ i.factor := Nat.le_succ _
  have hWcost : W.card ≤ ∑ v ∈ W, (x v).2.val := by
    calc
      W.card = ∑ _v ∈ W, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => hc v (hWad hv))
  exact hn.trans ((Nat.mul_le_mul_right W.card hf).trans (Nat.mul_le_mul_left i.factor hWcost))

theorem empty_demands {bits a B : ℕ} {ids : BitCode V bits} {q : Parameters a} {hB : 1 ≤ B}
    {ε : ℝ} {x : V → GeneralCoveringInitializedPhysical.Input V B}
    {d : GeneralCoveringInitializedPhysical.Original G q.k q.t B x}
    (hs : Specification G ids a B q hB ε x d) (hR : d.R = ∅) : output G ids a B q hB x = ∅ := by
  have he : output G ids a B q hB x ⊆ ∅ := by
    simpa only [hR, CoveringSupport.admissible, Finset.biUnion_empty] using hs.admissible
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (he hv))

/-- A zero-cost competitor forces empty ACTUAL output, and actual coverage
then forces empty original demand. No positive-cost premise outside admissible. -/
theorem zero_benchmark {bits a B : ℕ} {ids : BitCode V bits} {q : Parameters a} {hB : 1 ≤ B}
    {ε : ℝ} {x : V → GeneralCoveringInitializedPhysical.Input V B}
    {d : GeneralCoveringInitializedPhysical.Original G q.k q.t B x}
    (hs : Specification G ids a B q hB ε x d)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val)
    (W : Finset V) (hWad : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) (hz : ∑ v ∈ W, (x v).2.val = 0) :
    output G ids a B q hB x = ∅ ∧ d.R = ∅ := by
  have hy := hs.competitive W hWad hW
  rw [hz, Nat.cast_zero, mul_zero] at hy
  have hy0 : (∑ v ∈ output G ids a B q hB x, (x v).2.val) ≤ 0 := by exact_mod_cast hy
  have he : output G ids a B q hB x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hvCost := Finset.single_le_sum (fun u _ => Nat.zero_le ((x u).2.val)) hv
    have hp := hc v (hs.admissible hv)
    omega
  refine ⟨he, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro r hr
  obtain ⟨v, hv, _⟩ := hs.covers r hr
  rw [he] at hv
  exact Finset.notMem_empty v hv

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a)
    (hB : 1 ≤ B) (x : V → GeneralCoveringInitializedPhysical.Input V B) : output G ids a B q hB x = ∅ :=
  GeneralCoveringInitializedPhysical.empty_physical G ids q.init.b q.init.h q.init.f q.init.U
    q.L q.Δ a q.k q.t q.T B hB x
end Graph

/-- Natural parameters are selected before graph/IDs/original private data.
The statement is against every genuine integral cover, not a supplied optimum. -/
theorem uniform_approximation (a B : ℕ) (ha : 1 ≤ a) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Parameters a,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ {bits : ℕ} (ids : BitCode V bits)
        (x : V → GeneralCoveringInitializedPhysical.Input V B)
        (d : GeneralCoveringInitializedPhysical.Original G q.k q.t B x),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val) →
        Specification G ids a B q hB ε x d := by
  obtain ⟨i⟩ := initialization_exists a ha
  obtain ⟨L, Δ, η, hL, hLa, hΔ, hη, hheavy, hhigh, hboundary⟩ :=
    error_budgets a B i.factor hB i.factor_pos ε hε
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha'
  obtain ⟨t, k, T, ht, hk, hbdy⟩ := GeneralCoveringPhysicalBoundaryBound.initialized_parameters
    (a : ℝ) ha0 L hL Δ η hη
  let q : Parameters a := ⟨i, L, Δ, k, t, T, hk, ht⟩
  refine ⟨q, ?_⟩
  intro V _ _ G _ hden bits ids x d hc
  have hs := GeneralCoveringInitializedPhysical.covers (b := i.b) (h := i.h) (f := i.f) (U := i.U)
    (L := L) (Δ := Δ) (a := a) (T := T) G ids i.hb hB d ha hden hc
  refine ⟨hs.1, hs.2, ?_⟩
  intro W hWad hW
  let D := GeneralCoveringInitializedPhysical.centers G ids i.b i.h i.f i.U B x
  let P := GeneralCoveringOwnerSupport.heavy G d.cover D d.R L
  let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover D d.R L Δ
  let Z := GeneralCoveringInitializedPhysical.boundary (b := i.b) (h := i.h) (f := i.f) (U := i.U)
    (L := L) (Δ := Δ) (T := T) G ids d
  let m := ∑ v ∈ W, (x v).2.val
  have hN : (D.card : ℝ) ≤ (i.factor : ℝ) * m := by
    exact_mod_cast centers_cost G ids i d ha hden hc W hWad hW
  have hP : (L : ℝ) * P.card ≤ 2 * (a : ℝ) * D.card :=
    GeneralCoveringHeavyCount.count G d.cover D d.R L d.local_rows ha' hLa hden
  have hQ : (Δ : ℝ) * Q.card ≤ (2 * (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card := by
    simpa only [mul_assoc] using GeneralCoveringOwnerHighCount.count G d.cover D d.R L Δ hL d.local_rows ha0 hden
  have hZ : (Z.card : ℝ) ≤ 2 * η * D.card :=
    (hbdy G hden ids i.b i.h i.f i.U B x d).2
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hΔ0 : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hp : (B : ℝ) * P.card ≤ (ε / 3) * m :=
    count_budget (c := 2 * (a : ℝ)) (den := (L : ℝ)) hm (Nat.cast_nonneg B) (by positivity) hL0 hN hP hheavy
  have hq : (2 * (B : ℝ)) * Q.card ≤ (ε / 3) * m :=
    count_budget (c := 2 * (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) (den := (Δ : ℝ))
      hm (by positivity) (by positivity) hΔ0 hN hQ hhigh
  have hz : (2 * (B : ℝ)) * Z.card ≤ (ε / 3) * m :=
    count_budget (c := 2 * η) (den := 1) hm (by positivity) (by positivity) (by norm_num) hN
      (by simpa only [one_mul] using hZ) (by simpa only [div_one] using hboundary)
  have hn : (∑ v ∈ output G ids a B q hB x, (x v).2.val) ≤ m + B * P.card + 2 * B * (Q.card + Z.card) :=
    GeneralCoveringInitializedPhysical.cost (b := i.b) (h := i.h) (f := i.f) (U := i.U)
      (L := L) (Δ := Δ) (a := a) (T := T) G ids i.hb hB d ha hden hc W hWad hW
  have hr : ((∑ v ∈ output G ids a B q hB x, (x v).2.val : ℕ) : ℝ) ≤
      (m : ℝ) + (B : ℝ) * P.card + 2 * B * ((Q.card : ℝ) + Z.card) := by exact_mod_cast hn
  exact additive_to_approximation hr hp hq hz

/-- Public encoding/polynomial constants also precede the graph. The actual
program and messages are exactly those of the accepted InitializedPhysical. -/
theorem uniform_scheme (a B : ℕ) (ha : 1 ≤ a) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) (c p e : ℕ) :
    ∃ q : Parameters a, ∃ Kr Kb : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ {bits : ℕ} (ids : BitCode V bits) (M : ℕ),
        bits ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card V + 2) ^ e →
        ∀ (x : V → GeneralCoveringInitializedPhysical.Input V B)
        (d : GeneralCoveringInitializedPhysical.Original G q.k q.t B x),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val) →
        Specification G ids a B q hB ε x d ∧
        (program ids a B q hB).rounds ≤ Kr * (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
        (program ids a B q hB).maxBits ≤ Kb * Nat.clog 2 (Fintype.card V + 2) := by
  obtain ⟨q, hq⟩ := uniform_approximation a B ha hB ε hε
  refine ⟨q, GeneralCoveringInitializedPhysical.roundCoefficient q.init.h q.init.f q.init.U q.L q.Δ a q.k q.T B c p e,
    GeneralCoveringInitializedPhysical.bitCoefficient q.init.f q.L q.Δ a q.k B c p e, ?_⟩
  intro V _ _ G _ hden bits ids M hbits hM x d hc
  exact ⟨hq G hden ids x d hc,
    GeneralCoveringInitializedPhysical.costs ids q.init.b q.init.h q.init.f q.init.U q.L q.Δ a q.k q.t q.T B c p e M hB hbits hM⟩

/-- paper order: real density rho, cost bound and epsilon first; the
public integer density capacity, program parameters and resource constants
are then fixed before every graph/ID/private input. -/
theorem deterministic_scheme (ρ : ℝ) (hρ : 1 ≤ ρ) (B : ℕ) (hB : 1 ≤ B)
    (ε : ℝ) (hε : 0 < ε) (c p e : ℕ) :
    ∃ a : ℕ, ∃ q : Parameters a, ∃ Kr Kb : ℕ, ρ ≤ (a : ℝ) ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G ρ → ∀ {bits : ℕ} (ids : BitCode V bits) (M : ℕ),
        bits ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card V + 2) ^ e →
        ∀ (x : V → GeneralCoveringInitializedPhysical.Input V B)
        (d : GeneralCoveringInitializedPhysical.Original G q.k q.t B x),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val) →
        Specification G ids a B q hB ε x d ∧
        (program ids a B q hB).rounds ≤ Kr * (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
        (program ids a B q hB).maxBits ≤ Kb * Nat.clog 2 (Fintype.card V + 2) := by
  let a := Nat.ceil ρ
  have hρa : ρ ≤ (a : ℝ) := Nat.le_ceil ρ
  have ha : 1 ≤ a := by exact_mod_cast hρ.trans hρa
  obtain ⟨q, Kr, Kb, hq⟩ := uniform_scheme a B ha hB ε hε c p e
  refine ⟨a, q, Kr, Kb, hρa, ?_⟩
  intro V _ _ G _ hden bits ids M hbits hM x d hc
  have hdenA : MinorDensity.Bound G (a : ℝ) := by
    intro W _ _ J _ hm
    exact (hden W J hm).trans (mul_le_mul_of_nonneg_right hρa (Nat.cast_nonneg _))
  exact hq G hdenA ids M hbits hM x d hc

end Paper.GeneralCoveringDeterministicApproximation

#print axioms Paper.GeneralCoveringDeterministicApproximation.Initialization.factor_pos
#print axioms Paper.GeneralCoveringDeterministicApproximation.initialization_exists
#print axioms Paper.GeneralCoveringDeterministicApproximation.public_cutoff
#print axioms Paper.GeneralCoveringDeterministicApproximation.error_budgets
#print axioms Paper.GeneralCoveringDeterministicApproximation.count_budget
#print axioms Paper.GeneralCoveringDeterministicApproximation.additive_to_approximation
#print axioms Paper.GeneralCoveringDeterministicApproximation.centers_cost
#print axioms Paper.GeneralCoveringDeterministicApproximation.empty_demands
#print axioms Paper.GeneralCoveringDeterministicApproximation.zero_benchmark
#print axioms Paper.GeneralCoveringDeterministicApproximation.empty_physical
#print axioms Paper.GeneralCoveringDeterministicApproximation.uniform_approximation
#print axioms Paper.GeneralCoveringDeterministicApproximation.uniform_scheme
#print axioms Paper.GeneralCoveringDeterministicApproximation.deterministic_scheme
