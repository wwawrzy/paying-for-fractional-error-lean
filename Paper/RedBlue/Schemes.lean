import Paper.RedBlue.FractionalEndpoint
import Paper.Solver.LocalSearch.GeneralCoveringRandomIntegralApproximation

/-! Actual general-cover schemes with red-blue private input, planar density
and public parameter order. No initial cover is supplied to either program. -/
namespace Paper.RedBlue
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def randomOriginal {M : ℕ} (R B : Finset V) (c : V → Fin (M + 1))
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hne : ∀ r ∈ R, (rows G R B r).Nonempty) :
    GeneralCoveringRandomIntegralApproximation.Original G k t M (solverInput G R B c) where
  cover := rows G R B
  targets := targets G R B
  R := R
  hk := hk
  ht := ht
  incidence := targets_incidence G R B
  local_rows := fun r _ => rows_local G R B r
  nonempty_rows := hne
  demand := fun _ => rfl
  candidates := fun _ => rfl
  inverse := fun _ => rfl

noncomputable def deterministicOriginal {M : ℕ} (R B : Finset V) (c : V → Fin (M + 1))
    (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hne : ∀ r ∈ R, (rows G R B r).Nonempty) :
    GeneralCoveringInitializedPhysical.Original G k t M (solverInput G R B c) where
  cover := rows G R B
  targets := targets G R B
  R := R
  hk := hk
  ht := ht
  incidence := targets_incidence G R B
  local_rows := fun r _ => rows_local G R B r
  nonempty_rows := hne
  demand := fun _ => rfl
  candidates := fun _ => rfl
  inverse := fun _ => rfl

theorem covers_iff (R B D : Finset V) :
    GeneralCoveringNormalizedIntegral.Covers (rows G R B) R D ↔
      ∀ r ∈ R, ∃ v ∈ D, v ∈ B ∧ G.Adj r v := by
  constructor
  · intro h r hr
    obtain ⟨v, hv, hrow⟩ := h r hr
    obtain ⟨_, ha, hb⟩ := (mem_rows G R B r v).mp hrow
    exact ⟨v, hv, hb, ha⟩
  · intro h r hr
    obtain ⟨v, hv, hb, ha⟩ := h r hr
    exact ⟨v, hv, (mem_rows G R B r v).mpr ⟨hr, ha, hb⟩⟩

theorem randomized_parameters (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε)
    (C P E : ℕ) :
    ∃ q : GeneralCoveringRandomIntegralApproximation.Parameters 3, ∃ Kr Kb : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → ∀ {bits : ℕ} (ids : BitCode V bits) (N : ℕ),
        bits ≤ C * Nat.clog 2 N → N ≤ P * (Fintype.card V + 2) ^ E →
        ∀ (R B : Finset V) (c : V → Fin (M + 1))
          (hne : ∀ r ∈ R, (rows G R B r).Nonempty),
        (∀ v ∈ B, 1 ≤ (c v).val) →
        GeneralCoveringRandomIntegralApproximation.Specification G ids 3 M q hM ε
          (solverInput G R B c) (randomOriginal G R B c q.k q.t q.hk q.ht hne) ∧
        (GeneralCoveringRandomIntegralApproximation.program ids 3 M q hM).rounds = Kr ∧
        (GeneralCoveringRandomIntegralApproximation.program ids 3 M q hM).maxBits ≤
          Kb * Nat.clog 2 (Fintype.card V + 2) := by
  obtain ⟨q, Kr, Kb, hq⟩ := GeneralCoveringRandomIntegralApproximation.uniform_scheme
    3 M (by decide) hM ε hε C P E
  refine ⟨q, Kr, Kb, ?_⟩
  intro V _ _ G _ hp bits ids N hbits hN R B c hne hc
  exact hq G (FiveCliqueDensity.minor_density G hp.1) ids N hbits hN
    (solverInput G R B c) (randomOriginal G R B c q.k q.t q.hk q.ht hne)
    (fun v hv => hc v (admissible_subset_blue G R B hv))

theorem deterministic_parameters (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε : 0 < ε)
    (C P E : ℕ) :
    ∃ q : GeneralCoveringDeterministicApproximation.Parameters 3, ∃ Kr Kb : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → ∀ {bits : ℕ} (ids : BitCode V bits) (N : ℕ),
        bits ≤ C * Nat.clog 2 N → N ≤ P * (Fintype.card V + 2) ^ E →
        ∀ (R B : Finset V) (c : V → Fin (M + 1))
          (hne : ∀ r ∈ R, (rows G R B r).Nonempty),
        (∀ v ∈ B, 1 ≤ (c v).val) →
        GeneralCoveringDeterministicApproximation.Specification G ids 3 M q hM ε
          (solverInput G R B c) (deterministicOriginal G R B c q.k q.t q.hk q.ht hne) ∧
        (GeneralCoveringDeterministicApproximation.program ids 3 M q hM).rounds ≤
          Kr * (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
        (GeneralCoveringDeterministicApproximation.program ids 3 M q hM).maxBits ≤
          Kb * Nat.clog 2 (Fintype.card V + 2) := by
  obtain ⟨q, Kr, Kb, hq⟩ := GeneralCoveringDeterministicApproximation.uniform_scheme
    3 M (by decide) hM ε hε C P E
  refine ⟨q, Kr, Kb, ?_⟩
  intro V _ _ G _ hp bits ids N hbits hN R B c hne hc
  exact hq G (FiveCliqueDensity.minor_density G hp.1) ids N hbits hN
    (solverInput G R B c) (deterministicOriginal G R B c q.k q.t q.hk q.ht hne)
    (fun v hv => hc v (admissible_subset_blue G R B hv))

end Paper.RedBlue
#print axioms Paper.RedBlue.randomOriginal
#print axioms Paper.RedBlue.deterministicOriginal
#print axioms Paper.RedBlue.covers_iff
#print axioms Paper.RedBlue.randomized_parameters
#print axioms Paper.RedBlue.deterministic_parameters
