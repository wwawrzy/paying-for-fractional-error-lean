import Paper.Solver.LocalSearch.GeneralCoveringFractionalEndpoint

/-! The general fractional solver on open neighborhoods with unit costs.
The input lists are constructed locally before the solver starts. The
benchmark is the fractional total domination number of the original graph. -/
namespace Paper.TotalDomination.FractionalSolver
open BroadcastModel SevenFoundation
open scoped BigOperators

variable {V : Type} [LinearOrder V]

def startup : Program V PUnit (GeneralCoveringFractionalEndpoint.Input V 1) :=
  .local fun _ N _ => (⟨true, N, N⟩, ⟨1, by decide⟩)

noncomputable def runtime {ids : ℕ} (I : BitCode V ids) {a ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a 1 ε) (t k b n : ℕ) :=
  Program.seq startup (GeneralCoveringFractionalEndpoint.runtime I p t k b n (by decide))

theorem rounds {ids : ℕ} (I : BitCode V ids) {a ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a 1 ε) (t k b n : ℕ) :
    (runtime I p t k b n).rounds =
      (GeneralCoveringFractionalEndpoint.runtime I p t k b n (by decide)).rounds := by
  simp only [runtime, startup, Program.rounds, Nat.zero_add]

theorem maxBits {ids : ℕ} (I : BitCode V ids) {a ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a 1 ε) (t k b n : ℕ) :
    (runtime I p t k b n).maxBits =
      (GeneralCoveringFractionalEndpoint.runtime I p t k b n (by decide)).maxBits := by
  simp only [runtime, startup, Program.maxBits, Nat.zero_max]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def input (v : V) : GeneralCoveringFractionalEndpoint.Input V 1 :=
  (⟨true, G.neighborFinset v, G.neighborFinset v⟩, ⟨1, by decide⟩)

def original (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    GeneralCoveringInitializedFrameAverage.Original G (input G) where
  cover := fun v => G.neighborFinset v
  targets := fun v => G.neighborFinset v
  R := Finset.univ
  incidence := fun v r => by simp only [SimpleGraph.mem_neighborFinset, G.adj_comm]
  local_rows := fun r _ v hv =>
    (mem_closed G v r).mpr (Or.inr ((G.mem_neighborFinset r v).mp hv))
  rows := fun r _ => hfree r
  residual := fun r => by simp [input]
  candidates := fun _ => rfl
  inverse := fun _ => rfl

noncomputable def fractionalNumber : ℝ :=
  CoveringOptimum.number (fun v => G.neighborFinset v) Finset.univ (fun _ => 1)

noncomputable def solution {ids : ℕ} (I : BitCode V ids) {a ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a 1 ε) (t k b n : ℕ) (v : V) : ℝ :=
  (((runtime I p t k b n).runEncoded G (fun _ => PUnit.unit) v).1.val : ℝ) /
    GeneralCoveringOwnerFrameAverage.denominator p.L p.Δ k b n p.q

theorem solution_eq {ids : ℕ} (I : BitCode V ids) {a ε : ℝ}
    (p : GeneralCoveringFractionalErrorBudget.Parameters a 1 ε) (t k b n : ℕ) :
    solution G I p t k b n =
      GeneralCoveringFractionalEndpoint.solution G I p t k b n (by decide) (input G) := by
  funext v
  simp only [solution, GeneralCoveringFractionalEndpoint.solution, runtime,
    Program.runEncoded_eq_run, Program.run, startup]
  rfl

theorem benchmark_eq (hfree : ∀ v, (G.neighborFinset v).Nonempty) :
    GeneralCoveringNormalizedFractional.supportedNumber (fun v => G.neighborFinset v) Finset.univ
      (fun _ => 1) = fractionalNumber G :=
  GeneralCoveringNormalizedFractional.supportedNumber_eq_number _ _ _
    (fun v _ => hfree v) (fun _ => by norm_num)

/-- Public parameters are chosen before every graph and identifier codec.
The actual local initialization requires no graphwide input lists. -/
theorem parameters (a : ℝ) (ha : 1 ≤ a) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : GeneralCoveringFractionalErrorBudget.Parameters a 1 ε,
      ∃ t k b n : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      MinorDensity.Bound G a → (∀ v, (G.neighborFinset v).Nonempty) →
      ∀ {ids : ℕ} (I : BitCode V ids),
        let x := solution G I p t k b n
        (∀ v, 0 ≤ x v) ∧ (∀ r, 1 ≤ ∑ v ∈ G.neighborFinset r, x v) ∧
          (∑ v, x v) ≤ (1 + ε) * fractionalNumber G := by
  obtain ⟨p, t, k, b, n, ht, hk, hp⟩ :=
    GeneralCoveringFractionalEndpoint.parameters a ha 1 (by decide) ε hε
  refine ⟨p, t, k, b, n, ht, hk, ?_⟩
  intro V _ _ G _ hden hfree ids I
  have hs := hp G hden I (input G) (original G hfree) (fun _ _ => Nat.le_refl 1)
  dsimp only
  rw [solution_eq]
  refine ⟨hs.1.1, fun r => hs.1.2.2 r (Finset.mem_univ r), ?_⟩
  have hc := hs.2.1
  change SevenFoundation.cost
    (GeneralCoveringFractionalCorrect.coverInstance Finset.univ (fun v => G.neighborFinset v)
      (fun _ => (⟨1, by decide⟩ : Fin 2))) _ ≤ _ at hc
  simp only [SevenFoundation.cost, GeneralCoveringFractionalCorrect.coverInstance,
    Nat.cast_one, one_mul] at hc
  simpa only [input, original, Nat.cast_one, benchmark_eq G hfree] using hc

end Paper.TotalDomination.FractionalSolver

#print axioms Paper.TotalDomination.FractionalSolver.solution_eq
#print axioms Paper.TotalDomination.FractionalSolver.benchmark_eq
#print axioms Paper.TotalDomination.FractionalSolver.parameters
