import Paper.Solver.LocalSearch.GeneralCoveringInputNormalization
import Paper.Endpoints.Components.SmallComponentSetDecision

/-! Demand-bit normalization followed by actual raw bounded search.
The optional word is returned unchanged, including failure. Public runtime
arguments are only the identifier codec and scalar bounds. Contexts, incidence
functions, and positivity certificates occur exclusively in correctness proofs.
No feasible cost-budget witness or universal success is assumed. -/

namespace Paper.NormalizedComponentSearch

open BroadcastModel SevenFoundation
open scoped BigOperators

variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input

def program {bits : ℕ} (C : BitCode V bits) (diam a B K : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Option (SolutionWord.Word V B)) :=
  .seq (GeneralCoveringInputNormalization.program B hB)
    (.seq (.local fun _ _ s => GeneralCoveringFractional.searchInput 1 s)
      (GeneralCoveringSearch.program C diam a B 1 K))

variable [Fintype V] (I : SimpleGraph V) [DecidableRel I.Adj]

/-- Exact encoded composition retains the raw search result. -/
theorem run_program {bits : ℕ} (C : BitCode V bits) (diam a B K : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program C diam a B K hB).runEncoded I s =
      (GeneralCoveringSearch.program C diam a B 1 K).runEncoded I
        (fun v => GeneralCoveringFractional.searchInput 1
          ((GeneralCoveringInputNormalization.program B hB).runEncoded I s v)) := rfl

theorem run_program_eq_run {bits : ℕ} (C : BitCode V bits) (diam a B K : ℕ)
    (hB : 1 ≤ B) (s : V → Input V B) :
    (program C diam a B K hB).runEncoded I s =
      (GeneralCoveringSearch.program C diam a B 1 K).run I
        (fun v => GeneralCoveringFractional.searchInput 1
          ((GeneralCoveringInputNormalization.program B hB).runEncoded I s v)) := by
  rw [run_program, Program.runEncoded_eq_run]

/-- The normalized raw search has its full sound/complete/uniform contract,
without any assumption that a feasible solution lies within the budget. -/
theorem normalized_spec (H : ActiveTask.Context I) (R : Finset V) (hR : R ⊆ H.vertices)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed I r)
    (a : ℕ) (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound I (a : ℝ))
    (B K : ℕ) (hB : 1 ≤ B) {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (hactive : ∀ v, (s v).active = decide (v ∈ H.vertices))
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    let ns := (GeneralCoveringInputNormalization.program B hB).runEncoded I s
    GeneralCoveringSpec.Spec (fun r => (ns r).candidates) I
      (GeneralCoveringSearch.program C H.diameter a B 1 K) H.vertices
      (fun v => (ns v).cost) (TaskBenchmark.demand (q := 1) R) K
      (fun v => GeneralCoveringFractional.searchInput 1 (ns v)) := by
  let ns := (GeneralCoveringInputNormalization.program B hB).runEncoded I s
  let rows : V → Finset V := fun r => (ns r).candidates
  let inverse : V → Finset V := fun v => (ns v).targets
  let input := fun v => GeneralCoveringFractional.searchInput 1 (ns v)
  have hninc : ∀ v r, r ∈ inverse v ↔ v ∈ rows r := by
    intro v r
    exact GeneralCoveringInputNormalization.agreement I cover targets R hinc hlocal hB s hd hC ht v r
  have hnlocal : ∀ r ∈ H.vertices, rows r ⊆ closed I r := by
    intro r _
    exact GeneralCoveringInputNormalization.locality I cover R hlocal hB s hd hC r
  have hnactive : ∀ v, (input v).base.active = decide (v ∈ H.vertices) := by
    intro v
    exact (GeneralCoveringInputNormalization.metadata I B hB s v).1.trans (hactive v)
  have hndemand : ∀ v, (ns v).demand = decide (v ∈ R) := by
    intro v
    exact (GeneralCoveringInputNormalization.metadata I B hB s v).2.trans (hd v)
  have hnvalue : ∀ v, (input v).base.value = TaskBenchmark.demand (q := 1) R v := by
    intro v
    apply Fin.ext
    change (if (ns v).demand then 1 else 0) = if v ∈ R then 1 else 0
    rw [hndemand v]
    by_cases hv : v ∈ R <;> simp [hv]
  exact GeneralCoveringSearch.correct I H rows inverse hninc hnlocal a ha hden B 1
    (fun v => (ns v).cost) C K (TaskBenchmark.demand (q := 1) R) input
    hnactive (fun _ => rfl) hnvalue (TaskBenchmark.demand_outside H.vertices R hR)
    (fun _ => rfl) (fun _ => rfl)

/-- All costs seen by search are positive; only original admissible costs
need positivity. The other original costs may be zero. -/
theorem normalized_positive (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed I r)
    {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (s v).cost.val) :
    ∀ v, 1 ≤ ((GeneralCoveringInputNormalization.program B hB).runEncoded I s v).cost.val :=
  GeneralCoveringInputNormalization.positive I cover targets R hinc hlocal s hd ht hB hc

/-- The actual optional result decides affordable sets for normalized rows
and costs. The incidence-containment premise is explicit. -/
theorem solved_iff_normalized_set (H : ActiveTask.Context I) (R : Finset V)
    (hR : R ⊆ H.vertices) (cover targets : V → Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed I r)
    (htask : ∀ r ∈ R, cover r ⊆ H.vertices)
    (a : ℕ) (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound I (a : ℝ))
    (B K : ℕ) (hB : 1 ≤ B) {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (hactive : ∀ v, (s v).active = decide (v ∈ H.vertices))
    (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (s v).cost.val)
    (v : V) (hv : v ∈ H.vertices) :
    let ns := (GeneralCoveringInputNormalization.program B hB).runEncoded I s
    SmallComponentSearchDecision.Solved ((program C H.diameter a B K hB).runEncoded I s v) K ↔
      ∃ O : Finset V, O ⊆ CoveringSupport.admissible (fun r => (ns r).candidates) R ∧
        GeneralCoveringIntegral.Covers (fun r => (ns r).candidates) R O ∧
        (∑ u ∈ O, (ns u).cost.val) ≤ K := by
  dsimp only
  rw [run_program_eq_run]
  have hspec := normalized_spec I H R hR cover targets hinc hlocal a ha hden B K hB C s
    hactive hd hC ht
  have hp := normalized_positive I cover targets R hinc hlocal hB s hd ht hc
  have hntask : ∀ r ∈ R,
      ((GeneralCoveringInputNormalization.program B hB).runEncoded I s r).candidates ⊆ H.vertices := by
    intro r hr
    rw [GeneralCoveringInputNormalization.candidates_eq I cover R hB s hd hC r]
    simpa only [GeneralCoveringInputNormalization.trimmed, if_pos hr] using htask r hr
  exact SmallComponentSetDecision.solved_iff_set _ I _ H.vertices R _ K _ hspec hp hntask v hv

theorem rounds {bits : ℕ} (C : BitCode V bits) (diam a B K : ℕ) (hB : 1 ≤ B) :
    (program C diam a B K hB).rounds = 1 + RecursiveSearch.roundBound diam a K := by
  simp only [program, Program.rounds, GeneralCoveringInputNormalization.rounds,
    GeneralCoveringSearchBudget.rounds, Nat.zero_add]

theorem maxBits {bits : ℕ} (C : BitCode V bits) (diam a B K : ℕ) (hB : 1 ≤ B) :
    (program C diam a B K hB).maxBits ≤ max 1 (3 * bits + RecursiveSearch.extraBits diam a B 1 K) := by
  change max 1 (max 0 (GeneralCoveringSearch.program C diam a B 1 K).maxBits) ≤ _
  rw [Nat.zero_max]
  exact max_le_max (le_refl 1) (GeneralCoveringSearchBudget.maxBits C diam a B 1 K)

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (diam a B K : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C diam a B K hB).maxBits ≤
      (3 * c + RecursiveSearch.extraBits diam a B 1 K + 1) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hc : 1 ≤ 3 * c + RecursiveSearch.extraBits diam a B 1 K + 1 := by omega
  have hs := GeneralCoveringSearchBudget.logarithmic_bits C diam a B 1 K n c hids
  change max 1 (max 0 (GeneralCoveringSearch.program C diam a B 1 K).maxBits) ≤ _
  rw [Nat.zero_max]
  apply max_le
  · exact Nat.mul_le_mul hc hl
  · exact hs.trans (Nat.mul_le_mul (Nat.le_succ _) (le_refl _))

end Paper.NormalizedComponentSearch

#print axioms Paper.NormalizedComponentSearch.run_program_eq_run
#print axioms Paper.NormalizedComponentSearch.normalized_spec
#print axioms Paper.NormalizedComponentSearch.normalized_positive
#print axioms Paper.NormalizedComponentSearch.solved_iff_normalized_set
#print axioms Paper.NormalizedComponentSearch.rounds
#print axioms Paper.NormalizedComponentSearch.logarithmic_bits
