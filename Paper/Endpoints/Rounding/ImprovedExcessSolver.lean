import Paper.Communication.CappedWholeProgram
import Paper.Endpoints.Rounding.ImprovedExcessEndpoint
import Paper.Endpoints.Rounding.ImprovedExcessMaximumGain

/-! A uniform capped fractional solver followed by the exact unfiltered
improved rounding. Only public constants enter the program. The solver's
natural numerator is projected locally using its unchanged denominator. -/
namespace Paper.ImprovedExcessSolver
open BroadcastModel SevenFoundation
open scoped BigOperators

structure Config (a : ℚ) where
  mu : ℚ
  A : ℕ
  L : ℕ
  Δ : ℕ
  r : ℕ
  k : ℕ
  t : ℕ
  Q : ℕ
  T : ℕ
  s : ℕ
  q : ℕ
  M : ℕ
  Q_pos : 0 < Q
  q_pos : 0 < q

def denominator {a : ℚ} (p : Config a) : ℕ :=
  PartialFractionalProgram.denominator p.Δ p.k p.Q p.T p.s p.q

noncomputable def threshold {a : ℚ} (p : Config a) : ℝ :=
  ImprovedExcess.threshold (a : ℝ) (ImprovedExcessEndpoint.gap a) (p.mu : ℝ)

def roundBound {a : ℚ} (p : Config a) : ℕ :=
  (2 * p.A) * (4 + 2 * GeneralInitBroadcast.rank p.A) +
    (34 + 4 * OwnerBoundaryMean.radius p.k p.T + 4 * p.r +
      RecursiveSearch.roundBound (4 * p.k) p.A p.M) + 3

def messageConstant {a : ℚ} (p : Config a) (c : ℕ) : ℕ :=
  max (1 + GeneralInitBroadcast.rank p.A * (c + 1))
    (PartialFractionalBudget.constant p.L p.Δ p.r p.k p.Q p.T p.s p.A 1 p.q p.M c) + 1

variable {V : Type} [LinearOrder V]

noncomputable def program {a : ℚ} {b : ℕ} (C : BitCode V b) (p : Config a) :
    Program V Unit Bool :=
  .seq (CappedWholeProgram.program C p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos)
    (.seq (.local fun _ _ state => (state.val : ℝ) / denominator p)
      (ImprovedExcessProgram.program (ImprovedExcessEndpoint.cutoff a) (threshold p)))

variable [Fintype V]

theorem rounds {a : ℚ} {b : ℕ} (C : BitCode V b) (p : Config a) :
    (program C p).rounds = roundBound p := by
  change (CappedWholeProgram.program C p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos).rounds +
    (0 + (ImprovedExcessProgram.program (V := V) (ImprovedExcessEndpoint.cutoff a) (threshold p)).rounds) = _
  rw [CappedWholeProgram.rounds, ImprovedExcessProgram.rounds]
  rfl

theorem logarithmic_bits {a : ℚ} {b : ℕ} (C : BitCode V b) (p : Config a)
    (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n + 2) := by
  have hp := GeneralFractionalBroadcast.logarithmic_bits C
    p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s 1 p.q p.M p.Q_pos n c hids
  change max (CappedWholeProgram.program C p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos).maxBits
    (max 0 (ImprovedExcessProgram.program (V := V) (ImprovedExcessEndpoint.cutoff a) (threshold p)).maxBits) ≤ _
  rw [CappedWholeProgram.maxBits, ImprovedExcessProgram.maxBits, Nat.zero_max]
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  unfold messageConstant
  apply max_le <;> nlinarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def solution {a : ℚ} {b : ℕ} (C : BitCode V b) (p : Config a) (v : V) : ℝ :=
  (((CappedWholeProgram.program C p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos).run G
    (fun _ => ()) v).val : ℝ) / denominator p

noncomputable def output {a : ℚ} {b : ℕ} (C : BitCode V b) (p : Config a) : Finset V :=
  Finset.univ.filter fun v => (program C p).runEncoded G (fun _ => ()) v

theorem output_eq {a : ℚ} {b : ℕ} (C : BitCode V b) (p : Config a) :
    output G C p = ImprovedExcessEndpoint.selected G (ImprovedExcessEndpoint.cutoff a)
      (threshold p) (solution G C p) := by
  unfold output ImprovedExcessEndpoint.selected
  simp only [Program.runEncoded_eq_run, program, Program.run]
  rfl

set_option maxHeartbeats 1000000 in
/-- The target may be at or above 2a+1. A strictly positive rational gain
and the exact compensating real solver accuracy are chosen before the graph. -/
theorem parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) (c : ℝ)
    (hc : 2 * (a : ℝ) + 1 - ImprovedExcess.muMax (a : ℝ) (ImprovedExcessEndpoint.gap a) < c) :
    ∃ p : Config a,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G 3 → Incidence.InducedDensityBound G (a : ℝ) →
        ∀ {b : ℕ} (C : BitCode V b), dominates G (output G C p) ∧
          ((output G C p).card : ℝ) ≤ c * fractionalNumber G ∧
          (program C p).rounds = roundBound p ∧
          ∀ n d, b ≤ d * Nat.clog 2 (n + 2) →
            (program C p).maxBits ≤ messageConstant p d * Nat.clog 2 (n + 2) := by
  obtain ⟨hzero, hone⟩ := ImprovedExcessEndpoint.gap_bounds a ha hnoninteger
  have haR : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have hmax := ImprovedExcess.muMax_pos (a : ℝ) (ImprovedExcessEndpoint.gap a) haR hzero hone
  have hbelow : max 0 (2 * (a : ℝ) + 1 - c) <
      ImprovedExcess.muMax (a : ℝ) (ImprovedExcessEndpoint.gap a) :=
    max_lt hmax (by linarith)
  obtain ⟨mu, hmu, hlo, hhi⟩ := ImprovedExcess.exists_rational_mu_above
    (a : ℝ) (ImprovedExcessEndpoint.gap a) (max 0 (2 * (a : ℝ) + 1 - c))
    (le_max_left _ _) hbelow
  have hmuR : (0 : ℝ) < mu := by exact_mod_cast hmu
  obtain ⟨hmutheta, hadm⟩ := (ImprovedExcess.admissible_iff_le_muMax
    (a : ℝ) (ImprovedExcessEndpoint.gap a) (mu : ℝ) haR hzero hone hmuR.le).mpr hhi.le
  have hpos : 0 < 2 * (a : ℝ) + 1 - (mu : ℝ) := by linarith
  have hlt : 2 * (a : ℝ) + 1 - (mu : ℝ) < c := by
    have hh := (le_max_right 0 (2 * (a : ℝ) + 1 - c)).trans_lt hlo
    linarith
  let delta := (c - (2 * (a : ℝ) + 1 - (mu : ℝ))) / (2 * (a : ℝ) + 1 - (mu : ℝ))
  have hdelta : 0 < delta := div_pos (sub_pos.mpr hlt) hpos
  have hcancel : (2 * (a : ℝ) + 1 - (mu : ℝ)) * (1 + delta) = c := by
    dsimp only [delta]
    field_simp [ne_of_gt hpos]; ring
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
    CappedWholeProgram.parameters (3 : ℝ) (by norm_num) delta hdelta
  let p : Config a := ⟨mu, A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq⟩
  refine ⟨p, ?_⟩
  intro V _ _ G _ hminor hden b C
  obtain ⟨hy, hcap, hmass⟩ := hrun G hminor C
  have hd : ImprovedExcess.DensityWithExcess G (a : ℝ) 0 := by
    intro S
    simpa only [add_zero] using hden S
  have hr := ImprovedExcessEndpoint.rounding G a mu 0 ha hnoninteger hmu.le
    hmutheta le_rfl hadm hd (solution G C p) hy hcap
  rw [output_eq]
  refine ⟨hr.1, ?_, rounds C p, fun n d hids => logarithmic_bits C p n d hids⟩
  have hbnd : ((ImprovedExcessEndpoint.selected G (ImprovedExcessEndpoint.cutoff a)
      (threshold p) (solution G C p)).card : ℝ) ≤
      (2 * (a : ℝ) + 1 - (mu : ℝ)) * (∑ v, solution G C p v) := by
    simpa only [mul_zero, zero_mul, add_zero] using hr.2.1
  calc
    _ ≤ (2 * (a : ℝ) + 1 - (mu : ℝ)) * (∑ v, solution G C p v) := hbnd
    _ ≤ (2 * (a : ℝ) + 1 - (mu : ℝ)) * ((1 + delta) * fractionalNumber G) :=
      mul_le_mul_of_nonneg_left hmass hpos.le
    _ = c * fractionalNumber G := by rw [← mul_assoc, hcancel]

end Paper.ImprovedExcessSolver
#print axioms Paper.ImprovedExcessSolver.output_eq
#print axioms Paper.ImprovedExcessSolver.rounds
#print axioms Paper.ImprovedExcessSolver.logarithmic_bits
#print axioms Paper.ImprovedExcessSolver.parameters
