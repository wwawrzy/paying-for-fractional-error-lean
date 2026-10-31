import Paper.Initialization.Pruning.InitializerBroadcast
import Paper.Initialization.Pruning.FullInitialization

/-! Genuine initializer for every fixed integer minor-density bound.
Its public parameters are computed in natural arithmetic only. -/
namespace Paper.GeneralInitBroadcast
open BroadcastModel SevenFoundation
open scoped BigOperators

def rank (A : ℕ) : ℕ := ActualInitialization.listThreshold (2 * A) (2 * A)
def threshold (A : ℕ) : ℕ := ActualInitialization.candidateThreshold (2 * A) (2 * A)
def parameter (A : ℕ) : ℕ := A * (2 ^ rank A + 1) ^ 4 + (2 ^ rank A + 1) + 1

theorem parameter_pos (A : ℕ) : 1 ≤ parameter A :=
  Nat.le_add_left 1 (A * (2 ^ rank A + 1) ^ 4 + (2 ^ rank A + 1))

theorem parameter_eq (A : ℕ) : parameter A = FullInitialization.listParameter (A : ℝ) (rank A) := by
  let N := 2 ^ rank A + 1
  change A * N ^ 4 + N + 1 = ⌈(A : ℝ) * (N : ℝ) ^ 4 + (N : ℝ)⌉₊ + 1
  have he : (A : ℝ) * (N : ℝ) ^ 4 + (N : ℝ) = ((A * N ^ 4 + N : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, Nat.ceil_natCast]

noncomputable def constant (A : ℕ) : ℝ :=
  (InitializationCost.constant (parameter A) (2 * A) (2 * A) : ℝ) * (2 * (2 * (A : ℝ)) + 1)

theorem constant_nonneg (A : ℕ) : 0 ≤ constant A := by unfold constant; positivity

variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (A : ℕ) : Program V Bool Bool :=
  InitializerBroadcast.program C (parameter A) (threshold A) (rank A) (2 * A)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b : ℕ} (C : BitCode V b) (A : ℕ) (R : Finset V) : Finset V :=
  Finset.univ.filter (fun v => (program C A).run G (fun u => decide (u ∈ R)) v)

theorem output_eq {b : ℕ} (C : BitCode V b) (A : ℕ) (R : Finset V) :
    output G C A R = InitializationCost.output G (parameter A) (2 * A) (2 * A) R := by
  ext v
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and, program,
    InitializerBroadcast.correct G C (parameter A) (threshold A) (rank A) (2 * A) (parameter_pos A) R,
    decide_eq_true_eq]
  unfold InitializationCost.output
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst]
  rfl

theorem spec {b : ℕ} (C : BitCode V b) (A : ℕ) (hA : 1 ≤ A)
    (hden : MinorDensity.Bound G (A : ℝ)) (R : Finset V) (w x : V → ℝ)
    (hw : ∀ v, 1 ≤ w v) (hx : ∀ v, 0 ≤ x v) (hcover : ∀ r ∈ R, 1 ≤ ∑ v ∈ closed G r, x v) :
    R ⊆ covered G (output G C A R) ∧ ((output G C A R).card : ℝ) ≤ constant A * ∑ v, w v * x v := by
  have h := @FullInitialization.weighted_spec V (inferInstance : Fintype V) (inferInstance : LinearOrder V)
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at h
  have hs := h G (2 * A) (2 * A) (by omega) (by omega) (Nat.cast_nonneg A)
    (by push_cast; rfl) (by push_cast; rfl) hden R w x hw hx hcover
  rw [output_eq]
  dsimp only at hs
  have hp := parameter_eq A
  dsimp only [rank] at hp
  rw [← hp] at hs
  convert hs using 1 <;> simp only [constant, Nat.cast_mul, Nat.cast_ofNat]

theorem rounds {b : ℕ} (C : BitCode V b) (A : ℕ) :
    (program C A).rounds = (2 * A) * (4 + 2 * rank A) :=
  InitializerBroadcast.rounds C (parameter A) (threshold A) (rank A) (2 * A)

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (A n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C A).maxBits ≤ (1 + rank A * (c + 1)) * Nat.clog 2 (n + 2) :=
  InitializerBroadcast.logarithmic_bits C (parameter A) (threshold A) (rank A) (2 * A) n c hids

end Paper.GeneralInitBroadcast
