import Paper.Endpoints.Rounding.MinorDensityBroadcast
import Paper.Averaging.Tasks.KT0Compiler
import Paper.Preliminaries.PlanarDensity

/-! S13 startup bridge for the actual exact-density algorithm. KT0 code
receives no neighbor IDs; a first own-ID broadcast supplies the port table.
For every physical port numbering, the encoded selected set equals KT1. -/
namespace Paper.MinorDensityKT0
open BroadcastModel (BitCode)
open SevenFoundation
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (p : MinorDensityBroadcast.Config) :
    PortBroadcastModel.Program V Unit Bool := KT0Compiler.program C (MinorDensityBroadcast.program C p)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b)
    (p : MinorDensityBroadcast.Config) : Finset V :=
  Finset.univ.filter (fun v => (program C p).runEncoded G ports (fun _ => ()) v)

theorem output_eq (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b)
    (p : MinorDensityBroadcast.Config) : output G ports C p = MinorDensityBroadcast.output G C p := by
  unfold output program
  rw [KT0Compiler.program_encoded_correct]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (p : MinorDensityBroadcast.Config) :
    (program C p).rounds = 1 + MinorDensityBroadcast.roundBound p := by
  rw [program, KT0Compiler.program_rounds, MinorDensityBroadcast.rounds]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (p : MinorDensityBroadcast.Config)
    (n c : ℕ) (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C p).maxBits ≤ max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) :=
  KT0Compiler.logarithmic_bits C (MinorDensityBroadcast.program C p) n c _ hids
    (MinorDensityBroadcast.logarithmic_bits C p n c hids)

theorem exact_minor_density (a : ℚ) (ha : 1 ≤ a) :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ (ports : PortBroadcastModel.Numbering G)
          {b : ℕ} (C : BitCode V b),
        dominates G (output G ports C p) ∧
          ((output G ports C p).card : ℝ) ≤ (2 * (a : ℝ) + 1) * fractionalNumber G ∧
          (program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C p).maxBits ≤ max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  obtain ⟨p, hp⟩ := MinorDensityBroadcast.exact_minor_density a ha
  refine ⟨p, ?_⟩
  intro V _ _ G _ hden ports b C
  have h := hp G hden C
  rw [output_eq]
  exact ⟨h.1, h.2.1, rounds C p, fun n c hids => logarithmic_bits C p n c hids⟩

theorem exact_planar :
    ∃ p : MinorDensityBroadcast.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        dominates G (output G ports C p) ∧ ((output G ports C p).card : ℝ) ≤ 7 * fractionalNumber G ∧
          (program C p).rounds = 1 + MinorDensityBroadcast.roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C p).maxBits ≤ max c (MinorDensityBroadcast.messageConstant p c) * Nat.clog 2 (n + 2) := by
  obtain ⟨p, hp⟩ := exact_minor_density (3 : ℚ) (by norm_num)
  refine ⟨p, ?_⟩
  intro V _ _ G _ hG ports b C
  have h := hp G (PlanarDensity.minor_density G hG) ports C
  norm_num only [Rat.cast_ofNat, mul_add, mul_one, Nat.reduceMul, Nat.reduceAdd] at h
  exact h

end Paper.MinorDensityKT0
