import Paper.Endpoints.Rounding.GeneralCriticalBroadcast
import Paper.Endpoints.Rounding.GeneralNoncriticalBroadcast

/-! Uniform exact (2a+1) approximation for every fixed rational a>=1.
This endpoint uses KT1, with neighbor identifiers initially known. The
separate KT0 initialization theorem is required for any KT0 round claim. -/
namespace Paper.MinorDensityBroadcast
open BroadcastModel SevenFoundation

structure Config where
  critical : Bool
  degree : ℕ
  thresholdDen : ℕ
  thresholdNum : ℕ
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

variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (p : Config) : Program V Unit Bool :=
  if p.critical then GeneralCriticalBroadcast.program C p.A p.degree p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos
  else GeneralNoncriticalBroadcast.program C p.degree p.thresholdDen p.thresholdNum
    p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos

def roundBound (p : Config) : ℕ :=
  if p.critical then GeneralCriticalBroadcast.roundBound p.A p.r p.k p.T p.M
  else GeneralNoncriticalBroadcast.roundBound p.A p.r p.k p.T p.M

def messageConstant (p : Config) (c : ℕ) : ℕ :=
  if p.critical then GeneralCriticalBroadcast.messageConstant p.A p.degree p.L p.Δ p.r p.k p.Q p.T p.s p.q p.M c
  else GeneralNoncriticalBroadcast.messageConstant p.A p.L p.Δ p.r p.k p.Q p.T p.s p.q p.M c

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {b : ℕ} (C : BitCode V b) (p : Config) : Finset V :=
  Finset.univ.filter (fun v => (program C p).runEncoded G (fun _ => ()) v)

theorem output_critical {b : ℕ} (C : BitCode V b) (p : Config) (hp : p.critical = true) :
    output G C p = GeneralCriticalBroadcast.output G C p.A p.degree p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos := by
  unfold output program
  rw [hp]
  rfl

theorem output_noncritical {b : ℕ} (C : BitCode V b) (p : Config) (hp : p.critical = false) :
    output G C p = GeneralNoncriticalBroadcast.output G C p.degree p.thresholdDen p.thresholdNum
      p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s p.q p.M p.Q_pos := by
  unfold output program
  rw [hp]
  rfl

theorem rounds {b : ℕ} (C : BitCode V b) (p : Config) : (program C p).rounds = roundBound p := by
  cases hp : p.critical <;> simp only [program, roundBound, hp, Bool.false_eq_true,
    Bool.true_eq, if_false, if_true, GeneralCriticalBroadcast.rounds, GeneralNoncriticalBroadcast.rounds]

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (p : Config) (n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n + 2) := by
  cases hp : p.critical
  · simp only [program, messageConstant, hp, Bool.false_eq_true, if_false]
    exact GeneralNoncriticalBroadcast.logarithmic_bits C _ _ _ _ _ _ _ _ _ _ _ _ _ _ p.Q_pos n c hids
  · simp only [program, messageConstant, hp, Bool.true_eq, if_true]
    exact GeneralCriticalBroadcast.logarithmic_bits C _ _ _ _ _ _ _ _ _ _ _ _ p.Q_pos n c hids

set_option maxHeartbeats 1000000 in
theorem exact_minor_density (a : ℚ) (ha : 1 ≤ a) :
    ∃ p : Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ {b : ℕ} (C : BitCode V b),
        dominates G (output G C p) ∧ ((output G C p).card : ℝ) ≤ (2 * (a : ℝ) + 1) * fractionalNumber G ∧
          (program C p).rounds = roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n + 2) := by
  let d := ⌊2 * a⌋₊
  have hd : (d : ℚ) ≤ 2 * a := Nat.floor_le (by linarith)
  have hd1 : 2 * a < (d + 1 : ℕ) := by exact_mod_cast Nat.lt_floor_add_one (2 * a)
  by_cases hc : (d : ℚ) = 2 * a
  · have hdR : (d : ℝ) = 2 * (a : ℝ) := by exact_mod_cast hc
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
      GeneralCriticalBroadcast.exact_critical (a : ℝ) haR d hdR
    let p : Config := ⟨true, d, 1, 1, A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq⟩
    refine ⟨p, ?_⟩
    intro V _ _ G _ hden b C
    have h := hrun G hden C
    refine ⟨?_, ?_, rounds C p, fun n c hids => logarithmic_bits C p n c hids⟩
    · rw [output_critical G C p rfl]
      exact h.1
    · rw [output_critical G C p rfl]
      exact h.2.1
  · have hdlt : (d : ℚ) < 2 * a := lt_of_le_of_ne hd hc
    obtain ⟨m, h, A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
      GeneralNoncriticalBroadcast.exact_noncritical a ha d hdlt hd1
    let p : Config := ⟨false, d, m, h, A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq⟩
    refine ⟨p, ?_⟩
    intro V _ _ G _ hden b C
    have hs := hrun G hden C
    refine ⟨?_, ?_, rounds C p, fun n c hids => logarithmic_bits C p n c hids⟩
    · rw [output_noncritical G C p rfl]
      exact hs.1
    · rw [output_noncritical G C p rfl]
      exact hs.2.1

end Paper.MinorDensityBroadcast
