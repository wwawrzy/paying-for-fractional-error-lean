import Paper.Communication.CurrentThresholdProgram
import Paper.Endpoints.Rounding.NoncriticalRationalParameters
import Paper.Communication.CappedWholeProgram
import Paper.Averaging.Tasks.KT0Compiler

/-!
Actual current noninteger rounding, independently of a fractional solver.
All vertices are candidates and demands; the comparison cost is 2a+1.
The first threshold is precisely 1/(a+1), rather than the older adjustable
NoncriticalParameters.threshold. If k < 2a < k+1, the second threshold is
the integer count k+2. Three broadcasts carry one bit each.

The public threshold is encoded by natural numbers h,m. Rational a admits
such an encoding before any graph or fractional input is supplied. Optional
composition with any actual fractional program and KT0 startup is explicit;
the statements about rounding and Theorem B require no fractional solver.
-/

namespace Paper.CurrentNonintegerProgram

open BroadcastModel SevenFoundation
open RatioCriticalRoundingProgram (State removeFirst selectHigh removeHigh)

section Programs

variable {V : Type} [DecidableEq V]

def start (m h D N : ℕ) : Program V (Fin N) State :=
  .local fun _ _ p => ⟨true, true, decide (h * D < m * p.val), false, false, false⟩

def program (k m h D N : ℕ) : Program V (Fin N) Bool :=
  .seq (start m h D N)
    (.seq removeFirst (.seq (selectHigh (k + 1)) (.seq removeHigh
      (.local fun _ _ st => st.first || st.high || st.last))))

theorem rounds (k m h D N : ℕ) : (program (V := V) k m h D N).rounds = 3 := rfl

theorem maxBits (k m h D N : ℕ) : (program (V := V) k m h D N).maxBits = 1 := rfl

/-- KT0 rounding when a numerator is already supplied as private input. -/
def portProgram {b : ℕ} (C : BitCode V b) (k m h D N : ℕ) :
    PortBroadcastModel.Program V (Fin N) Bool :=
  KT0Compiler.program C (program k m h D N)

theorem port_rounds {b : ℕ} (C : BitCode V b) (k m h D N : ℕ) :
    (portProgram C k m h D N).rounds = 4 := by
  rw [portProgram, KT0Compiler.program_rounds, rounds]

theorem port_maxBits {b : ℕ} (C : BitCode V b) (k m h D N : ℕ) :
    (portProgram C k m h D N).maxBits = max b 1 := by
  rw [portProgram, KT0Compiler.program_maxBits, maxBits]

/-- Optional composition with any actual fractional program. No accuracy
or optimality property of that program is needed to define the code. -/
def withFractional (k m h D N : ℕ) (P : Program V Unit (Fin N)) : Program V Unit Bool :=
  .seq P (program k m h D N)

theorem withFractional_rounds (k m h D N : ℕ) (P : Program V Unit (Fin N)) :
    (withFractional k m h D N P).rounds = P.rounds + 3 := by
  rw [withFractional, Program.rounds, rounds]

theorem withFractional_maxBits (k m h D N : ℕ) (P : Program V Unit (Fin N)) :
    (withFractional k m h D N P).maxBits = max P.maxBits 1 := by
  rw [withFractional, Program.maxBits, maxBits]

def withFractionalKT0 {b : ℕ} (C : BitCode V b) (k m h D N : ℕ)
    (P : Program V Unit (Fin N)) : PortBroadcastModel.Program V Unit Bool :=
  KT0Compiler.program C (withFractional k m h D N P)

theorem withFractionalKT0_rounds {b : ℕ} (C : BitCode V b) (k m h D N : ℕ)
    (P : Program V Unit (Fin N)) :
    (withFractionalKT0 C k m h D N P).rounds = P.rounds + 4 := by
  rw [withFractionalKT0, KT0Compiler.program_rounds, withFractional_rounds]
  omega

theorem withFractionalKT0_maxBits {b : ℕ} (C : BitCode V b) (k m h D N : ℕ)
    (P : Program V Unit (Fin N)) :
    (withFractionalKT0 C k m h D N P).maxBits = max b (max P.maxBits 1) := by
  rw [withFractionalKT0, KT0Compiler.program_maxBits, withFractional_maxBits]

theorem port_logarithmic_bits {b : ℕ} (C : BitCode V b) (k m h D N n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (portProgram C k m h D N).maxBits ≤ max c 1 * Nat.clog 2 (n + 2) := by
  rw [port_maxBits]
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  exact (max_le_max hids (by simpa only [Nat.one_mul] using hl)).trans_eq
    (by simpa only [Nat.one_mul] using max_mul_mul_right c 1 (Nat.clog 2 (n + 2)))

theorem withFractionalKT0_logarithmic_bits [Fintype V] {b : ℕ} (C : BitCode V b)
    (k m h D N : ℕ) (P : Program V Unit (Fin N)) (n c K : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2))
    (hmsg : P.maxBits ≤ K * Nat.clog 2 (n + 2)) :
    (withFractionalKT0 C k m h D N P).maxBits ≤
      max c (max K 1) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hp : (withFractional k m h D N P).maxBits ≤
      max K 1 * Nat.clog 2 (n + 2) := by
    rw [withFractional_maxBits]
    exact (max_le_max hmsg (by simpa only [Nat.one_mul] using hl)).trans_eq
      (by simpa only [Nat.one_mul] using max_mul_mul_right K 1 (Nat.clog 2 (n + 2)))
  exact KT0Compiler.logarithmic_bits C _ n c _ hids hp

end Programs

section Semantics

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The exact current uniform-cost input: F is empty and C=R0=V. -/
noncomputable def input (a : ℝ) (ha : 1 ≤ a) (x : V → ℝ)
    (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1) :
    CurrentRounding.Input G a where
  candidates := Finset.univ
  demands := Finset.univ
  demands_subset := Finset.Subset.refl _
  c := fun _ => 2 * a + 1
  x := x
  cost_pos := by intro v _; linarith
  cost_le := by intro v _; exact le_rfl
  nonneg := by intro v _; exact hx.1 v
  cap := by intro v _; exact hcap v
  coverage := by
    intro r hr
    simpa only [Finset.inter_univ] using hx.2 r hr

theorem objective_eq (a : ℝ) (ha : 1 ≤ a) (x : V → ℝ)
    (hx : PartialOptimum.Feasible G Finset.univ x) (hcap : ∀ v, x v ≤ 1) :
    CurrentRounding.objective G a (input G a ha x hx hcap) =
      (2 * a + 1) * ∑ v, x v := by
  change (∑ v, (2 * a + 1) * x v) = _
  exact (Finset.mul_sum _ _ _).symm

/-- A closed-neighborhood count is integral; this is the exact second
threshold, including the gap on both sides of 2a. -/
theorem high_threshold (a : ℝ) (k : ℕ) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ)) (n : ℕ) :
    k + 1 + 1 ≤ n ↔ 2 * a + 1 ≤ (n : ℝ) := by
  constructor
  · intro hn
    have hnR : ((k + 1 + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at hnR hk1
    linarith
  · intro hn
    by_contra hnot
    have hnN : n ≤ k + 1 := by omega
    have hnR : (n : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hnN
    push_cast at hnR
    linarith

theorem start_correct (m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (a : ℝ) (ha : 1 ≤ a) (hratio : (h : ℝ) / m = 1 / (a + 1))
    (p : V → Fin N)
    (hx : PartialOptimum.Feasible G Finset.univ (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v, ((p v).val : ℝ) / D ≤ 1) :
    (start m h D N).run G p = CurrentThresholdProgram.expected G a
      (input G a ha (fun v => ((p v).val : ℝ) / D) hx hcap) 0 := by
  funext v
  apply State.ext <;>
    simp [start, Program.run, CurrentThresholdProgram.expected, input,
      CurrentRounding.first, RatioCriticalRoundingProgram.threshold m h _ D hm hD, hratio]

/-- The reused second broadcast is correct for arbitrary current input
data; only the gap between consecutive integer degrees is specialized. -/
theorem selectHigh_correct (a : ℝ) (k : ℕ) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ)) (I : CurrentRounding.Input G a) :
    (selectHigh (k + 1)).run G (CurrentThresholdProgram.expected G a I 1) =
      CurrentThresholdProgram.expected G a I 2 := by
  rw [RatioCriticalRoundingProgram.selectHigh,
    ObserveProgram.run G _ _ _ (CurrentRounding.residual G a I) (by rfl)]
  funext v
  apply State.ext <;> try rfl
  have hn := high_threshold a k hk hk1
    (closed G v ∩ CurrentRounding.residual G a I).card
  apply Bool.eq_iff_iff.mpr
  simp [CurrentThresholdProgram.expected, CurrentRounding.high, CurrentRounding.hits, hn]

theorem correct (k m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (a : ℝ) (ha : 1 ≤ a) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ))
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (p : V → Fin N)
    (hx : PartialOptimum.Feasible G Finset.univ (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v, ((p v).val : ℝ) / D ≤ 1) :
    (program k m h D N).run G p = fun v => decide (v ∈ CurrentRounding.output G a
      (input G a ha (fun u => ((p u).val : ℝ) / D) hx hcap)) := by
  change (fun v => let st := removeHigh.run G ((selectHigh (k + 1)).run G
    (removeFirst.run G ((start m h D N).run G p))) v;
    st.first || st.high || st.last) = _
  rw [start_correct G m h D N hm hD a ha hratio p hx hcap,
    CurrentThresholdProgram.removeFirst_correct,
    selectHigh_correct G a k hk hk1, CurrentThresholdProgram.removeHigh_correct]
  funext v
  apply Bool.eq_iff_iff.mpr
  simp [CurrentThresholdProgram.expected, CurrentRounding.output, or_assoc]

theorem encoded_correct (k m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (a : ℝ) (ha : 1 ≤ a) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ))
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (p : V → Fin N)
    (hx : PartialOptimum.Feasible G Finset.univ (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v, ((p v).val : ℝ) / D ≤ 1) :
    (program k m h D N).runEncoded G p = fun v => decide (v ∈ CurrentRounding.output G a
      (input G a ha (fun u => ((p u).val : ℝ) / D) hx hcap)) := by
  rw [Program.runEncoded_eq_run]
  exact correct G k m h D N hm hD a ha hk hk1 hratio p hx hcap

def output (k m h D N : ℕ) (p : V → Fin N) : Finset V :=
  Finset.univ.filter (fun v => (program k m h D N).runEncoded G p v)

theorem output_eq (k m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (a : ℝ) (ha : 1 ≤ a) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ))
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (p : V → Fin N)
    (hx : PartialOptimum.Feasible G Finset.univ (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v, ((p v).val : ℝ) / D ≤ 1) :
    output G k m h D N p = CurrentRounding.output G a
      (input G a ha (fun u => ((p u).val : ℝ) / D) hx hcap) := by
  unfold output
  rw [encoded_correct G k m h D N hm hD a ha hk hk1 hratio p hx hcap]
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

theorem port_encoded_correct (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (C : BitCode V b) (k m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (a : ℝ) (ha : 1 ≤ a) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ))
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (p : V → Fin N)
    (hx : PartialOptimum.Feasible G Finset.univ (fun v => ((p v).val : ℝ) / D))
    (hcap : ∀ v, ((p v).val : ℝ) / D ≤ 1) :
    (portProgram C k m h D N).runEncoded G ports p =
      fun v => decide (v ∈ CurrentRounding.output G a
        (input G a ha (fun u => ((p u).val : ℝ) / D) hx hcap)) := by
  rw [portProgram, KT0Compiler.program_encoded_correct]
  exact encoded_correct G k m h D N hm hD a ha hk hk1 hratio p hx hcap

/-- Composition semantics uses only feasibility and a cap; it assumes no
LP accuracy or target approximation inequality. -/
theorem withFractional_encoded_correct (k m h D N : ℕ) (hm : 0 < m) (hD : 0 < D)
    (a : ℝ) (ha : 1 ≤ a) (hk : (k : ℝ) < 2 * a)
    (hk1 : 2 * a < ((k + 1 : ℕ) : ℝ))
    (hratio : (h : ℝ) / m = 1 / (a + 1)) (P : Program V Unit (Fin N))
    (hx : PartialOptimum.Feasible G Finset.univ
      (fun v => (((P.runEncoded G (fun _ => ())) v).val : ℝ) / D))
    (hcap : ∀ v, (((P.runEncoded G (fun _ => ())) v).val : ℝ) / D ≤ 1) :
    (withFractional k m h D N P).runEncoded G (fun _ => ()) =
      fun v => decide (v ∈ CurrentRounding.output G a
        (input G a ha (fun u => (((P.runEncoded G (fun _ => ())) u).val : ℝ) / D) hx hcap)) := by
  change (program k m h D N).runEncoded G (P.runEncoded G (fun _ => ())) = _
  exact encoded_correct G k m h D N hm hD a ha hk hk1 hratio _ hx hcap

end Semantics

/-- Natural public encodings for the current threshold, with no graph or
solver in the parameter choice. The integer floor is also fixed publicly. -/
theorem rational_parameters (a : ℚ) (ha : 1 ≤ a)
    (hnoninteger : ¬ ∃ z : ℤ, (z : ℚ) = 2 * a) :
    ∃ k m h : ℕ, 0 < m ∧ (k : ℝ) < 2 * (a : ℝ) ∧
      2 * (a : ℝ) < ((k + 1 : ℕ) : ℝ) ∧
      (h : ℝ) / m = 1 / ((a : ℝ) + 1) := by
  let k := ⌊2 * a⌋₊
  have hk : (k : ℚ) ≤ 2 * a := Nat.floor_le (by linarith)
  have hk1 : 2 * a < (k + 1 : ℕ) := by
    exact_mod_cast Nat.lt_floor_add_one (2 * a)
  have hkne : (k : ℚ) ≠ 2 * a := by
    intro he
    apply hnoninteger
    refine ⟨(k : ℤ), ?_⟩
    exact_mod_cast he
  have hkl : (k : ℚ) < 2 * a := lt_of_le_of_ne hk hkne
  have hap : (0 : ℚ) < a + 1 := by linarith
  have hσ : (0 : ℚ) ≤ 1 / (a + 1) := (div_pos zero_lt_one hap).le
  obtain ⟨m, h, hm, hratio⟩ := NoncriticalRationalParameters.natural_ratio (1 / (a + 1)) hσ
  refine ⟨k, m, h, hm, ?_, ?_, ?_⟩
  · exact_mod_cast hkl
  · exact_mod_cast hk1
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add] using hratio

end Paper.CurrentNonintegerProgram
