import Paper.Partitions.Local.DeterministicColorReductionLogStar

/-! An actual varying-width broadcast program for the stopped scalar schedule.
Each active stage is Codec.program. A stopped stage is a local identity.
Equality transports reconcile the public width indices without an oracle.
Initial identifier bits are computed locally by a supplied injective BitCode.
The bound is in logStar(input bits); no graph-order or power-simulation claim. -/
namespace Paper.DeterministicColorReductionProgram
open BroadcastModel DeterministicColorReductionArithmetic DeterministicColorReductionLogStar

abbrev Bits := DeterministicColorReductionStep.Bits

theorem logThreshold_le_threshold (Δ : ℕ) : logThreshold Δ ≤ threshold Δ :=
  self_le_two_pow (logThreshold Δ)

theorem active_width_le (b Δ : ℕ) (hb : threshold Δ ≤ b) :
    DeterministicColorReductionCodec.width b Δ ≤ b := by
  have hmul : b ≤ factor Δ * b := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right b (factor_pos Δ)
  have hlarge : 2 ^ (4 * factor Δ) ≤ b := (logThreshold_le_threshold Δ).trans hb
  calc
    DeterministicColorReductionCodec.width b Δ ≤ factor Δ * logStep b := width_le_scaled b Δ
    _ ≤ factor Δ * logStep (factor Δ * b) := Nat.mul_le_mul_left _ (logStep_mono hmul)
    _ ≤ b := scaled_logStep_le (factor Δ) b (factor_pos Δ) hlarge

theorem step_le (Δ b : ℕ) : step Δ b ≤ b := by
  by_cases hb : b < threshold Δ
  · rw [step_small Δ b hb]
  · rw [step_large Δ b (by omega)]
    exact active_width_le b Δ (by omega)

theorem run_le (Δ t b : ℕ) : run Δ t b ≤ b := by
  induction t generalizing b with
  | zero => exact le_rfl
  | succ t ih => exact (ih (step Δ b)).trans (step_le Δ b)

def castBits {m n : ℕ} (h : m = n) (s : Bits m) : Bits n := h ▸ s

theorem castBits_injective {m n : ℕ} (h : m = n) : Function.Injective (castBits h) := by
  cases h
  exact fun _ _ he => he

theorem castBits_ne {m n : ℕ} (h : m = n) (s t : Bits m) (hne : s ≠ t) :
    castBits h s ≠ castBits h t := fun he => hne (castBits_injective h he)

theorem small_width (Δ t b : ℕ) (hb : b < threshold Δ) : b = run Δ (t + 1) b :=
  (run_small Δ (t + 1) b hb).symm

theorem active_width (Δ t b : ℕ) (hb : ¬ b < threshold Δ) :
    run Δ t (DeterministicColorReductionCodec.width b Δ) = run Δ (t + 1) b := by
  change run Δ t (DeterministicColorReductionCodec.width b Δ) = run Δ t (step Δ b)
  rw [step_large Δ b (by omega)]

variable {V : Type} [DecidableEq V]

/-- A computable equality transport of the output type; no extra round. -/
def transport {In : Type} {m n : ℕ} (h : m = n) (P : Program V In (Bits m)) :
    Program V In (Bits n) := h ▸ P

theorem transport_rounds {In : Type} {m n : ℕ} (h : m = n) (P : Program V In (Bits m)) :
    (transport h P).rounds = P.rounds := by cases h; rfl

theorem transport_maxBits {In : Type} {m n : ℕ} (h : m = n) (P : Program V In (Bits m)) :
    (transport h P).maxBits = P.maxBits := by cases h; rfl

def program (Δ : ℕ) : (t b : ℕ) → Program V (Bits b) (Bits (run Δ t b))
  | 0, _ => .local fun _ _ s => s
  | t + 1, b =>
      if hb : b < threshold Δ then
        transport (small_width Δ t b hb) (.local fun _ _ s => s)
      else
        transport (active_width Δ t b hb)
          (.seq (DeterministicColorReductionCodec.program b Δ)
            (program Δ t (DeterministicColorReductionCodec.width b Δ)))

/-- Semantic bit iteration, using only the supplied neighbor map in each update. -/
def colors (N : V → Finset V) (Δ : ℕ) :
    (t b : ℕ) → (V → Bits b) → V → Bits (run Δ t b)
  | 0, _, c => c
  | t + 1, b, c =>
      if hb : b < threshold Δ then
        fun v => castBits (small_width Δ t b hb) (c v)
      else
        fun v => castBits (active_width Δ t b hb)
          (colors N Δ t (DeterministicColorReductionCodec.width b Δ)
            (DeterministicColorReductionCodec.nextColor b Δ N c) v)

theorem rounds (Δ t b : ℕ) : (program (V := V) Δ t b).rounds = usedRounds Δ t b := by
  induction t generalizing b with
  | zero => rfl
  | succ t ih =>
    by_cases hb : b < threshold Δ
    · simp only [program, dif_pos hb, transport_rounds, Program.rounds, usedRounds, if_pos hb]
    · simp only [program, dif_neg hb, transport_rounds, Program.rounds,
        DeterministicColorReductionCodec.rounds, ih, usedRounds, if_neg hb, Nat.add_comm]

theorem maxBits (Δ t b : ℕ) : (program (V := V) Δ t b).maxBits ≤ b := by
  induction t generalizing b with
  | zero => exact Nat.zero_le b
  | succ t ih =>
    by_cases hb : b < threshold Δ
    · simpa only [program, dif_pos hb, transport_maxBits, Program.maxBits] using Nat.zero_le b
    · simpa only [program, dif_neg hb, transport_maxBits, Program.maxBits,
        DeterministicColorReductionCodec.maxBits] using
        max_le (le_refl b) ((ih (DeterministicColorReductionCodec.width b Δ)).trans
          (active_width_le b Δ (by omega)))

/-- Compute one's initial identifier bits locally, then execute the public budget. -/
def fromIdentifiers {b : ℕ} (C : BitCode V b) (Δ : ℕ) :
    Program V Unit (Bits (run Δ (4 * logStar b) b)) :=
  .seq (.local fun v _ _ => C.encode v) (program Δ (4 * logStar b) b)

theorem identifiers_rounds {b : ℕ} (C : BitCode V b) (Δ : ℕ) :
    (fromIdentifiers C Δ).rounds ≤ 4 * logStar b := by
  change 0 + (program (V := V) Δ (4 * logStar b) b).rounds ≤ 4 * logStar b
  rw [Nat.zero_add, rounds]
  exact usedRounds_le Δ _ b

theorem identifiers_maxBits {b : ℕ} (C : BitCode V b) (Δ : ℕ) :
    (fromIdentifiers C Δ).maxBits ≤ b := by
  simpa only [fromIdentifiers, Program.maxBits, Nat.zero_max] using
    maxBits (V := V) Δ (4 * logStar b) b

theorem identifiers_parameters {b : ℕ} (C : BitCode V b) (Δ : ℕ) :
    (fromIdentifiers C Δ).rounds ≤ 4 * logStar b ∧
    (fromIdentifiers C Δ).maxBits ≤ b ∧ run Δ (4 * logStar b) b < threshold Δ :=
  ⟨identifiers_rounds C Δ, identifiers_maxBits C Δ, schedule_small b Δ⟩

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transport_run {In : Type} {m n : ℕ} (h : m = n) (P : Program V In (Bits m))
    (c : V → In) : (transport h P).runEncoded G c =
      fun v => castBits h (P.runEncoded G c v) := by
  cases h
  rfl

theorem correct (Δ t b : ℕ) : ∀ c : V → Bits b,
    (program Δ t b).runEncoded G c = colors (fun v => G.neighborFinset v) Δ t b c := by
  induction t generalizing b with
  | zero => intro c; rfl
  | succ t ih =>
    intro c
    by_cases hb : b < threshold Δ
    · simpa only [program, colors, dif_pos hb] using
        transport_run G (small_width Δ t b hb) (.local fun _ _ s => s) c
    · have hc : (DeterministicColorReductionCodec.program b Δ).runEncoded G c =
          DeterministicColorReductionCodec.nextColor b Δ (fun v => G.neighborFinset v) c :=
        funext (fun v => DeterministicColorReductionCodec.correct G b Δ c v)
      have hi := ih (DeterministicColorReductionCodec.width b Δ)
        ((DeterministicColorReductionCodec.program b Δ).runEncoded G c)
      have hh : (Program.seq (DeterministicColorReductionCodec.program b Δ)
          (program Δ t (DeterministicColorReductionCodec.width b Δ))).runEncoded G c =
          colors (fun v => G.neighborFinset v) Δ t (DeterministicColorReductionCodec.width b Δ)
            (DeterministicColorReductionCodec.nextColor b Δ (fun v => G.neighborFinset v) c) := by
        change (program Δ t (DeterministicColorReductionCodec.width b Δ)).runEncoded G
          ((DeterministicColorReductionCodec.program b Δ).runEncoded G c) = _
        rw [hi, hc]
      have hhcast := congrArg (fun f : V → Bits (run Δ t (DeterministicColorReductionCodec.width b Δ)) =>
        fun v => castBits (active_width Δ t b hb) (f v)) hh
      simpa only [program, colors, dif_neg hb] using
        (transport_run G (active_width Δ t b hb)
          (.seq (DeterministicColorReductionCodec.program b Δ)
            (program Δ t (DeterministicColorReductionCodec.width b Δ))) c).trans hhcast

theorem colors_proper (Δ t b : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    ∀ (c : V → Bits b), (∀ u v, G.Adj u v → c u ≠ c v) →
    ∀ u v, G.Adj u v → colors (fun v => G.neighborFinset v) Δ t b c u ≠
      colors (fun v => G.neighborFinset v) Δ t b c v := by
  induction t generalizing b with
  | zero => intro c hc u v ha; exact hc u v ha
  | succ t ih =>
    intro c hc u v ha
    by_cases hb : b < threshold Δ
    · simpa only [colors, dif_pos hb] using
        castBits_ne (small_width Δ t b hb) (c u) (c v) (hc u v ha)
    · have hn : ∀ u v, G.Adj u v →
          DeterministicColorReductionCodec.nextColor b Δ (fun v => G.neighborFinset v) c u ≠
          DeterministicColorReductionCodec.nextColor b Δ (fun v => G.neighborFinset v) c v := by
        intro u v ha
        simpa only [DeterministicColorReductionCodec.correct] using
          DeterministicColorReductionCodec.proper G b Δ c hdeg hc u v ha
      have hi := ih (DeterministicColorReductionCodec.width b Δ)
        (DeterministicColorReductionCodec.nextColor b Δ (fun v => G.neighborFinset v) c) hn u v ha
      simpa only [colors, dif_neg hb] using
        castBits_ne (active_width Δ t b hb) _ _ hi

theorem proper (Δ t b : ℕ) (c : V → Bits b) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hc : ∀ u v, G.Adj u v → c u ≠ c v) (u v : V) (ha : G.Adj u v) :
    (program Δ t b).runEncoded G c u ≠ (program Δ t b).runEncoded G c v := by
  rw [correct]
  exact colors_proper G Δ t b hdeg c hc u v ha

theorem identifiers_proper {b : ℕ} (C : BitCode V b) (Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u v : V) (ha : G.Adj u v) :
    (fromIdentifiers C Δ).runEncoded G (fun _ => ()) u ≠
      (fromIdentifiers C Δ).runEncoded G (fun _ => ()) v := by
  change (program Δ (4 * logStar b) b).runEncoded G C.encode u ≠
    (program Δ (4 * logStar b) b).runEncoded G C.encode v
  exact proper G Δ (4 * logStar b) b C.encode hdeg
    (fun u v ha => DeterministicColorReductionStep.identifiers_proper G C u v ha) u v ha

end Graph
end Paper.DeterministicColorReductionProgram

#print axioms Paper.DeterministicColorReductionProgram.step_le
#print axioms Paper.DeterministicColorReductionProgram.correct
#print axioms Paper.DeterministicColorReductionProgram.proper
#print axioms Paper.DeterministicColorReductionProgram.rounds
#print axioms Paper.DeterministicColorReductionProgram.maxBits
#print axioms Paper.DeterministicColorReductionProgram.identifiers_proper
#print axioms Paper.DeterministicColorReductionProgram.identifiers_parameters
