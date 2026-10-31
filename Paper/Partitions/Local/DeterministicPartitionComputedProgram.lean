import Paper.Partitions.Local.DeterministicColorReductionPhysicalProgram
import Paper.Partitions.Local.DeterministicPartitionIterationProgram
import Paper.Preliminaries.FiniteWordCode

/-! A public finite palette and the actual partition entry program.
The palette depends only on Delta,k. Binary words are numbered by the explicit
FiniteWordCode.words equivalence, then zero-extended by retaining their value
in the larger Fin. No one-hot word codec or abstract finite enumeration is used.
Initial active bits are private memory through physical identifier coloring.
The executable input contains no supplied coloring or power-neighbor oracle. -/
namespace Paper.DeterministicPartitionComputedProgram
open BroadcastModel DeterministicColorReductionArithmetic DeterministicColorReductionLogStar
variable {V : Type} [LinearOrder V]

abbrev powerDegree (Δ k : ℕ) : ℕ := (Δ + 1) ^ (2 * k)

def terminalWidth (Δ k ids : ℕ) : ℕ := run (powerDegree Δ k) (4 * logStar ids) ids

def palette (Δ k : ℕ) : ℕ := 2 ^ threshold (powerDegree Δ k)

theorem terminal_lt (Δ k ids : ℕ) : terminalWidth Δ k ids < threshold (powerDegree Δ k) :=
  schedule_small ids (powerDegree Δ k)

theorem palette_pos (Δ k : ℕ) : 0 < palette Δ k := Nat.two_pow_pos _

/-- Actual computable binary numbering, using two symbols rather than one-hot words. -/
def number (w : ℕ) (s : DeterministicColorReductionStep.Bits w) : Fin (2 ^ w) :=
  FiniteWordCode.words 2 w (fun i => finTwoEquiv.symm (s i))

theorem number_injective (w : ℕ) : Function.Injective (number w) := by
  intro s t he
  have h := (FiniteWordCode.words 2 w).injective he
  funext i
  exact finTwoEquiv.symm.injective (congrFun h i)

/-- High zero padding: the binary integer is unchanged in the public larger range. -/
def pad (Δ k ids : ℕ) (s : DeterministicColorReductionStep.Bits (terminalWidth Δ k ids)) :
    Fin (palette Δ k) :=
  ⟨(number _ s).val, (number _ s).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (terminal_lt Δ k ids).le)⟩

theorem pad_val (Δ k ids : ℕ) (s : DeterministicColorReductionStep.Bits (terminalWidth Δ k ids)) :
    (pad Δ k ids s).val = (number _ s).val := rfl

theorem pad_injective (Δ k ids : ℕ) : Function.Injective (pad Δ k ids) := by
  intro s t he
  have hv := congrArg (fun x : Fin (palette Δ k) => x.val) he
  apply number_injective (terminalWidth Δ k ids)
  apply Fin.ext
  simpa only [pad_val] using hv

def coloring {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) : Program V Unit (Fin (palette Δ k)) :=
  .seq (DeterministicColorReductionPhysicalProgram.fromIdentifiers C Δ (2 * k))
    (.local fun _ _ s => pad Δ k ids s)

theorem coloring_rounds {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) :
    (coloring C Δ k).rounds =
      (DeterministicColorReductionPhysicalProgram.fromIdentifiers C Δ (2 * k)).rounds := by
  simp only [coloring, Program.rounds, Nat.add_zero]

theorem coloring_maxBits {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) :
    (coloring C Δ k).maxBits =
      (DeterministicColorReductionPhysicalProgram.fromIdentifiers C Δ (2 * k)).maxBits := by
  simp only [coloring, Program.maxBits, Nat.max_zero]

def candidateColors (Δ k : ℕ) : ℕ := palette Δ k * 2 ^ ((Δ + 1) ^ k)

def iteration {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) :
    Program V (Bool × Fin (palette Δ k)) (Finset V) :=
  DeterministicPartitionIterationProgram.program C Δ k t (palette Δ k) (candidateColors Δ k) T
    (palette_pos Δ k)

def holdActive : Program V Bool (Unit × Bool) := .local fun _ _ s => ((), s)

def attachColor (Φ : ℕ) : Program V (Fin Φ × Bool) (Bool × Fin Φ) :=
  .local fun _ _ s => (s.2, s.1)

def program {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) : Program V Bool (Finset V) :=
  .seq holdActive
    (.seq (ProgramMemory.carry (X := Bool) (coloring C Δ k))
      (.seq (attachColor (palette Δ k)) (iteration C Δ k t T)))

theorem rounds {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) :
    (program C Δ k t T).rounds =
      (DeterministicColorReductionPhysicalProgram.fromIdentifiers C Δ (2 * k)).rounds +
        T * (candidateColors Δ k * k + 2 * k + 1) := by
  simp only [program, holdActive, attachColor, iteration, Program.rounds, ProgramMemory.rounds,
    coloring_rounds, DeterministicPartitionIterationProgram.rounds, Nat.zero_add, Nat.add_zero]

def iterationBits (ids Δ k : ℕ) : ℕ :=
  (Δ + 1) ^ (candidateColors Δ k * k + 2 * k + 1) *
    (ids + (Δ * (ids + 1) + (1 + palette Δ k)) + 1)

theorem maxBits {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) :
    (program C Δ k t T).maxBits ≤
      max (powerDegree Δ k * (ids + ids + 1)) (iterationBits ids Δ k) := by
  have hc : (coloring C Δ k).maxBits ≤ powerDegree Δ k * (ids + ids + 1) := by
    rw [coloring_maxBits]
    exact DeterministicColorReductionPhysicalProgram.identifiers_maxBits C Δ (2 * k)
  have hi := DeterministicPartitionIterationProgram.maxBits C Δ k t (palette Δ k)
    (candidateColors Δ k) T (palette_pos Δ k)
  simpa only [program, holdActive, attachColor, iteration, Program.maxBits, ProgramMemory.maxBits,
    Nat.zero_max, iterationBits] using max_le_max hc hi

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The mathematical name of the actual computed palette output. -/
def color {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ) : V → Fin (palette Δ k) :=
  (coloring C Δ k).runEncoded G (fun _ => ())

theorem color_proper_ball {ids : ℕ} (C : BitCode V ids) (Δ k : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (u v : V) (hne : u ≠ v)
    (hball : v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k)) :
    color G C Δ k u ≠ color G C Δ k v := by
  intro he
  change pad Δ k ids ((DeterministicColorReductionPhysicalProgram.fromIdentifiers C Δ (2 * k)).runEncoded
      G (fun _ => ()) u) =
    pad Δ k ids ((DeterministicColorReductionPhysicalProgram.fromIdentifiers C Δ (2 * k)).runEncoded
      G (fun _ => ()) v) at he
  exact DeterministicColorReductionPhysicalProgram.identifiers_proper_ball G C Δ (2 * k) hdeg
    u v hne hball (pad_injective Δ k ids he)

/-- The active bit survives coloring privately, then the real iteration receives Bool x Fin Phi. -/
theorem execution_eq {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) (S : Finset V) :
    (program C Δ k t T).runEncoded G (fun u => decide (u ∈ S)) =
      (iteration C Δ k t T).runEncoded G (fun u => (decide (u ∈ S), color G C Δ k u)) := by
  simp only [Program.runEncoded_eq_run]
  change (iteration C Δ k t T).run G (fun v =>
      let st := (ProgramMemory.carry (X := Bool) (coloring C Δ k)).run G
        (fun u => ((), decide (u ∈ S))) v
      (st.2, st.1)) =
    (iteration C Δ k t T).run G (fun u => (decide (u ∈ S), color G C Δ k u))
  rw [ProgramMemory.run G (coloring C Δ k)]
  have hc : (coloring C Δ k).run G (fun _ => ()) = color G C Δ k :=
    (Program.runEncoded_eq_run G (coloring C Δ k) (fun _ => ())).symm
  rw [hc]

def parts {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) (S : Finset V) : Finset (Finset V) :=
  DeterministicPartitionIterationCore.parts (fun v => G.neighborFinset v) k t
    (DeterministicPartitionIterationPower.color (fun v => G.neighborFinset v) Δ k (palette Δ k)
      (color G C Δ k)) (candidateColors Δ k) S T

/-- Exact complete-part output from the actual composed program. -/
theorem correct {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) (S : Finset V)
    (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) :
    (program C Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v =
      (parts G C Δ k t T S).biUnion (fun U => if v ∈ U then U else ∅) := by
  rw [execution_eq G C Δ k t T S]
  exact DeterministicPartitionIterationProgram.correct G C Δ k t (palette Δ k) (candidateColors Δ k) T
    (palette_pos Δ k) S (color G C Δ k) hdeg v

def partition {ids : ℕ} (C : BitCode V ids) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (S : Finset V) (T : ℕ) : SmallParts.Data G S k :=
  DeterministicPartitionIterationPower.partition G Δ hdeg k hk t ht (palette Δ k) (color G C Δ k)
    (color_proper_ball G C Δ k hdeg) S T

theorem partition_parts {ids : ℕ} (C : BitCode V ids) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (S : Finset V) (T : ℕ) :
    (partition G C Δ hdeg k hk t ht S T).parts = parts G C Δ k t T S :=
  DeterministicPartitionIterationPower.partition_parts G Δ hdeg k hk t ht (palette Δ k)
    (color G C Δ k) (color_proper_ball G C Δ k hdeg) S T

theorem output_part {ids : ℕ} (C : BitCode V ids) (Δ k t T : ℕ) (hk : 0 < k) (ht : 0 < t)
    (S : Finset V) (hdeg : ∀ v, G.degree v ≤ Δ) (v : V) (hv : v ∈ S) :
    let U := (program C Δ k t T).runEncoded G (fun u => decide (u ∈ S)) v
    U ∈ (partition G C Δ hdeg k hk t ht S T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected := by
  have he := congrFun (execution_eq G C Δ k t T S) v
  have hp :=
    DeterministicPartitionIterationProgram.output_part G C Δ k t (palette Δ k) T hk ht
      (palette_pos Δ k) S (color G C Δ k) hdeg (color_proper_ball G C Δ k hdeg) v hv
  exact (congrArg (fun U : Finset V =>
    U ∈ (partition G C Δ hdeg k hk t ht S T).parts ∧ v ∈ U ∧ U.card ≤ k ∧
      (G.induce (U : Set V)).Connected) he).mpr
    (by simpa only [partition, iteration, candidateColors] using hp)

end Graph

/-- Proof-only crossing-graph decidability, matching the received cut theorem.
It is introduced after all executable definitions and changes no physical test. -/
private noncomputable local instance partCutDecidable {W : Type} [Fintype W] [LinearOrder W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (S : Finset W) (P : Finset (Finset W)) :
    DecidableRel (PartCut.graph H S P).Adj := fun _ _ => Classical.propDecidable _

/-- Choose t,k,T before the graph and identifier representation, with no supplied chi. -/
theorem uniform_cut (C : ℝ) (hC : 0 ≤ C) (Δ : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t k T : ℕ, ∃ ht : 0 < t, ∃ hk : 0 < k,
      ∀ {W : Type} [Fintype W] [LinearOrder W] (H : SimpleGraph W) [DecidableRel H.Adj],
        SeparatorBalance.Bound H C (2 / 3) → (hdeg : ∀ v, H.degree v ≤ Δ) →
        ∀ {ids : ℕ} (I : BitCode W ids) (S : Finset W),
          ((PartCut.graph H S (partition H I Δ hdeg k hk t ht S T).parts).edgeFinset.card : ℝ) ≤
            η * S.card := by
  obtain ⟨t, k, T, ht, hk, h⟩ := DeterministicPartitionIterationPower.parameters C hC Δ η hη
  refine ⟨t, k, T, ht, hk, ?_⟩
  intro W _ _ H _ hprofile hdeg ids I S
  exact (h H hprofile hdeg (palette Δ k) (color H I Δ k) (color_proper_ball H I Δ k hdeg) S).2.2

end Paper.DeterministicPartitionComputedProgram

#print axioms Paper.DeterministicPartitionComputedProgram.pad_injective
#print axioms Paper.DeterministicPartitionComputedProgram.color_proper_ball
#print axioms Paper.DeterministicPartitionComputedProgram.execution_eq
#print axioms Paper.DeterministicPartitionComputedProgram.correct
#print axioms Paper.DeterministicPartitionComputedProgram.output_part
#print axioms Paper.DeterministicPartitionComputedProgram.uniform_cut
#print axioms Paper.DeterministicPartitionComputedProgram.rounds
#print axioms Paper.DeterministicPartitionComputedProgram.maxBits
