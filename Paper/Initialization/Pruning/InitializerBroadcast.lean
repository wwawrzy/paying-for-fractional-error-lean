import Paper.Initialization.Pruning.InitializerPassCorrect
import Paper.Initialization.Pruning.InitializerRun

/-! Full fixed-pass initialization, with literal private residual/past
bits. The selected set is exactly the previously analysed initializer. -/
namespace Paper.InitializerBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def step {b : ℕ} (C : BitCode V b) (a h f : ℕ) : Program V (Bool × Bool) (Bool × Bool) :=
  .seq (ProgramMemory.carry (InitializerPassBroadcast.program C a h f))
    (.local fun _ _ s => (s.1.2, s.2 || s.1.1))

def program {b : ℕ} (C : BitCode V b) (a h f T : ℕ) : Program V Bool Bool :=
  .seq (.local fun _ _ s => (s, false)) (.seq ((step C a h f).iterate T)
    (.local fun _ _ s => s.2 || s.1))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_step {b : ℕ} (C : BitCode V b) (a h f : ℕ) (ha : 1 ≤ a) (R P : Finset V) :
    (step C a h f).run G (fun v => (decide (v ∈ R), decide (v ∈ P))) = fun v =>
      (decide (v ∈ InitializerPass.residual G a h f R),
        decide (v ∈ P ∪ InitializerPass.selected G a h f R)) := by
  change (fun v => (((ProgramMemory.carry (InitializerPassBroadcast.program C a h f)).run G
      (fun u => (decide (u ∈ R), decide (u ∈ P))) v).1.2,
    ((ProgramMemory.carry (InitializerPassBroadcast.program C a h f)).run G
      (fun u => (decide (u ∈ R), decide (u ∈ P))) v).2 ||
    ((ProgramMemory.carry (InitializerPassBroadcast.program C a h f)).run G
      (fun u => (decide (u ∈ R), decide (u ∈ P))) v).1.1)) = _
  rw [ProgramMemory.run G (InitializerPassBroadcast.program C a h f), InitializerPassCorrect.correct G C a h f ha R]
  funext v
  simp only [Finset.mem_union, Bool.decide_or]

theorem iterate_correct {b : ℕ} (C : BitCode V b) (a h f : ℕ) (ha : 1 ≤ a) (R : Finset V) (T : ℕ) :
    ((step C a h f).iterate T).run G (fun v => (decide (v ∈ R), false)) = fun v =>
      (decide (v ∈ InitializerRun.state G a h f R T), decide (v ∈ InitializerRun.past G a h f R T)) := by
  induction T with
  | zero =>
    funext v
    simp only [Program.iterate, Program.run, InitializerRun.state, InitializerRun.past,
      Finset.range_zero, Finset.biUnion_empty, Finset.notMem_empty, decide_false]
    exact Prod.ext (Bool.decide_congr Iff.rfl) rfl
  | succ T ih =>
    change (step C a h f).run G (((step C a h f).iterate T).run G (fun v => (decide (v ∈ R), false))) = _
    rw [ih, run_step G C a h f ha]
    rw [InitializerRun.past_succ]
    have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [hinst]
    rfl

theorem correct {b : ℕ} (C : BitCode V b) (a h f T : ℕ) (ha : 1 ≤ a) (R : Finset V) :
    (program C a h f T).run G (fun v => decide (v ∈ R)) = fun v =>
      decide (v ∈ InitializerRun.past G a h f R T ∪ InitializerRun.state G a h f R T) := by
  change (fun v => (((step C a h f).iterate T).run G (fun u => (decide (u ∈ R), false)) v).2 ||
      (((step C a h f).iterate T).run G (fun u => (decide (u ∈ R), false)) v).1) = _
  rw [iterate_correct G C a h f ha R T]
  funext v
  simp only [Finset.mem_union, Bool.decide_or]

theorem rounds {b : ℕ} (C : BitCode V b) (a h f T : ℕ) :
    (program C a h f T).rounds = T * (4 + 2 * f) := by
  simp only [program, step, Program.rounds, Program.iterate_rounds, ProgramMemory.rounds,
    InitializerPassBroadcast.rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (a h f T : ℕ) :
    (program C a h f T).maxBits ≤ max 1 (f * (b + 1)) := by
  simp only [program, Program.maxBits, Nat.zero_max, Nat.max_zero]
  apply (Program.iterate_maxBits (step C a h f) T).trans
  simp only [step, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero]
  exact InitializerPassBroadcast.maxBits C a h f

theorem logarithmic_bits {b : ℕ} (C : BitCode V b) (a h f T n c : ℕ)
    (hids : b ≤ c * Nat.clog 2 (n + 2)) :
    (program C a h f T).maxBits ≤ (1 + f * (c + 1)) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hw := ListPacket.logarithmic_width f b c n hids
  apply (maxBits C a h f T).trans
  apply max_le <;> nlinarith
end Paper.InitializerBroadcast
