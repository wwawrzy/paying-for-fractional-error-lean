import Paper.Preliminaries.TerminalWord

/-! Actual exact positive-demand count from private search input. It also
provides the correct zero-budget branch: empty word iff no demand remains. -/
namespace Paper.SearchCount
open BroadcastModel
variable {V : Type} [LinearOrder V]

def queryInput {B q : ℕ} (b : ℕ) (s : TerminalProtocol.Input V B q) :
    Bool × (Fin 1 → CappedCount.Count (2 ^ b)) :=
  (s.active, fun _ => CappedCount.cap (2 ^ b)
    (if s.active = true ∧ 0 < s.value.val then 1 else 0))

def prepare (b B q : ℕ) : Program V (TerminalProtocol.Input V B q)
    (Bool × (Fin 1 → CappedCount.Count (2 ^ b))) :=
  .local fun _ _ s => queryInput b s

def finish (b : ℕ) : Program V (PayloadFlood.State (Fin 1 → CappedCount.Count (2 ^ b))) (Option ℕ) :=
  .local fun _ _ s => s.2.map (fun f => (f 0).value.val)

def program {b : ℕ} (C : BitCode V b) (D B q : ℕ) :=
  Program.seq (prepare b B q) (.seq (TaskQueries.countProgram C 1 D) (finish b))

def zero {b : ℕ} (C : BitCode V b) (D B q : ℕ) :=
  Program.seq (program C D B q) (.local fun _ _ s =>
    match s with
    | some 0 => some ([] : SolutionWord.Word V B)
    | _ => none)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D B q : ℕ) (s : V → TerminalProtocol.Input V B q) :
    (program C D B q).run G s = fun v =>
      ((TaskQueries.countProgram C 1 D).run G (fun u => queryInput b (s u)) v).2.map
        (fun f => (f 0).value.val) := rfl

variable (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
variable (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
variable (k : ℕ) (hsize : I.card ≤ k) (B q : ℕ) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
variable (hb : ∀ v, (s v).value = multiplicity v)
include hI hsize ha hb

theorem correct (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) :
    (program C (4 * k) B q).run G s v = some
      (TerminalProtocolCorrect.demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card := by
  let H := PhysicalTasks.vertices G D R L Q I
  let A := TerminalProtocolCorrect.demands H multiplicity
  have hi : (fun u => queryInput b (s u)) = fun u => (decide (u ∈ H),
      fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0)) := by
    funext u
    dsimp only [queryInput]
    rw [ha u, hb u]
    apply Prod.ext
    · rfl
    · funext i
      simp [A, H, TerminalProtocolCorrect.demands]
  have hcounts := TaskQueries.counts G C 1 D R L Q I hI k hsize (fun _ => A)
    (fun _ => Finset.filter_subset _ _) v hv
  have hh := congrArg (Option.map (fun f : Fin 1 → ℕ => f 0)) hcounts
  simp only [Option.map_map, Option.map_some] at hh
  change (((TaskQueries.countProgram C 1 (4 * k)).run G
    (fun u => (decide (u ∈ H), fun _ : Fin 1 => CappedCount.cap (2 ^ b) (if u ∈ A then 1 else 0))) v).2.map
      (fun f => (f 0).value.val)) = some A.card at hh
  rw [run_program, hi]
  exact hh

theorem zero_correct (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) :
    (zero C (4 * k) B q).run G s v =
      if (TerminalProtocolCorrect.demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card = 0
      then some [] else none := by
  change (match (program C (4 * k) B q).run G s v with
    | some 0 => some ([] : SolutionWord.Word V B)
    | _ => none) = _
  rw [correct G D R L Q I hI k hsize B q multiplicity C s ha hb v hv]
  cases hn : (TerminalProtocolCorrect.demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card <;>
    simp [hn]

omit hI hsize ha hb

theorem rounds (D B q : ℕ) : (program C D B q).rounds = 4 * D + 1 := by
  simp [program, prepare, finish, Program.rounds, TaskQueries.countProgram, TaskAllReduce.rounds]

theorem maxBits (D B q : ℕ) : (program C D B q).maxBits ≤ max (3 * b + 3) (D + 2) := by
  have hh := TaskAllReduce.maxBits C (PacketCode.vector (BinaryCounter.countCode b) 1) D
  have hw : b + 1 * (2 * (b + 1)) + 1 = 3 * b + 3 := by omega
  rw [hw] at hh
  simpa only [program, prepare, finish, Program.maxBits, Nat.max_zero, Nat.zero_max,
    TaskQueries.countProgram] using hh
end Paper.SearchCount
