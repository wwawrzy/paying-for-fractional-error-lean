import Paper.Solver.LocalSearch.RecursiveSearchCorrect
import Paper.Averaging.Tasks.TaskBenchmark

/-! Actual physical task fractional solver: only private active/demand
bits and a bounded integer cost are inputs. The output is an own-vertex
bounded natural numerator with fixed public denominator q. -/
namespace Paper.FractionalSearch
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B : ℕ) where
  active : Bool
  cost : Fin (B + 1)
  demand : Bool

def searchInput {B : ℕ} (q : ℕ) (s : Input V B) : TerminalProtocol.Input V B q :=
  ⟨s.active, s.cost, ⟨if s.demand then q else 0, by split_ifs <;> omega⟩⟩

def prepare (B q : ℕ) : Program V (Input V B) (TerminalProtocol.Input V B q × Bool) :=
  .local fun _ _ s => (searchInput q s, s.active)

def count (M : ℕ) (v : V) (ans : Option (SolutionWord.Word V B)) : Fin (M + 1) :=
  ⟨min (ans.map (fun w => SolutionWord.copies w v) |>.getD 0) M,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def finish (B M : ℕ) : Program V (Option (SolutionWord.Word V B) × Bool) (Fin (M + 1)) :=
  .local fun v _ s => if s.2 then count M v s.1 else 0

def program {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ) :=
  Program.seq (prepare B q) (.seq (ProgramMemory.carry (RecursiveSearch.program C diam a B q M)) (finish B M))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ)
    (s : V → Input V B) (v : V) :
    (program C diam a B q M).run G s v =
      if (s v).active then count M v ((RecursiveSearch.program C diam a B q M).run G (fun u => searchInput q (s u)) v)
      else 0 := by
  change (finish B M).run G ((ProgramMemory.carry (RecursiveSearch.program C diam a B q M)).run G
    (fun u => (searchInput q (s u), (s u).active))) v = _
  rw [ProgramMemory.run]
  rfl

theorem count_some {B M : ℕ} (w : SolutionWord.Word V B) (hw : w.length ≤ M) (v : V) :
    (count M v (some w)).val = SolutionWord.copies w v := by
  have hh : SolutionWord.copies w v ≤ w.length := by
    rw [← SolutionWord.total_size]
    exact Finset.single_le_sum (fun u _ => Nat.zero_le (SolutionWord.copies w u)) (Finset.mem_univ v)
  change min (SolutionWord.copies w v) M = _
  exact Nat.min_eq_left (hh.trans hw)

theorem rounds {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ) :
    (program C diam a B q M).rounds = RecursiveSearch.roundBound diam a M := by
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds, RecursiveSearch.rounds,
    Nat.zero_add, Nat.add_zero]

theorem maxBits {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ) :
    (program C diam a B q M).maxBits ≤ 3 * bits + RecursiveSearch.extraBits diam a B q M := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact RecursiveSearch.maxBits C diam a B q M

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (k a B q M n c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C (4 * k) a B q M).maxBits ≤
      (3 * c + RecursiveSearch.extraBits (4 * k) a B q M) * Nat.clog 2 (n + 2) := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact RecursiveSearch.logarithmic_bits C k a B q M n c hids
end Paper.FractionalSearch
