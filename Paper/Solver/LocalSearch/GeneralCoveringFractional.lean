import Paper.Solver.LocalSearch.GeneralCoveringSearchBudget
import Paper.Averaging.Tasks.TaskBenchmark

/-! Actual task fractional solver with private active/demand bits, a bounded
integer cost and the two local incidence lists. The output is an own-vertex
bounded natural numerator with fixed public denominator q. -/
namespace Paper.GeneralCoveringFractional
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Input (V : Type) (B : ℕ) where
  active : Bool
  cost : Fin (B + 1)
  demand : Bool
  candidates : Finset V
  targets : Finset V

def searchInput {B : ℕ} (q : ℕ) (s : Input V B) : GeneralCoveringResidual.Input V B q :=
  ⟨⟨s.active, s.cost, ⟨if s.demand then q else 0, by split_ifs <;> omega⟩⟩, s.candidates, s.targets⟩

def prepare (B q : ℕ) : Program V (Input V B) (GeneralCoveringResidual.Input V B q × Bool) :=
  .local fun _ _ s => (searchInput q s, s.active)

def count (M : ℕ) (v : V) (ans : Option (SolutionWord.Word V B)) : Fin (M + 1) :=
  ⟨min (ans.map (fun w => SolutionWord.copies w v) |>.getD 0) M,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

def finish (B M : ℕ) : Program V (Option (SolutionWord.Word V B) × Bool) (Fin (M + 1)) :=
  .local fun v _ s => if s.2 then count M v s.1 else 0

def program {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ) :=
  Program.seq (prepare B q) (.seq (ProgramMemory.carry (GeneralCoveringSearch.program C diam a B q M)) (finish B M))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ)
    (s : V → Input V B) (v : V) :
    (program C diam a B q M).run G s v =
      if (s v).active then count M v ((GeneralCoveringSearch.program C diam a B q M).run G (fun u => searchInput q (s u)) v)
      else 0 := by
  change (finish B M).run G ((ProgramMemory.carry (GeneralCoveringSearch.program C diam a B q M)).run G
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
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds, GeneralCoveringSearchBudget.rounds,
    Nat.zero_add, Nat.add_zero]

theorem maxBits {bits : ℕ} (C : BitCode V bits) (diam a B q M : ℕ) :
    (program C diam a B q M).maxBits ≤ 3 * bits + RecursiveSearch.extraBits diam a B q M := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact GeneralCoveringSearchBudget.maxBits C diam a B q M

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (D a B q M n c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C D a B q M).maxBits ≤
      (3 * c + RecursiveSearch.extraBits D a B q M) * Nat.clog 2 (n + 2) := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  exact GeneralCoveringSearchBudget.logarithmic_bits C D a B q M n c hids
end Paper.GeneralCoveringFractional

#print axioms Paper.GeneralCoveringFractional.rounds
#print axioms Paper.GeneralCoveringFractional.logarithmic_bits
