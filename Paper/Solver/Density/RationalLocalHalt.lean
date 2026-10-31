import Paper.Solver.Density.RationalSaturation
import Paper.Solver.Density.RationalBalance

/-! A one-bit physical broadcast detects a sufficient local halt condition.
The actual primal numerator is then unchanged by every future sequence of
the runtime instructions, without a supplied maximum degree or final clock.
Reaching this condition with unequal local phase ranges is a separate task. -/
namespace Paper.Density.RationalLocalHalt
open BroadcastModel RationalRuntime RationalAccounting RationalSaturation
open RationalBalance SevenFoundation
open scoped BigOperators

variable {V : Type} [DecidableEq V]

def haltRound (m K : ℕ) : Round V (State m K) Bool Bool where
  send _ _ s := s.stopped
  update _ N s messages := s.stopped && decide (∀ u : N, messages u = true)

def certificate (m K : ℕ) : Program V (State m K) Bool :=
  .broadcast 1 BitCode.bool (haltRound m K)

theorem resources (m K : ℕ) :
    (certificate (V := V) m K).rounds = 1 ∧ (certificate (V := V) m K).maxBits = 1 :=
  ⟨rfl, rfl⟩

inductive Instruction where
  | inner (ep : ℤ) (ed : ℕ)
  | restart
  | cleanup

def instruction (m K : ℕ) : Instruction → Program V (State m K) (State m K)
  | .inner ep ed => inner m K ep ed
  | .restart => .local fun _ _ s => { s with active := !s.stopped }
  | .cleanup => .local fun _ _ s => clean s

def continuation (m K : ℕ) : List Instruction → Program V (State m K) (State m K)
  | [] => .local fun _ _ s => s
  | i :: is => .seq (instruction m K i) (continuation m K is)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def Finished {m K : ℕ} (s : V → State m K) (v : V) : Prop :=
  ∀ r ∈ closed G v, (s r).stopped = true

theorem certificate_iff {m K : ℕ} (s : V → State m K) (v : V) :
    (certificate m K).run G s v = true ↔ Finished G s v := by
  change ((s v).stopped && decide (∀ u : G.neighborFinset v, (s u).stopped = true)) = true ↔ _
  rw [Bool.and_eq_true_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, hN⟩ r hr
    rcases (mem_closed G r v).mp hr with rfl | hr
    · exact hv
    · exact hN ⟨r, (G.mem_neighborFinset v r).mpr hr⟩
  · intro h
    exact ⟨h v (self_mem_closed G v), fun u => h u
      ((mem_closed G u v).mpr (Or.inr ((G.mem_neighborFinset v u).mp u.property)))⟩

theorem clean_stopped {m K : ℕ} (s : State m K) (h : s.stopped = true) :
    (clean s).stopped = true := by
  unfold clean
  split_ifs <;> first | rfl | exact h

theorem instruction_stopped {m K : ℕ} (i : Instruction) (s : V → State m K)
    (r : V) (h : (s r).stopped = true) :
    ((instruction m K i).run G s r).stopped = true := by
  cases i with
  | inner ep ed => exact h
  | restart => exact h
  | cleanup => exact clean_stopped _ h

theorem instruction_finished {m K : ℕ} (i : Instruction) (s : V → State m K)
    (v : V) (h : Finished G s v) : Finished G ((instruction m K i).run G s) v :=
  fun r hr => instruction_stopped G i s r (h r hr)

theorem finished_gamma {m K : ℕ} (s : V → State m K) (v : V) (h : Finished G s v) :
    gamma G s v = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  simp only [source, request, h r hr, Bool.not_true, Bool.and_false, requirement,
    Bool.false_eq_true, if_false, Rat.cast_zero]

theorem instruction_primal {m K : ℕ} (hm : 1 ≤ m) (i : Instruction)
    (s : V → State m K) (v : V) (h : Finished G s v) :
    ((instruction m K i).run G s v).primal = (s v).primal := by
  cases i with
  | inner ep ed =>
    have hi : (eval G (primalRound m K ep ed) s v).increment.value.val = 0 := by
      have hz := zero_increment G hm ep ed s v (finished_gamma G s v h)
      change (((eval G (primalRound m K ep ed) s v).increment.value.val : ℕ) : ℝ) = 0 at hz
      exact Nat.cast_eq_zero.mp hz
    change (s v).primal + (eval G (primalRound m K ep ed) s v).increment.value.val = _
    rw [hi, Nat.add_zero]
  | restart => rfl
  | cleanup => exact clean_primal _

/-- A successful local certificate makes the output irrevocable under any
later runtime instruction sequence, regardless of its duration or thresholds. -/
theorem certified_primal_stable {m K : ℕ} (hm : 1 ≤ m) (s : V → State m K) (v : V)
    (h : (certificate m K).run G s v = true) (is : List Instruction) :
    ((continuation m K is).run G s v).primal = (s v).primal ∧
      (certificate m K).run G ((continuation m K is).run G s) v = true := by
  have hf := (certificate_iff G s v).mp h
  suffices ∀ (s : V → State m K), Finished G s v →
      ((continuation m K is).run G s v).primal = (s v).primal ∧
        Finished G ((continuation m K is).run G s) v by
    obtain ⟨hp, hf⟩ := this s hf
    exact ⟨hp, (certificate_iff G _ v).mpr hf⟩
  induction is with
  | nil => exact fun _ hs => ⟨rfl, hs⟩
  | cons i is ih =>
    intro s hs
    obtain ⟨hp, hf⟩ := ih _ (instruction_finished G i s v hs)
    exact ⟨hp.trans (instruction_primal G hm i s v hs), hf⟩

end Paper.Density.RationalLocalHalt

#print axioms Paper.Density.RationalLocalHalt.resources
#print axioms Paper.Density.RationalLocalHalt.certificate_iff
#print axioms Paper.Density.RationalLocalHalt.instruction_primal
#print axioms Paper.Density.RationalLocalHalt.certified_primal_stable
