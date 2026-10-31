import Paper.Owners.Construction.OwnerPayloadStarRead
import Paper.Owners.Construction.OwnerPayloadLocalKeys

/-! Actual three-round physical delivery to every owner-star vertex and
every support candidate. At most L+1 distinct root payloads are retained. -/
namespace Paper.RootPayloadRoute
open BroadcastModel
variable {V A : Type} [LinearOrder V]

def starInput (s : OwnerPayloadRoute.Input V A) : OwnerPayloadRead.Input V A :=
  ⟨s.metadata.owner, true, s.active, s.payload⟩

def candidateProgram {b w : ℕ} (C : BitCode V b) (P : BitCode A w) :
    Program V (OwnerPayloadRoute.Input V A) (List (V × A)) :=
  .seq (.local fun _ _ s => OwnerPayloadRoute.readInput s)
    (.seq (OwnerPayloadRead.program P)
      (.seq (.local fun _ _ s => s.toList) (TaggedGather.program C P 1)))

def program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L : ℕ) :
    Program V (OwnerPayloadRoute.Input V A) {l : List (V × A) // l.length ≤ L + 1} :=
  .seq (.local fun _ _ s => (starInput s, s))
    (.seq (ProgramMemory.carry (OwnerPayloadRead.program P))
      (.seq (.local fun _ _ s => (s.2, s.1))
        (.seq (ProgramMemory.carry (candidateProgram C P))
          (.local fun _ _ s => TaggedDictionary.bounded (L + 1) (s.1 ++ s.2.toList)))))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem candidate_run {b w : ℕ} (C : BitCode V b) (P : BitCode A w)
    (s : V → OwnerPayloadRoute.Input V A) :
    (candidateProgram C P).run G s = OwnerPayloadRoute.candidate G C P s := rfl

theorem run_program {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L : ℕ)
    (s : V → OwnerPayloadRoute.Input V A) (v : V) :
    ((program C P L).run G s v).val = TaggedDictionary.bounded (L + 1)
      (OwnerPayloadRoute.candidate G C P s v ++
        ((OwnerPayloadRead.program P).run G (fun u => starInput (s u)) v).toList) := by
  dsimp only [program, Program.run]
  rw [ProgramMemory.run G (OwnerPayloadRead.program P)]
  dsimp only
  rw [ProgramMemory.run G (candidateProgram C P)]
  rfl

theorem rounds {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L : ℕ) :
    (program C P L).rounds = 3 := rfl

theorem maxBits {b w : ℕ} (C : BitCode V b) (P : BitCode A w) (L : ℕ) :
    (program C P L).maxBits ≤ b + w + 1 := by
  simp only [program, candidateProgram, Program.maxBits, ProgramMemory.maxBits,
    OwnerPayloadRead.maxBits, TaggedGather.maxBits, Nat.one_mul, Nat.zero_max, Nat.max_zero]
  exact max_le (by omega) (max_le (by omega) (le_refl _))

end Paper.RootPayloadRoute
