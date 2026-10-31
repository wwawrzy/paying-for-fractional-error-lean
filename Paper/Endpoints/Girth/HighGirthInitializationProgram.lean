import Paper.Endpoints.Girth.HighGirthSelectionCorrect

/-! Original branch-distance-two initialization by three Boolean KT0 rounds.
Only the own numerator is supplied; all transformation data are computed. -/
namespace Paper.HighGirthInitializationProgram
open PortBroadcastModel SevenFoundation
variable {V : Type}

@[ext] structure State (N : Nat) where
  numerator : Fin N
  branch : Bool
  near : Bool
  zone : Bool
  far : Bool
  demand : Bool
  cost : Nat

def start (N : Nat) : Program V (Fin N) (State N) :=
  .local fun _ degree p => ⟨p, decide (3 ≤ degree), false, false, false, false, 0⟩

def findNear (N : Nat) : Program V (State N) (State N) :=
  HighGirthPortObservation.program State.branch
    (fun _ _ st count => {st with near := decide (0 < count)})

def findZone (N : Nat) : Program V (State N) (State N) :=
  HighGirthPortObservation.program State.near
    (fun _ _ st count => {st with zone := decide (0 < count), far := !decide (0 < count)})

def findDemandCost (N : Nat) : Program V (State N) (State N) :=
  HighGirthPortObservation.program State.far
    (fun _ _ st count => {st with demand := st.zone && decide (count = 0), cost := 3 - (count - (if st.far then 1 else 0))})

def program (N : Nat) : Program V (Fin N) (HighGirthSelectionProgram.Input N) :=
  .seq (start N) (.seq (findNear N) (.seq (findZone N) (.seq (findDemandCost N)
    (.local fun _ _ st => ⟨st.zone, st.demand, st.cost, st.numerator⟩))))

theorem rounds (N : Nat) : (program (V := V) N).rounds = 3 := rfl

theorem maxBits (N : Nat) : (program (V := V) N).maxBits = 1 := rfl

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def expected {N : Nat} (p : V → Fin N) (phase : Nat) (v : V) : State N :=
  ⟨p v, decide (v ∈ HighGirthTransformation.branches G),
   if 1 ≤ phase then decide (v ∈ covered G (HighGirthTransformation.branches G)) else false,
   if 2 ≤ phase then decide (v ∈ HighGirthTransformation.zone G) else false,
   if 2 ≤ phase then decide (v ∈ HighGirthTransformation.far G) else false,
   if 3 ≤ phase then decide (v ∈ HighGirthTransformation.demands G) else false,
   if 3 ≤ phase then HighGirthTransformation.candidateCost G v else 0⟩

theorem start_correct (ports : Numbering G) (N : Nat) (p : V → Fin N) :
    (start N).runEncoded G ports p = expected G p 0 := by
  funext v
  apply State.ext <;> try rfl
  simp [start, Program.runEncoded, expected, HighGirthTransformation.branches]

theorem count_pos_iff (A : Finset V) (v : V) :
    0 < (closed G v ∩ A).card ↔ v ∈ covered G A := by
  have h := HighGirthSelectionProgram.count_zero_iff G A v
  simpa only [Nat.pos_iff_ne_zero, not_not] using not_congr h

theorem closed_count (A : Finset V) (v : V) :
    (closed G v ∩ A).card = (if v ∈ A then 1 else 0) + (G.neighborFinset v ∩ A).card := by
  have hc : closed G v = insert v (G.neighborFinset v) := by
    ext u
    simp [closed, SimpleGraph.mem_neighborFinset]
  rw [hc]
  by_cases hv : v ∈ A
  · rw [if_pos hv, Finset.insert_inter_of_mem hv,
      Finset.card_insert_of_notMem (by simp)]
    omega
  · rw [if_neg hv, Finset.insert_inter_of_notMem hv]
    omega

end Paper.HighGirthInitializationProgram
#print axioms Paper.HighGirthInitializationProgram.rounds
#print axioms Paper.HighGirthInitializationProgram.maxBits
#print axioms Paper.HighGirthInitializationProgram.start_correct
#print axioms Paper.HighGirthInitializationProgram.count_pos_iff
#print axioms Paper.HighGirthInitializationProgram.closed_count
