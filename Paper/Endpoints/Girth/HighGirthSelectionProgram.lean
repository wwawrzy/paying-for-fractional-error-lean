import Paper.Endpoints.Girth.HighGirthPortObservationCorrect

/-! Three physical Boolean broadcasts of the original high-girth rounding.
Initial transformation flags and the own numerator are local inputs. -/
namespace Paper.HighGirthSelectionProgram
open PortBroadcastModel SevenFoundation
variable {V : Type}

structure Input (N : Nat) where
  zone : Bool
  demand : Bool
  cost : Nat
  numerator : Fin N

@[ext] structure State where
  zone : Bool
  demand : Bool
  first : Bool
  residual : Bool
  high : Bool
  last : Bool

def start (D N : Nat) : Program V (Input N) State :=
  .local fun _ _ st => ⟨st.zone, st.demand,
    st.zone && decide (st.cost = 3 ∧ D < 2 * st.numerator.val), false, false, false⟩

def removeFirst : Program V State State := HighGirthPortObservation.program State.first
  (fun _ _ st count => {st with residual := st.demand && decide (count = 0)})

def selectHigh : Program V State State := HighGirthPortObservation.program State.residual
  (fun _ _ st count => {st with high := st.zone && !st.first && decide (4 ≤ count)})

def removeHigh : Program V State State := HighGirthPortObservation.program State.high
  (fun _ _ st count => {st with last := st.residual && decide (count = 0)})

def program (D N : Nat) : Program V (Input N) Bool :=
  .seq (start D N) (.seq removeFirst (.seq selectHigh (.seq removeHigh
    (.local fun _ _ st => st.first || st.high || st.last))))

theorem rounds (D N : Nat) : (program (V := V) D N).rounds = 3 := rfl

theorem maxBits (D N : Nat) : (program (V := V) D N).maxBits = 1 := rfl

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def input {N : Nat} (p : V → Fin N) (v : V) : Input N :=
  ⟨decide (v ∈ HighGirthTransformation.zone G),
   decide (v ∈ HighGirthTransformation.demands G),
   HighGirthTransformation.candidateCost G v, p v⟩

noncomputable def expected (x : V → Real) (phase : Nat) (v : V) : State :=
  ⟨decide (v ∈ HighGirthTransformation.zone G),
   decide (v ∈ HighGirthTransformation.demands G),
   decide (v ∈ HighGirthRounding.first G x),
   if 1 ≤ phase then decide (v ∈ HighGirthRounding.residual G x) else false,
   if 2 ≤ phase then decide (v ∈ HighGirthRounding.high G x) else false,
   if 3 ≤ phase then decide (v ∈ HighGirthRounding.last G x) else false⟩

theorem threshold (D p : Nat) (hD : 0 < D) :
    D < 2 * p ↔ (1 : Real) / 2 < (p : Real) / D := by
  have hd : (0 : Real) < D := by exact_mod_cast hD
  rw [div_lt_div_iff₀ (by norm_num : (0 : Real) < 2) hd]
  norm_cast
  simp only [one_mul, Nat.mul_comm p 2]

theorem count_zero_iff (A : Finset V) (v : V) :
    (closed G v ∩ A).card = 0 ↔ v ∉ covered G A := by
  rw [Finset.card_eq_zero]
  constructor
  · intro h hv
    obtain ⟨u, huA, huv⟩ := Finset.mem_biUnion.mp hv
    have hu : u ∈ closed G v ∩ A := Finset.mem_inter.mpr
      ⟨(closed_symm G v u).mp huv, huA⟩
    rw [h] at hu
    exact Finset.notMem_empty u hu
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨huv, huA⟩ := Finset.mem_inter.mp hu
    exact h (Finset.mem_biUnion.mpr ⟨u,huA,(closed_symm G v u).mpr huv⟩)

theorem start_correct (ports : PortBroadcastModel.Numbering G)
    (D N : Nat) (hD : 0 < D) (p : V → Fin N) :
    (start D N).runEncoded G ports (input G p) =
      expected G (fun v => ((p v).val : Real) / D) 0 := by
  funext v
  apply State.ext <;> try rfl
  apply Bool.eq_iff_iff.mpr
  simp [start, Program.runEncoded, input, expected, HighGirthRounding.first,
    threshold D _ hD]

end Paper.HighGirthSelectionProgram
#print axioms Paper.HighGirthSelectionProgram.rounds
#print axioms Paper.HighGirthSelectionProgram.maxBits
#print axioms Paper.HighGirthSelectionProgram.threshold
#print axioms Paper.HighGirthSelectionProgram.count_zero_iff
#print axioms Paper.HighGirthSelectionProgram.start_correct
