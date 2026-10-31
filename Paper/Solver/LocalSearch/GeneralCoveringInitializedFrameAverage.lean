import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameAverageMean
import Paper.Solver.LocalSearch.GeneralCoveringInitializedRandomFractionalExpectation

/-! One actual initializer followed by the actual deterministic frame solver.
The original private input is saved throughout. The output numerator is a
bounded natural, and its public denominator is independent of graph/input. -/
namespace Paper.GeneralCoveringInitializedFrameAverage
open BroadcastModel
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringInitializerRun.Input V × Fin (B + 1)
abbrev Output (V : Type) (L Δ a B k b n q : ℕ) :=
  Fin (GeneralCoveringOwnerFrameAverage.numeratorBound L Δ a B k b n q + 1) × Input V B

def seed {B : ℕ} (out : GeneralCoveringRequests.Output) (s : Input V B) :
    GeneralCoveringOwnerFrameAverage.Input V B := (GeneralCoveringOwners.initializerInput out s.1, s.2)

def program {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V L Δ a B k b n q) :=
  .seq (.local fun _ _ s => (s.1, s))
    (.seq (ProgramMemory.carry (X := Input V B) (GeneralCoveringInitializerRun.program I ib ih ifreq it))
      (.seq (.local fun _ _ s => (seed s.1 s.2, s.2))
        (.seq (ProgramMemory.carry (X := Input V B)
          (GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB))
          (.local fun _ _ s => (s.1.1, s.2)))))

def state {B Δ k b n : ℕ} (s : V → Input V B) (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :
    V → GeneralCoveringInitializedRandomFractional.Input V B Δ k b n := fun u => ((s u).1, ((s u).2, β u))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Only original private incidence and demanded rows are interpreted here. -/
structure Original {B : ℕ} (s : V → Input V B) where
  cover : V → Finset V
  targets : V → Finset V
  R : Finset V
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ SevenFoundation.closed G r
  rows : ∀ r ∈ R, (cover r).Nonempty
  residual : ∀ r, (s r).1.residual = decide (r ∈ R)
  candidates : ∀ r, (s r).1.candidates = cover r
  inverse : ∀ v, (s v).1.targets = targets v

def randomOriginal {B Δ k b n : ℕ} {s : V → Input V B} (d : Original G s)
    (β : V → ActiveFiniteBitPartition.Bits Δ k b n) :
    GeneralCoveringInitializedRandomFractional.Original G (state s β) where
  cover := d.cover
  targets := d.targets
  R := d.R
  incidence := d.incidence
  local_rows := d.local_rows
  rows := d.rows
  residual := d.residual
  candidates := d.candidates
  inverse := d.inverse

def solverInput {ids B : ℕ} (I : BitCode V ids) (ib ih ifreq it : ℕ) (s : V → Input V B) :
    V → GeneralCoveringOwnerFrameAverage.Input V B := fun v =>
  seed ((GeneralCoveringInitializerRun.program I ib ih ifreq it).runEncoded G (fun u => (s u).1) v) (s v)

private theorem compose_run {In S Mid T Saved Out : Type} (P : Program V In S) (Q : Program V Mid T)
    (first : Saved → In) (next : S → Saved → Mid) (out : T → Out) (s : V → Saved) :
    (Program.seq (Program.local fun _ _ x => (first x, x))
      (Program.seq (ProgramMemory.carry P)
        (Program.seq (Program.local fun _ _ x => (next x.1 x.2, x.2))
          (Program.seq (ProgramMemory.carry Q) (Program.local fun _ _ x => (out x.1, x.2)))))).runEncoded G s =
      fun v => (out (Q.runEncoded G (fun u => next (P.runEncoded G (fun w => first (s w)) u) (s u)) v), s v) := by
  simp only [Program.runEncoded_eq_run]
  change (Program.seq _ (Program.seq (ProgramMemory.carry Q) _)).run G
    ((ProgramMemory.carry P).run G (fun u => (first (s u), s u))) = _
  rw [ProgramMemory.run]
  change (Program.local _).run G ((ProgramMemory.carry Q).run G
    (fun v => (next (P.run G (fun w => first (s w)) v) (s v), s v))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_program {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program I ib ih ifreq it L Δ a B k t b n q hB).runEncoded G s = fun v =>
      (((GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB).runEncoded G
        (solverInput G I ib ih ifreq it s) v).1, s v) := by
  delta program solverInput
  exact compose_run G (GeneralCoveringInitializerRun.program I ib ih ifreq it)
    (GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB) Prod.fst seed Prod.fst s

theorem input_retained {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program I ib ih ifreq it L Δ a B k t b n q hB).runEncoded G s v).2 = s v := by rw [run_program]

theorem private_solver {ids B : ℕ} (I : BitCode V ids) (ib ih ifreq it : ℕ) (s : V → Input V B) (v : V) :
    (solverInput G I ib ih ifreq it s v).1.demand = (s v).1.residual ∧
    (solverInput G I ib ih ifreq it s v).1.candidates = (s v).1.candidates ∧
    (solverInput G I ib ih ifreq it s v).1.targets = (s v).1.targets ∧
    (solverInput G I ib ih ifreq it s v).2 = (s v).2 := ⟨rfl, rfl, rfl, rfl⟩

theorem mean {ids B : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a k : ℕ) (hk : 0 < k)
    (t : ℕ) (ht : 0 < t) (b n q : ℕ) (hq : 0 < q) (hB : 1 ≤ B)
    (s : V → Input V B) (d : Original G s) (v : V) :
    ((((program I ib ih ifreq it L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
        GeneralCoveringOwnerFrameAverage.denominator L Δ k b n q =
      (∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        (((GeneralCoveringInitializedRandomFractional.program I ib ih ifreq it L Δ a B k q t b n hB).runEncoded G
          (state s β) v).1.1.1 : ℝ) / q) / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
  let β₀ := GeneralCoveringInitializedRandomFractionalExpectation.zeroCoins V Δ k b n
  have hi : (fun u => (GeneralCoveringInitializedRandomFractional.randomInput G I ib ih ifreq it (state s β₀) u).1) =
      fun u => (solverInput G I ib ih ifreq it s u).1 := rfl
  have hd : GeneralCoveringTaskRandomPhysicalMarks.Original G
      (fun u => (solverInput G I ib ih ifreq it s u).1) :=
    Eq.mp (congrArg (GeneralCoveringTaskRandomPhysicalMarks.Original G) hi)
      (GeneralCoveringInitializedRandomFractional.original G I ib ih ifreq it (randomOriginal G d β₀))
  rw [run_program]
  apply (GeneralCoveringOwnerFrameAverageMean.mean G I L Δ a k hk t ht b n q hq hB
    (solverInput G I ib ih ifreq it s) hd v).trans
  apply congrArg (fun x : ℝ => x / Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n))
  apply Finset.sum_congr rfl
  intro β _
  have hinput : GeneralCoveringOwnerFrameTaskPointwise.randomInput (solverInput G I ib ih ifreq it s) β =
      GeneralCoveringInitializedRandomFractional.randomInput G I ib ih ifreq it (state s β) := rfl
  have hv := congrArg (fun out : GeneralCoveringInitializedRandomFractional.Output V B Δ k b n =>
    ((out.1.1.1 : ℝ) / q))
    (congrFun (GeneralCoveringInitializedRandomFractional.run_program G I ib ih ifreq it L Δ a B k q t b n hB (state s β)) v)
  exact (congrArg (fun z : V → GeneralCoveringRandomFractionalPhysical.Input V B Δ k b n =>
    (((GeneralCoveringRandomFractionalPhysical.program I L Δ a B k q t b n hB).runEncoded G z v).1.1 : ℝ) / q) hinput).trans hv.symm

theorem rounds {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (program (V := V) I ib ih ifreq it L Δ a B k t b n q hB).rounds =
      (GeneralCoveringInitializerRun.program I ib ih ifreq it).rounds +
      (GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB).rounds := by
  simp only [program, Program.rounds, ProgramMemory.rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits {ids : ℕ} (I : BitCode V ids) (ib ih ifreq it L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (program (V := V) I ib ih ifreq it L Δ a B k t b n q hB).maxBits =
      max (GeneralCoveringInitializerRun.program I ib ih ifreq it).maxBits
        (GeneralCoveringOwnerFrameAverage.program I L Δ a B k t b n q hB).maxBits := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]

end Paper.GeneralCoveringInitializedFrameAverage

#print axioms Paper.GeneralCoveringInitializedFrameAverage.run_program
#print axioms Paper.GeneralCoveringInitializedFrameAverage.input_retained
#print axioms Paper.GeneralCoveringInitializedFrameAverage.private_solver
#print axioms Paper.GeneralCoveringInitializedFrameAverage.mean
#print axioms Paper.GeneralCoveringInitializedFrameAverage.rounds
#print axioms Paper.GeneralCoveringInitializedFrameAverage.maxBits
