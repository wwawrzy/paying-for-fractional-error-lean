import Paper.Communication.MaskProgram
import Paper.Communication.EncodedProgram

/-! Physical broadcasts simulate any logical spanning subgraph using private
local neighbor lists. The existing mask compiler is reused unchanged; its
active flag is irrelevant to translation. No neighbor-discovery procedure
is assumed or implemented here. -/

namespace Paper.SubgraphBroadcast

open BroadcastModel

variable {V : Type} [DecidableEq V]

/-- Install the private neighbor list locally, run the existing compiler, and
project the result. No graph, vertex enumeration, or global vector is input
to this constructor. The environment remains private throughout execution. -/
def program {In Out : Type} (P : Program V In Out) : Program V (Finset V × In) Out :=
  .seq (.local fun _ _ s => (s.2, (⟨false, s.1⟩ : MaskProgram.Env V)))
    (.seq (MaskProgram.translate P) (.local fun _ _ s => s.1))

theorem rounds {In Out : Type} (P : Program V In Out) :
    (program P).rounds = P.rounds := by
  simp only [program, Program.rounds, MaskProgram.rounds, Nat.add_zero, Nat.zero_add]

theorem maxBits {In Out : Type} (P : Program V In Out) :
    (program P).maxBits = P.maxBits := by
  simp only [program, Program.maxBits, MaskProgram.maxBits, Nat.max_zero, Nat.zero_max]

variable [Fintype V] (G I : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel I.Adj]
  (hle : I ≤ G)

include hle

theorem inter_neighbors (v : V) :
    G.neighborFinset v ∩ I.neighborFinset v = I.neighborFinset v := by
  apply Finset.inter_eq_right.mpr
  intro u hu
  exact (G.mem_neighborFinset v u).mpr (hle ((I.mem_neighborFinset v u).mp hu))

/-- One physical broadcast implements the logical round and retains its
private environment; no restriction on the environment's active bit is needed. -/
theorem round_correct {In Out Msg : Type} {w : ℕ} (code : BitCode Msg w)
    (R : Round V In Out Msg) (env : V → MaskProgram.Env V)
    (hneighbors : ∀ v, (env v).neighbors = I.neighborFinset v) (s : V → In) (v : V) :
    (MaskProgram.simulateRound code R).run G (fun u => (s u, env u)) v =
      (eval I R s v, env v) := by
  change (R.update v (G.neighborFinset v ∩ (env v).neighbors) (s v)
    (fun u => R.send u.val (env u.val).neighbors (s u.val)), env v) = _
  rw [hneighbors v, inter_neighbors G I hle v]
  simp only [hneighbors]
  rfl

/-- Structural simulation for arbitrary private environments with exact
logical neighbor lists. The compiler itself is the existing translation. -/
theorem translate_correct {In Out : Type} (P : Program V In Out)
    (env : V → MaskProgram.Env V)
    (hneighbors : ∀ v, (env v).neighbors = I.neighborFinset v) : ∀ s : V → In,
    (MaskProgram.translate P).run G (fun v => (s v, env v)) =
      fun v => (P.run I s v, env v) := by
  induction P with
  | «local» f =>
    intro s
    funext v
    change (f v (env v).neighbors (s v), env v) = _
    rw [hneighbors v]
    rfl
  | broadcast w code R =>
    intro s
    funext v
    exact round_correct G I hle code R env hneighbors s v
  | seq P Q ihP ihQ =>
    intro s
    change (MaskProgram.translate Q).run G ((MaskProgram.translate P).run G
      (fun v => (s v, env v))) = _
    rw [ihP s]
    exact ihQ _

theorem run_correct {In Out : Type} (P : Program V In Out) (neighbors : V → Finset V)
    (hneighbors : ∀ v, neighbors v = I.neighborFinset v) (s : V → In) :
    (program P).run G (fun v => (neighbors v, s v)) = P.run I s := by
  change (fun v => ((MaskProgram.translate P).run G
    (fun u => (s u, (⟨false, neighbors u⟩ : MaskProgram.Env V))) v).1) = _
  rw [translate_correct G I hle P (fun v => ⟨false, neighbors v⟩) hneighbors s]

/-- Actual encoded physical execution agrees with encoded logical execution. -/
theorem runEncoded_correct {In Out : Type} (P : Program V In Out)
    (neighbors : V → Finset V) (hneighbors : ∀ v, neighbors v = I.neighborFinset v)
    (s : V → In) :
    (program P).runEncoded G (fun v => (neighbors v, s v)) = P.runEncoded I s := by
  simp only [Program.runEncoded_eq_run]
  exact run_correct G I hle P neighbors hneighbors s

end Paper.SubgraphBroadcast

#print axioms Paper.SubgraphBroadcast.round_correct
#print axioms Paper.SubgraphBroadcast.translate_correct
#print axioms Paper.SubgraphBroadcast.runEncoded_correct
#print axioms Paper.SubgraphBroadcast.rounds
#print axioms Paper.SubgraphBroadcast.maxBits
