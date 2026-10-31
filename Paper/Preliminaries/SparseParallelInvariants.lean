import Paper.Preliminaries.SparseParallel

namespace Paper.SparseParallelInvariants
open BroadcastModel
variable {V R : Type} [Fintype V] [DecidableEq V] [LinearOrder R]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem round_run {In Out Msg : Type} {b w : ℕ} (C : BitCode R b) (P : BitCode Msg w) (K : ℕ)
    (round : Round V In Out Msg) (s : V → List (R × In) × SparseRolePrepare.Env V R) (v : V) :
    (SparseParallel.simulateRound C P K round).run G s v =
      (SparseParallel.updates round v (G.neighborFinset v) (s v).2 (s v).1
        (fun u => TaggedDictionary.bounded K (SparseParallel.messages round u.val (s u.val).2 (s u.val).1)), (s v).2) := rfl

theorem env_preserved {In Out : Type} {b : ℕ} (C : BitCode R b) (K : ℕ) (P : Program V In Out) :
    ∀ (s : V → List (R × In) × SparseRolePrepare.Env V R) (v : V),
      ((SparseParallel.translate C K P).run G s v).2 = (s v).2 := by
  induction P with
  | «local» _ => intro s v; rfl
  | broadcast _ _ _ => intro s v; rfl
  | seq P Q ihP ihQ =>
    intro s v
    change ((SparseParallel.translate C K Q).run G ((SparseParallel.translate C K P).run G s) v).2 = _
    rw [ihQ]
    exact ihP s v

theorem keys_preserved {In Out : Type} {b : ℕ} (C : BitCode R b) (K : ℕ) (P : Program V In Out) :
    ∀ (s : V → List (R × In) × SparseRolePrepare.Env V R) (v : V),
      TaggedDictionary.keys (((SparseParallel.translate C K P).run G s v).1) = TaggedDictionary.keys (s v).1 := by
  induction P with
  | «local» f =>
    intro s v
    change TaggedDictionary.keys (RoleDictionary.mapValues (fun r x => f v ((s v).2.neighbors r) x) (s v).1) = _
    exact RoleDictionary.keys_map (R := R) _ (s v).1
  | broadcast w code round =>
    intro s v
    dsimp only [SparseParallel.translate, SparseParallel.simulateRound, Program.run, eval, SparseParallel.updates]
    exact RoleDictionary.keys_map (R := R) _ (s v).1
  | seq P Q ihP ihQ =>
    intro s v
    change TaggedDictionary.keys (((SparseParallel.translate C K Q).run G
      ((SparseParallel.translate C K P).run G s) v).1) = _
    rw [ihQ]
    exact ihP s v
end Paper.SparseParallelInvariants
