import Paper.Preliminaries.SparseRoundCorrect

/-! Full arbitrary-program sparse-role simulation, proved by local/
broadcast/sequence induction. Only actual active entries are represented. -/
namespace Paper.SparseParallelCorrect
open BroadcastModel
variable {V Role : Type} [Fintype V] [DecidableEq V] [LinearOrder Role]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def result {In Out : Type} (P : Program V In Out) (roles : V → Finset Role)
    (s : V → Role → In) (v : V) (r : Role) : Out :=
  P.run (MaskedTaskGraph.graph G (SparseRolePrepare.vertices roles r)) (fun u => s u r) v

theorem consistent {In Out : Type} {b : ℕ} (C : BitCode Role b) (K : ℕ) (P : Program V In Out)
    (roles : V → Finset Role) (hK : ∀ v, (roles v).card ≤ K) :
    ∀ (s : V → Role → In) (xs : V → List (Role × In)),
      (∀ v, TaggedDictionary.keys (xs v) = roles v) →
      (∀ v, TaggedDictionary.Consistent (s v) (xs v)) → ∀ v,
      TaggedDictionary.Consistent (result G P roles s v)
        (((SparseParallel.translate C K P).run G
          (fun u => (xs u, SparseRolePrepare.learned G C K roles u)) v).1) := by
  induction P with
  | «local» f =>
    intro s xs hkeys hstate v p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hr : q.1 ∈ roles v := by
      rw [← hkeys v]
      exact (TaggedDictionary.mem_keys (xs v) q.1).mpr ⟨q, hq, rfl⟩
    change f v ((SparseRolePrepare.learned G C K roles v).neighbors q.1) q.2 = _
    rw [hstate v q hq, SparseRolePrepare.neighbors_inside G C K roles hK v q.1 hr]
    rfl
  | broadcast w code round =>
    intro s xs hkeys hstate v
    exact SparseRoundCorrect.updates_consistent G round C K roles hK s xs hkeys hstate v
  | @seq In Mid Out P Q ihP ihQ =>
    intro s xs hkeys hstate v
    let mid := (SparseParallel.translate C K P).run G
      (fun u => (xs u, SparseRolePrepare.learned G C K roles u))
    let sMid : V → Role → Mid := result G P roles s
    have henv : mid = fun u => ((mid u).1, SparseRolePrepare.learned G C K roles u) := by
      funext u
      refine Prod.ext rfl ?_
      exact SparseParallelInvariants.env_preserved G C K P _ u
    have hmkeys : ∀ u, TaggedDictionary.keys (mid u).1 = roles u := fun u =>
      (SparseParallelInvariants.keys_preserved G C K P _ u).trans (hkeys u)
    have hmstate : ∀ u, TaggedDictionary.Consistent (sMid u) (mid u).1 := ihP s xs hkeys hstate
    change TaggedDictionary.Consistent (result G Q roles sMid v)
      (((SparseParallel.translate C K Q).run G mid v).1)
    rw [henv]
    exact ihQ sMid (fun u => (mid u).1) hmkeys hmstate v

theorem lookup_correct {In Out : Type} {b : ℕ} (C : BitCode Role b) (K : ℕ) (P : Program V In Out)
    (roles : V → Finset Role) (hK : ∀ v, (roles v).card ≤ K)
    (s : V → Role → In) (xs : V → List (Role × In))
    (hkeys : ∀ v, TaggedDictionary.keys (xs v) = roles v)
    (hstate : ∀ v, TaggedDictionary.Consistent (s v) (xs v)) (v : V) (r : Role) (hr : r ∈ roles v) :
    TaggedDictionary.lookup (((SparseParallel.translate C K P).run G
      (fun u => (xs u, SparseRolePrepare.learned G C K roles u)) v).1) r = some (result G P roles s v r) := by
  apply TaggedDictionary.lookup_correct (result G P roles s v) _ (consistent G C K P roles hK s xs hkeys hstate v) r
  rw [SparseParallelInvariants.keys_preserved G C K P _ v, hkeys v]
  exact hr

theorem execute_correct {In Out : Type} {b : ℕ} (C : BitCode Role b) (K : ℕ) (P : Program V In Out)
    (xs : V → List (Role × In)) (hK : ∀ v, (TaggedDictionary.keys (xs v)).card ≤ K)
    (s : V → Role → In) (hstate : ∀ v, TaggedDictionary.Consistent (s v) (xs v))
    (v : V) (r : Role) (hr : r ∈ TaggedDictionary.keys (xs v)) :
    TaggedDictionary.lookup (((SparseParallel.execute C K P).run G xs v).1) r =
      some (P.run (MaskedTaskGraph.graph G
        (SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r)) (fun u => s u r) v) := by
  dsimp only [SparseParallel.execute, Program.run]
  rw [ProgramMemory.run G (SparseRolePrepare.program C K)]
  exact lookup_correct G C K P (fun u => TaggedDictionary.keys (xs u)) hK s xs (fun _ => rfl) hstate v r hr

theorem execute_keys {In Out : Type} {b : ℕ} (C : BitCode Role b) (K : ℕ) (P : Program V In Out)
    (xs : V → List (Role × In)) (v : V) :
    TaggedDictionary.keys (((SparseParallel.execute C K P).run G xs v).1) = TaggedDictionary.keys (xs v) := by
  dsimp only [SparseParallel.execute, Program.run]
  rw [ProgramMemory.run G (SparseRolePrepare.program C K)]
  exact SparseParallelInvariants.keys_preserved G C K P _ v
end Paper.SparseParallelCorrect
