import Paper.Preliminaries.SparseParallelInvariants
import Paper.Communication.MaskProgramCorrect

/-! Real tagged packets deliver each active role's exact scalar message.
The proof derives role participation from received neighbor-role lists. -/
namespace Paper.SparseRoundCorrect
open BroadcastModel
variable {V Role : Type} [Fintype V] [DecidableEq V] [LinearOrder Role]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def expected {In Out Msg : Type} (round : Round V In Out Msg) (roles : V → Finset Role)
    (s : V → Role → In) (v : V) (r : Role) : Msg :=
  round.send v ((MaskedTaskGraph.graph G (SparseRolePrepare.vertices roles r)).neighborFinset v) (s v r)

theorem sent_consistent {In Out Msg : Type} (round : Round V In Out Msg) {b : ℕ}
    (C : BitCode Role b) (K : ℕ) (roles : V → Finset Role) (hK : ∀ v, (roles v).card ≤ K)
    (s : V → Role → In) (xs : V → List (Role × In))
    (hkeys : ∀ v, TaggedDictionary.keys (xs v) = roles v)
    (hstate : ∀ v, TaggedDictionary.Consistent (s v) (xs v)) (v : V) :
    TaggedDictionary.Consistent (expected G round roles s v)
      (SparseParallel.messages round v (SparseRolePrepare.learned G C K roles v) (xs v)) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hr : q.1 ∈ roles v := by
    rw [← hkeys v]
    exact (TaggedDictionary.mem_keys (xs v) q.1).mpr ⟨q, hq, rfl⟩
  change round.send v ((SparseRolePrepare.learned G C K roles v).neighbors q.1) q.2 = _
  rw [hstate v q hq, SparseRolePrepare.neighbors_inside G C K roles hK v q.1 hr]
  rfl

theorem sent_lookup {In Out Msg : Type} (round : Round V In Out Msg) {b : ℕ}
    (C : BitCode Role b) (K : ℕ) (roles : V → Finset Role) (hK : ∀ v, (roles v).card ≤ K)
    (s : V → Role → In) (xs : V → List (Role × In))
    (hkeys : ∀ v, TaggedDictionary.keys (xs v) = roles v)
    (hstate : ∀ v, TaggedDictionary.Consistent (s v) (xs v)) (v : V) (r : Role) (hr : r ∈ roles v) :
    TaggedDictionary.lookup (TaggedDictionary.bounded K
      (SparseParallel.messages round v (SparseRolePrepare.learned G C K roles v) (xs v))).val r =
        some (expected G round roles s v r) := by
  have hk : TaggedDictionary.keys
      (SparseParallel.messages round v (SparseRolePrepare.learned G C K roles v) (xs v)) = roles v :=
    (RoleDictionary.keys_map _ _).trans (hkeys v)
  apply TaggedDictionary.bounded_lookup K (expected G round roles s v) _
    (sent_consistent G round C K roles hK s xs hkeys hstate v)
  · rw [hk]
    exact hK v
  · rw [hk]
    exact hr

theorem updates_consistent {In Out Msg : Type} (round : Round V In Out Msg) {b : ℕ}
    (C : BitCode Role b) (K : ℕ) (roles : V → Finset Role) (hK : ∀ v, (roles v).card ≤ K)
    (s : V → Role → In) (xs : V → List (Role × In))
    (hkeys : ∀ v, TaggedDictionary.keys (xs v) = roles v)
    (hstate : ∀ v, TaggedDictionary.Consistent (s v) (xs v)) (v : V) :
    TaggedDictionary.Consistent
      (fun r => eval (MaskedTaskGraph.graph G (SparseRolePrepare.vertices roles r)) round (fun u => s u r) v)
      (SparseParallel.updates round v (G.neighborFinset v) (SparseRolePrepare.learned G C K roles v) (xs v)
        (fun u => TaggedDictionary.bounded K (SparseParallel.messages round u.val
          (SparseRolePrepare.learned G C K roles u.val) (xs u.val)))) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hr : q.1 ∈ roles v := by
    rw [← hkeys v]
    exact (TaggedDictionary.mem_keys (xs v) q.1).mpr ⟨q, hq, rfl⟩
  have hi : ∀ u : ↥(G.neighborFinset v ∩ (SparseRolePrepare.learned G C K roles v).neighbors q.1),
      TaggedDictionary.lookup (TaggedDictionary.bounded K (SparseParallel.messages round u.val
        (SparseRolePrepare.learned G C K roles u.val) (xs u.val))).val q.1 =
          some (expected G round roles s u.val q.1) := by
    intro u
    have hu := (Finset.mem_inter.mp u.property).2
    have hu' := (congrArg (fun N : Finset V => u.val ∈ N)
      (SparseRolePrepare.neighbor_filter G C K roles hK v q.1)).mp hu
    exact sent_lookup G round C K roles hK s xs hkeys hstate u.val q.1
      ((SparseRolePrepare.mem_vertices roles q.1 u.val).mp (Finset.mem_inter.mp hu').2)
  change round.update v (G.neighborFinset v ∩ (SparseRolePrepare.learned G C K roles v).neighbors q.1) q.2
    (fun u => (TaggedDictionary.lookup (TaggedDictionary.bounded K (SparseParallel.messages round u.val
      (SparseRolePrepare.learned G C K roles u.val) (xs u.val))).val q.1).getD
        (round.send v ((SparseRolePrepare.learned G C K roles v).neighbors q.1) q.2)) = _
  simp only [hi, Option.getD_some]
  rw [hstate v q hq, SparseRolePrepare.neighbors_inside G C K roles hK v q.1 hr,
    MaskProgramCorrect.inter_neighbors G (SparseRolePrepare.vertices roles q.1) v]
  rfl
end Paper.SparseRoundCorrect
