import Paper.Owners.Construction.OwnerRoleMetadata
import Paper.Preliminaries.FiniteSubsetCode
import Paper.Partitions.Local.PriorityTaskView
import Paper.Preliminaries.LocalSeedRecords
import Paper.Solver.LocalSearch.FractionalSearch
import Paper.Owners.Construction.OwnerMetadataBroadcast

/-! Literal finite local task decoder. It decodes the subset and padded
priorities, evaluates the genuine virtual partition/boundary protocol,
checks canonical mask/anchor/part, then forms own physical solver input.
No graph, global owner enumeration or externally supplied task is read. -/
namespace Paper.OwnerRoleTaskData
open BroadcastModel
variable {V : Type} [LinearOrder V]

structure Task (V : Type) where
  owners : Finset V
  boundary : V → Bool
  valid : Bool

def addresses {Δ : ℕ} (xs : List (TopologyGather.Record V Δ)) : List V :=
  (TaggedDictionary.keys xs).sort (· ≤ ·)

def seeds (Δ k Q T F : ℕ) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ)) :
    List (V × PriorityPartitionBroadcast.Input Δ k Q T) :=
  if h : (addresses xs).length ≤ F then
    LocalSeedRecords.records (addresses xs) h (fun u => (true, OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T F i u))
  else []

def view {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ)) (u : V) : Bool × Finset V :=
  FrameInterpreter.evaluate (PriorityTaskView.program C Δ k t Q T hQ) xs (seeds Δ k Q T F i xs)
    (true, fun _ => ⟨0, hQ⟩) u

def compute {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ)) : Task V :=
  let N := FrameInterpreter.neighbors xs
  let l := (NeighborBalls.ball N a k).sort (· ≤ ·)
  let ω := OwnerRoleMetadata.mask ((Δ + 1) ^ k) Q T F i
  let I := FiniteSubsetCode.decode l ((Δ + 1) ^ k) ω
  let f := view C Δ k t Q T F hQ i xs
  ⟨I, fun u => (f u).1,
    decide ((addresses xs).length ≤ F ∧ ω = FiniteSubsetCode.encode l ((Δ + 1) ^ k) I ∧
      I.card ≤ k ∧ a ∈ I ∧ FinitePriorityIndex.leader I a = a ∧ (f a).2 = I)⟩

def input {B : ℕ} (d : Task V) (m : OwnerMetadataBroadcast.State V)
    (c : Fin (B + 1)) : FractionalSearch.Input V B :=
  ⟨d.valid && decide (m.owner ∈ d.owners ∨ (m.heavy = false ∧ (m.support ∩ d.owners).Nonempty)), c,
   d.valid && m.remaining && decide (m.owner ∈ d.owners) && !(d.boundary m.owner)⟩

theorem invalid_inactive {B : ℕ} (d : Task V) (m : OwnerMetadataBroadcast.State V)
    (c : Fin (B + 1)) (h : d.valid = false) :
    (input d m c).active = false := by simp only [input, h, Bool.false_and]

theorem invalid_no_demand {B : ℕ} (d : Task V) (m : OwnerMetadataBroadcast.State V)
    (c : Fin (B + 1)) (h : d.valid = false) :
    (input d m c).demand = false := by simp only [input, h, Bool.false_and]

theorem same_frame {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (a : V) (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs ys : List (TopologyGather.Record V Δ)) (he : xs = ys) :
    compute C Δ k t Q T F hQ a i xs = compute C Δ k t Q T F hQ a i ys := by rw [he]

end Paper.OwnerRoleTaskData
