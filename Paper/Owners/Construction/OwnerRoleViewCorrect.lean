import Paper.Owners.Construction.OwnerRoleTaskData
import Paper.Partitions.Local.ClosedNeighborBalls
import Paper.Preliminaries.LocalSeedExtension

/-! Exact interpretation of the literal local role-view computation.
Only finite local priority coordinates are required; all other source
coordinates are arbitrary, with independence proved by program locality. -/
namespace Paper.OwnerRoleViewCorrect
open BroadcastModel
variable {V : Type} [LinearOrder V]

theorem extension (Δ k Q T F : ℕ) (hQ : 0 < Q)
    (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (hF : (OwnerRoleTaskData.addresses xs).length ≤ F) :
    ∃ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      ∀ j : Fin (OwnerRoleTaskData.addresses xs).length,
        OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T F i
          (LocalSeedRecords.slot (OwnerRoleTaskData.addresses xs) hF j) =
        ζ ((OwnerRoleTaskData.addresses xs).get j) := by
  let l := OwnerRoleTaskData.addresses xs
  let τ := fun j : Fin l.length => OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T F i
    (LocalSeedRecords.slot l hF j)
  let fallback : PriorityPartitionBroadcast.Table Δ k Q T := fun _ => ⟨0, hQ⟩
  refine ⟨FrameInterpreter.inputs (LocalSeedRecords.base l τ) fallback, ?_⟩
  intro j
  exact (LocalSeedExtension.inputs_get l (Finset.sort_nodup _ _) τ fallback j).symm

theorem seeds_eq (Δ k Q T F : ℕ)
    (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (hF : (OwnerRoleTaskData.addresses xs).length ≤ F)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (hζ : ∀ j : Fin (OwnerRoleTaskData.addresses xs).length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T F i
        (LocalSeedRecords.slot (OwnerRoleTaskData.addresses xs) hF j) =
      ζ ((OwnerRoleTaskData.addresses xs).get j)) :
    OwnerRoleTaskData.seeds Δ k Q T F i xs =
      LocalSeedRecords.base (OwnerRoleTaskData.addresses xs) (fun j =>
        (true, ζ ((OwnerRoleTaskData.addresses xs).get j))) := by
  unfold OwnerRoleTaskData.seeds
  rw [dif_pos hF]
  unfold LocalSeedRecords.records
  congr 1
  funext j
  dsimp only
  rw [hζ j]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem view_correct {b : ℕ} (C : BitCode V b) (Δ k t Q T F : ℕ) (hQ : 0 < Q)
    (i : Fin (OwnerRoleMetadata.count ((Δ + 1) ^ k) Q T F))
    (xs : List (TopologyGather.Record V Δ))
    (hF : (OwnerRoleTaskData.addresses xs).length ≤ F)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T)
    (hζ : ∀ j : Fin (OwnerRoleTaskData.addresses xs).length,
      OwnerRoleMetadata.table ((Δ + 1) ^ k) Q T F i
        (LocalSeedRecords.slot (OwnerRoleTaskData.addresses xs) hF j) =
      ζ ((OwnerRoleTaskData.addresses xs).get j))
    (htrue : ∀ p ∈ xs, p.2.val.toFinset = G.neighborFinset p.1)
    (u : V) (hcover : NeighborBalls.ball (fun w => G.neighborFinset w) u (T * (3 * k + 1) + 1) ⊆
      TaggedDictionary.keys xs) :
    OwnerRoleTaskData.view C Δ k t Q T F hQ i xs u =
      (PriorityTaskView.program C Δ k t Q T hQ).run G (fun w => (true, ζ w)) u := by
  unfold OwnerRoleTaskData.view
  rw [seeds_eq Δ k Q T F i xs hF ζ hζ]
  apply LocalSeedRecords.evaluate_base G _ xs (OwnerRoleTaskData.addresses xs)
    (fun w => (true, ζ w)) _ u htrue
  · rwa [PriorityTaskView.rounds]
  · rw [OwnerRoleTaskData.addresses, Finset.sort_toFinset, PriorityTaskView.rounds]
    exact hcover

theorem all_true_eq {b : ℕ} (C : BitCode V b) (Δ k t Q T : ℕ) (hQ : 0 < Q)
    (S : Finset V) (hS : ∀ u ∈ S, G.neighborFinset u ⊆ S)
    (ζ : V → PriorityPartitionBroadcast.Table Δ k Q T) (v : V) (hv : v ∈ S) :
    (PriorityTaskView.program C Δ k t Q T hQ).run G (fun u => (true, ζ u)) v =
      (PriorityTaskView.program C Δ k t Q T hQ).run G (fun u => (decide (u ∈ S), ζ u)) v := by
  have hh := NeighborLocality.input_locality (PriorityTaskView.program C Δ k t Q T hQ)
    (fun u => G.neighborFinset u) (fun u => (true, ζ u))
    (fun u => (decide (u ∈ S), ζ u)) v (fun u hu => by
      dsimp only
      rw [decide_eq_true (ClosedNeighborBalls.subset _ S hS v hv _ hu)])
  rw [NeighborInterpreter.run_graph, NeighborInterpreter.run_graph] at hh
  exact hh

end Paper.OwnerRoleViewCorrect
