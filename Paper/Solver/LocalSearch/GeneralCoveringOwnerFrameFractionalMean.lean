import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameFractional
import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskNative
import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskMean

/-! Exact finite averaging for the actual masked fractional-client answers.
Each sparse role reads its native canonical task decoder and actual private
metadata/cost. Its carrier depends only on the anchor, not on metadata.
The observer used by finite projection is derived from the actual client;
no external task-score contract is a premise. Summing these means into the
full random task vector and adding the repair mean are later steps. -/
namespace Paper.GeneralCoveringOwnerFrameFractionalMean
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open GeneralCoveringOwnerFrameTaskData GeneralCoveringOwnerFrameTaskInputs
open scoped BigOperators
variable {V : Type} [LinearOrder V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance publicAdj (C : V → Finset V) (D R : Finset V) (L Δ : ℕ) :
    DecidableRel (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).Adj := fun _ _ => Classical.propDecidable _

noncomputable def canonical (C : V → Finset V) (D R : Finset V) (L Δ k n : ℕ) (a : V) :
    List (TopologyGather.Record V Δ) :=
  (NeighborBalls.ball (fun u => (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
    (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset u) a (frameRadius k n)).sort.map
    (TopologyGather.localData (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
      (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)) Δ)

noncomputable def task {ids : ℕ} (I : BitCode V ids) (C : V → Finset V) (D R : Finset V)
    (L Δ k t b n : ℕ) (role : Role V Δ k b n) : GeneralCoveringOwnerFrameTaskData.Task V :=
  compute I Δ k t b n (ofLex role).1 (ofLex role).2 (canonical G C D R L Δ k n (ofLex role).1)

noncomputable def expected {ids B : ℕ} (I : BitCode V ids) (C : V → Finset V) (D R : Finset V)
    (L Δ k t b n : ℕ) (s : V → Input V B) (u : V) (role : Role V Δ k b n) : GeneralCoveringFractional.Input V B :=
  GeneralCoveringOwnerFrameTaskData.input (task G I C D R L Δ k t b n role)
    (frames G I L Δ k n s u).source.env.metadata (s u).2

def carrier {ids B : ℕ} (I : BitCode V ids) (L Δ k n : ℕ) (s : V → Input V B) (a : V) : Finset V :=
  Finset.univ.filter (fun u => a ∈ (frames G I L Δ k n s u).anchors)

noncomputable def score {ids : ℕ} (I : BitCode V ids) (L Δ a B k n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (anchor v : V) (d : GeneralCoveringOwnerFrameTaskData.Task V) : Fin (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + 1) :=
  (GeneralCoveringTaskFractionalSolve.program I a B k q hB).runEncoded
    (MaskedTaskGraph.graph G (carrier G I L Δ k n s anchor))
    (fun u => GeneralCoveringOwnerFrameTaskData.input d (frames G I L Δ k n s u).source.env.metadata (s u).2) v

def answer {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (role : Role V Δ k b n) (v : V) : ℕ :=
  ((TaggedDictionary.lookup (((GeneralCoveringOwnerFrameFractional.sparse I L Δ a B k t b n q hB).runEncoded G s v).1.1)
    role).getD 0).val

theorem canonical_capacity (C : V → Finset V) (D R : Finset V) (L Δ k n : ℕ) (a : V) :
    (GeneralCoveringOwnerFramePartition.addresses (canonical G C D R L Δ k n a)).length ≤ frameSlots Δ k n := by
  have hk : TaggedDictionary.keys (canonical G C D R L Δ k n a) =
      NeighborBalls.ball (fun u => (GeneralCoveringOwnerVirtualPrepare.publicGraph G C D R L
        (GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ)).neighborFinset u) a (frameRadius k n) := by
    simp [canonical, TaggedDictionary.keys, List.map_map, Function.comp_def, TopologyGather.localData]
  rw [GeneralCoveringOwnerFramePartition.addresses, Finset.length_sort, hk]
  exact NeighborBallGraph.graph_card_bound _ Δ (GeneralCoveringOwnerTopologyGather.public_degree G C D R L Δ) a _

/-- Every native sparse entry has the common canonical-task interpretation. -/
theorem consistent {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v) (v : V) :
    TaggedDictionary.Consistent (expected G I C D R L Δ k t b n s v)
      ((GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).runEncoded G s v).1 := by
  rw [GeneralCoveringOwnerFrameTaskInputs.run_program]
  intro p hp
  change p ∈ build I Δ k t b n (frames G I L Δ k n s v) (s v).2 at hp
  unfold build RoleInputList.rows at hp
  obtain ⟨role, hrole, rfl⟩ := List.mem_map.mp hp
  have hr : role ∈ TaskRoleId.space (frames G I L Δ k n s v).anchors (metadataCount Δ k b n) :=
    (Finset.mem_sort (· ≤ ·)).mp hrole
  have ha := (TaskRoleId.mem_space _ _ role).mp hr
  rw [GeneralCoveringOwnerFrameTaskInputs.value_frame G I B L Δ k t b n s v role ha]
  rw [GeneralCoveringOwnerRoleFrames.canonical_eq G C targets D R L Δ (outerRadius k n) k (frameRadius k n)
    hinc hlocal (fun u => (s u).1) hD hR hC hTargets I (Nat.le_refl _) v (ofLex role).1 ha]
  rfl

/-- Metadata never changes the physical carrier of a fixed anchor. -/
theorem role_region {ids B : ℕ} (I : BitCode V ids) (L Δ k t b n : ℕ) (s : V → Input V B) (role : Role V Δ k b n) :
    SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (GeneralCoveringOwnerFrameFractional.prepared G I L Δ k t b n s u).1) role =
      carrier G I L Δ k n s (ofLex role).1 := by
  ext u
  rw [SparseRolePrepare.mem_vertices]
  unfold GeneralCoveringOwnerFrameFractional.prepared
  rw [GeneralCoveringOwnerFrameTaskInputs.keys, TaskRoleId.mem_space]
  simp only [carrier, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The finite-mean observer is the actual accepted masked fractional runtime. -/
theorem lookup_score {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v)
    (v : V) (role : Role V Δ k b n) (hr : (ofLex role).1 ∈ (frames G I L Δ k n s v).anchors) :
    TaggedDictionary.lookup (((GeneralCoveringOwnerFrameFractional.sparse I L Δ a B k t b n q hB).runEncoded G s v).1.1) role =
      some (score G I L Δ a B k n q hB s (ofLex role).1 v (task G I C D R L Δ k t b n role)) := by
  have hkey : role ∈ TaggedDictionary.keys (GeneralCoveringOwnerFrameFractional.prepared G I L Δ k t b n s v).1 := by
    unfold GeneralCoveringOwnerFrameFractional.prepared
    rw [GeneralCoveringOwnerFrameTaskInputs.keys]
    exact (TaskRoleId.mem_space _ _ role).mpr hr
  have he := SparseParallelCorrect.execute_correct G (TaskRoleId.code I (metadataCount Δ k b n)) (capacity L Δ k b n)
    (GeneralCoveringTaskFractionalSolve.program I a B k q hB)
    (fun u => (GeneralCoveringOwnerFrameFractional.prepared G I L Δ k t b n s u).1)
    (fun u => GeneralCoveringOwnerFrameTaskInputs.key_bound G I B L Δ k t b n C targets D R
      hinc hlocal s hD hR hC hTargets u)
    (expected G I C D R L Δ k t b n s)
    (fun u => consistent G I B L Δ k t b n C targets D R hinc hlocal s hD hR hC hTargets u) v role hkey
  rw [role_region G I L Δ k t b n s role] at he
  rw [GeneralCoveringOwnerFrameFractional.run_sparse, Program.runEncoded_eq_run]
  simpa only [expected, score, Program.runEncoded_eq_run] using he

theorem answer_score {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v)
    (v : V) (role : Role V Δ k b n) (hr : (ofLex role).1 ∈ (frames G I L Δ k n s v).anchors) :
    answer G I L Δ a B k t b n q hB s role v =
      (score G I L Δ a B k n q hB s (ofLex role).1 v (task G I C D R L Δ k t b n role)).val := by
  rw [answer, lookup_score G I L Δ a B k t b n q hB C targets D R hinc hlocal s hD hR hC hTargets v role hr]
  rfl

/-- Each local finite-role mean equals the public-coin mean of the actual client. -/
theorem role_mean {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v)
    (v anchor : V) (ha : anchor ∈ (frames G I L Δ k n s v).anchors) (mask : Fin (partSlots Δ k) → Bool) :
    (∑ ω : GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n,
      (answer G I L Δ a B k t b n q hB s (TaskRoleId.make anchor (encode Δ k b n mask ω)) v : ℝ)) /
        Fintype.card (GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n) =
      (∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
        ((score G I L Δ a B k n q hB s anchor v
          (GeneralCoveringOwnerFrameTaskMean.decoded I Δ k t b n (canonical G C D R L Δ k n anchor) anchor mask
            (GeneralCoveringOwnerFrameTaskMean.restrict Δ k b n (canonical G C D R L Δ k n anchor) β))).val : ℝ)) /
          Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n) := by
  calc
    _ = (∑ ω : GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n,
        ((score G I L Δ a B k n q hB s anchor v
          (GeneralCoveringOwnerFrameTaskMean.decoded I Δ k t b n (canonical G C D R L Δ k n anchor) anchor mask ω)).val : ℝ)) /
          Fintype.card (GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n) := by
      apply congrArg (fun z : ℝ => z / Fintype.card (GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n))
      apply Finset.sum_congr rfl
      intro ω _
      exact congrArg (fun z : ℕ => (z : ℝ)) (answer_score G I L Δ a B k t b n q hB C targets D R
        hinc hlocal s hD hR hC hTargets v (TaskRoleId.make anchor (encode Δ k b n mask ω)) ha)
    _ = _ := GeneralCoveringOwnerFrameTaskMean.mean I Δ k t b n (canonical G C D R L Δ k n anchor) anchor mask
      (canonical_capacity G C D R L Δ k n anchor) (fun d => (score G I L Δ a B k n q hB s anchor v d).val)

noncomputable def globalMean {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C : V → Finset V) (D R : Finset V) (s : V → Input V B) (anchor v : V) (mask : Fin (partSlots Δ k) → Bool) : ℝ :=
  (∑ β : V → ActiveFiniteBitPartition.Bits Δ k b n,
    ((score G I L Δ a B k n q hB s anchor v
      (GeneralCoveringOwnerFrameTaskMean.decoded I Δ k t b n (canonical G C D R L Δ k n anchor) anchor mask
        (GeneralCoveringOwnerFrameTaskMean.restrict Δ k b n (canonical G C D R L Δ k n anchor) β))).val : ℝ)) /
      Fintype.card (V → ActiveFiniteBitPartition.Bits Δ k b n)

/-- Exact own native numerator/common denominator as a sum of actual client means.
The sum still ranges over candidate masks; identification with the random
partition task vector and the repair contribution are not asserted here. -/
theorem vector_mean {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v) (v : V) :
    ((((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
        GeneralCoveringOwnerFrameFractional.denominator Δ k b n q =
      (∑ anchor ∈ (frames G I L Δ k n s v).anchors,
        ∑ mask : Fin (partSlots Δ k) → Bool, globalMean G I L Δ a B k t b n q hB C D R s anchor v mask) / q := by
  have hn : (((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v).1).val =
      ∑ anchor ∈ (frames G I L Δ k n s v).anchors,
        ∑ mask : Fin (partSlots Δ k) → Bool,
          ∑ ω : GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n,
            answer G I L Δ a B k t b n q hB s (TaskRoleId.make anchor (encode Δ k b n mask ω)) v := by
    rw [GeneralCoveringOwnerFrameFractional.exact_sum G I L Δ a B k t b n q hB C targets D R
      hinc hlocal s hD hR hC hTargets v, GeneralCoveringOwnerFrameFractional.role_metadata_sum]
    apply Finset.sum_congr rfl
    intro anchor _
    rw [Finset.sum_comm]
    rfl
  have hm : ((((GeneralCoveringOwnerFrameFractional.program I L Δ a B k t b n q hB).runEncoded G s v).1).val : ℝ) /
      Fintype.card (GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n) =
      ∑ anchor ∈ (frames G I L Δ k n s v).anchors,
        ∑ mask : Fin (partSlots Δ k) → Bool, globalMean G I L Δ a B k t b n q hB C D R s anchor v mask := by
    rw [hn]
    simp only [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro anchor ha
    apply Finset.sum_congr rfl
    intro mask _
    simpa only [globalMean, Finset.sum_div] using role_mean G I L Δ a B k t b n q hB C targets D R hinc hlocal s hD hR hC hTargets v anchor ha mask
  rw [GeneralCoveringOwnerFrameFractional.denominator_card, Nat.cast_mul,
    mul_comm (q : ℝ) (Fintype.card (GeneralCoveringOwnerFrameTaskMean.Arrays Δ k b n) : ℝ), ← div_div]
  exact congrArg (fun z : ℝ => z / q) hm

end Paper.GeneralCoveringOwnerFrameFractionalMean

#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.canonical_capacity
#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.consistent
#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.role_region
#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.lookup_score
#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.answer_score
#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.role_mean

#print axioms Paper.GeneralCoveringOwnerFrameFractionalMean.vector_mean
