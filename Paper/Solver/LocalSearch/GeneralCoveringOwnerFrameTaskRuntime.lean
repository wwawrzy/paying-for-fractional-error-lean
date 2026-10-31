import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameFractionalMean
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalInvariant

/-! Native retained private data determine the complete per-part client
input. Every actual task participant receives each anchor in its part,
so the carrier enlargement theorem applies to the executable score. -/
namespace Paper.GeneralCoveringOwnerFrameTaskRuntime
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open GeneralCoveringOwnerFrameTaskData GeneralCoveringOwnerFrameTaskInputs
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem score_invalid {ids : ℕ} (I : BitCode V ids) (L Δ a B k n q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (anchor v : V) (d : GeneralCoveringOwnerFrameTaskData.Task V) (hv : d.valid = false) :
    GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s anchor v d = 0 :=
  GeneralCoveringTaskFractionalInvariant.inactive _ I a B k q hB _ v
    (GeneralCoveringOwnerFrameTaskData.invalid d
      (frames G I L Δ k n s v).source.env.metadata (s v).2 hv).1

section Original
variable {ids B : ℕ} (I : BitCode V ids) (L Δ k n : ℕ)
variable (C targets : V → Finset V) (D R : Finset V)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u)
variable (hlocal : ∀ u ∈ R, C u ⊆ closed G u) (s : V → Input V B)
variable (hD : ∀ v, (s v).1.center = decide (v ∈ D))
variable (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
variable (hC : ∀ v, (s v).1.candidates = C v)
variable (hTargets : ∀ v, (s v).1.targets = targets v)
include hinc hlocal hD hR hC hTargets

theorem metadata (u : V) :
    (frames G I L Δ k n s u).source.env.metadata =
      GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L (fun v => (s v).1) u := by
  unfold frames
  rw [GeneralCoveringOwnerRoleFrames.env_retained]
  exact (GeneralCoveringOwnerSimulation.learned_spec G I C targets D R L Δ hinc hlocal
    (fun v => (s v).1) hD hR hC hTargets).1 u

variable (Q : Finset D) (S Bdy : Finset (Low D Q))

/-- All five fields are identified from the actual retained metadata and
own cost; the demanded-row and active bits use the native task decoder. -/
theorem payload (d : GeneralCoveringOwnerFrameTaskData.Task V) (hv : d.valid = true)
    (hS : d.owners = GeneralCoveringOwnerRoleFrames.partIds D Q S)
    (hb : ∀ i ∈ S, d.boundary i.val.val = decide (i ∈ Bdy)) :
    (fun u => GeneralCoveringOwnerFrameTaskData.input d
      (frames G I L Δ k n s u).source.env.metadata (s u).2) =
      GeneralCoveringTaskFractionalParallel.taskInput C targets
        (vertices G C D R L Q S) (demands G C D R L Q S Bdy) (fun u => (s u).2) := by
  funext u
  rw [metadata G I L Δ k n C targets D R hinc hlocal s hD hR hC hTargets u]
  let m := GeneralCoveringOwnerDiscoveryCorrect.metadata G C D R L (fun v => (s v).1) u
  have ha := active_correct G C D R L Q S d m (s u).2 u hv hS rfl rfl rfl rfl
  have hd := demand_correct G C D R L Q S Bdy d m (s u).2 u hv hS rfl rfl hb
  have hc : (GeneralCoveringOwnerFrameTaskData.input d m (s u).2).candidates = C u := hC u
  have ht : (GeneralCoveringOwnerFrameTaskData.input d m (s u).2).targets = targets u := hTargets u
  change GeneralCoveringOwnerFrameTaskData.input d m (s u).2 =
    ⟨decide (u ∈ vertices G C D R L Q S), (s u).2,
      decide (u ∈ demands G C D R L Q S Bdy), C u, targets u⟩
  rw [← ha, ← hd, ← hc, ← ht]
  rfl

end Original

section Carrier
variable {ids B : ℕ} (I : BitCode V ids) (L Δ k n : ℕ)
variable (C targets : V → Finset V) (D R : Finset V)
variable (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u)
variable (hlocal : ∀ u ∈ R, C u ⊆ closed G u) (s : V → Input V B)
variable (hD : ∀ v, (s v).1.center = decide (v ∈ D))
variable (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
variable (hC : ∀ v, (s v).1.candidates = C v)
variable (hTargets : ∀ v, (s v).1.targets = targets v)
local notation "Q" => GeneralCoveringOwnerVirtualPrepare.high G C D R L Δ
include hinc hlocal hD hR hC hTargets

/-- Delivery of all part IDs to every actual participant proves the
carrier inclusion needed by the exact runtime comparison. -/
theorem carrier (S : Finset (Low D Q))
    (hconn : ((graph G C D R L Q).induce (S : Set (Low D Q))).Connected)
    (hsize : S.card ≤ k) (a : V) (ha : a ∈ GeneralCoveringOwnerRoleFrames.partIds D Q S) :
    vertices G C D R L Q S ⊆ GeneralCoveringOwnerFrameFractionalMean.carrier G I L Δ k n s a := by
  intro u hu
  simp only [GeneralCoveringOwnerFrameFractionalMean.carrier,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact GeneralCoveringOwnerRoleFrames.task_ids G C targets D R L Δ (outerRadius k n) k (frameRadius k n)
    hinc hlocal (fun v => (s v).1) hD hR hC hTargets I (Nat.le_add_right _ _)
    S hconn hsize u hu ha

/-- A valid native decoded part produces exactly the standard physical
per-part masked client vector, including its deterministic numerator. -/
theorem score (S Bdy : Finset (Low D Q))
    (hconn : ((graph G C D R L Q).induce (S : Set (Low D Q))).Connected)
    (hsize : S.card ≤ k) (anchor : V)
    (ha : anchor ∈ GeneralCoveringOwnerRoleFrames.partIds D Q S)
    (d : GeneralCoveringOwnerFrameTaskData.Task V) (hv : d.valid = true)
    (hS : d.owners = GeneralCoveringOwnerRoleFrames.partIds D Q S)
    (hb : ∀ i ∈ S, d.boundary i.val.val = decide (i ∈ Bdy))
    (a q : ℕ) (hB : 1 ≤ B) (v : V) :
    GeneralCoveringOwnerFrameFractionalMean.score G I L Δ a B k n q hB s anchor v d =
      (GeneralCoveringTaskFractionalSolve.program I a B k q hB).runEncoded
        (MaskedTaskGraph.graph G (vertices G C D R L Q S))
        (GeneralCoveringTaskFractionalParallel.taskInput C targets
          (vertices G C D R L Q S) (demands G C D R L Q S Bdy) (fun u => (s u).2)) v := by
  unfold GeneralCoveringOwnerFrameFractionalMean.score
  rw [payload G I L Δ k n C targets D R hinc hlocal s hD hR hC hTargets Q S Bdy d hv hS hb]
  let K := GeneralCoveringTaskDiameter.context G C D R L Q S hlocal hconn k hsize
  exact congrFun (GeneralCoveringTaskFractionalInvariant.masked G K
    (GeneralCoveringOwnerFrameFractionalMean.carrier G I L Δ k n s anchor)
    (carrier G I L Δ k n C targets D R hinc hlocal s hD hR hC hTargets S hconn hsize anchor ha)
    C targets _ (demands_in_vertices G C D R L Q S Bdy) hinc
    (fun r hr => hlocal r (demands_subset G C D R L Q S Bdy hr))
    (rows_in_vertices G C D R L Q S Bdy hlocal) I a B q
    (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) hB (fun u => (s u).2)) v

end Carrier

end Paper.GeneralCoveringOwnerFrameTaskRuntime

#print axioms Paper.GeneralCoveringOwnerFrameTaskRuntime.metadata
#print axioms Paper.GeneralCoveringOwnerFrameTaskRuntime.payload
#print axioms Paper.GeneralCoveringOwnerFrameTaskRuntime.carrier
#print axioms Paper.GeneralCoveringOwnerFrameTaskRuntime.score
#print axioms Paper.GeneralCoveringOwnerFrameTaskRuntime.score_invalid
