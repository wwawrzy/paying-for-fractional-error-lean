import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskData
import Paper.Preliminaries.RoleInputList

/-! Actual fixed-metadata task inputs from one owner-frame execution.
Only finite delivered anchors and metadata are enumerated. Each physical
vertex contributes its own original incidence lists and bounded cost.
No global input map, completed task solution or physical-ball enumeration
is read by this executable program. -/
namespace Paper.GeneralCoveringOwnerFrameTaskInputs
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]
open GeneralCoveringOwnerFrameTaskData

abbrev Role (V : Type) (Δ k b n : ℕ) := TaskRoleId.Id V (metadataCount Δ k b n)
def outerRadius (k n : ℕ) : ℕ := k + frameRadius k n

def capacity (L Δ k b n : ℕ) : ℕ :=
  (max 1 L * (Δ + 1) ^ k) * metadataCount Δ k b n

abbrev FrameState (V : Type) (L Δ k n : ℕ) :=
  GeneralCoveringOwnerRoleFrames.Output V L Δ (outerRadius k n)

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringOwners.Input V × Fin (B + 1)
abbrev Payload (V : Type) (B Δ k b n : ℕ) :=
  List (Role V Δ k b n × GeneralCoveringFractional.Input V B)
abbrev Saved (V : Type) (B L Δ k n : ℕ) := FrameState V L Δ k n × Fin (B + 1)
abbrev Output (V : Type) (B L Δ k b n : ℕ) := Payload V B Δ k b n × Saved V B L Δ k n

def value {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) (r : Role V Δ k b n) : GeneralCoveringFractional.Input V B :=
  let a := (ofLex r).1
  let i := (ofLex r).2
  let xs := (TaggedDictionary.lookup s.frames a).getD []
  GeneralCoveringOwnerFrameTaskData.input (compute I Δ k t b n a i xs) s.source.env.metadata c

def build {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) : Payload V B Δ k b n :=
  RoleInputList.rows (TaskRoleId.space s.anchors (metadataCount Δ k b n)) (value I Δ k t b n s c)

/-- The public frame radius includes every owner's partition dependency ball. -/
def program {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) :
    Program V (Input V B) (Output V B L Δ k b n) :=
  .seq (ProgramMemory.carry (X := Fin (B + 1))
    (GeneralCoveringOwnerRoleFrames.program I L Δ (outerRadius k n) k (frameRadius k n)))
    (.local fun _ _ s => (build I Δ k t b n s.1 s.2, s))

theorem build_keys {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) :
    TaggedDictionary.keys (build I Δ k t b n s c) =
      TaskRoleId.space s.anchors (metadataCount Δ k b n) := RoleInputList.keys _ _

theorem build_consistent {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) :
    TaggedDictionary.Consistent (value I Δ k t b n s c) (build I Δ k t b n s c) := RoleInputList.consistent _ _

theorem build_lookup {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) (r : Role V Δ k b n)
    (h : (ofLex r).1 ∈ s.anchors) :
    TaggedDictionary.lookup (build I Δ k t b n s c) r = some (value I Δ k t b n s c r) := by
  apply TaggedDictionary.lookup_correct _ _ (build_consistent I Δ k t b n s c)
  rw [build_keys]
  exact (TaskRoleId.mem_space _ _ r).mpr h

theorem value_cost {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) (r : Role V Δ k b n) :
    (value I Δ k t b n s c r).cost = c := rfl

theorem value_candidates {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) (r : Role V Δ k b n) :
    (value I Δ k t b n s c r).candidates = s.source.env.metadata.owned.input.candidates := rfl

theorem value_targets {ids B L : ℕ} (I : BitCode V ids) (Δ k t b n : ℕ)
    (s : FrameState V L Δ k n) (c : Fin (B + 1)) (r : Role V Δ k b n) :
    (value I Δ k t b n s c r).targets = s.source.env.metadata.owned.input.targets := rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def frames {ids B : ℕ} (I : BitCode V ids) (L Δ k n : ℕ) (s : V → Input V B) :=
  (GeneralCoveringOwnerRoleFrames.program I L Δ (outerRadius k n) k (frameRadius k n)).runEncoded G (fun v => (s v).1)

theorem run_program {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) (s : V → Input V B) :
    (program I B L Δ k t b n).runEncoded G s = fun v =>
      (build I Δ k t b n (frames G I L Δ k n s v) (s v).2, (frames G I L Δ k n s v, (s v).2)) := by
  rw [Program.runEncoded_eq_run]
  change (Program.local fun _ _ z => (build I Δ k t b n z.1 z.2, z)).run G
    ((ProgramMemory.carry (GeneralCoveringOwnerRoleFrames.program I L Δ (outerRadius k n) k (frameRadius k n))).run G s) = _
  have he : s = fun v => ((s v).1, (s v).2) := rfl
  rw [he, ProgramMemory.run]
  change (fun v => (build I Δ k t b n
    ((GeneralCoveringOwnerRoleFrames.program I L Δ (outerRadius k n) k (frameRadius k n)).run G (fun u => (s u).1) v) (s v).2,
    ((GeneralCoveringOwnerRoleFrames.program I L Δ (outerRadius k n) k (frameRadius k n)).run G (fun u => (s u).1) v, (s v).2))) = _
  simp only [frames, Program.runEncoded_eq_run]

theorem source_retained {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) (s : V → Input V B) (v : V) :
    ((program I B L Δ k t b n).runEncoded G s v).2.1 = frames G I L Δ k n s v := by rw [run_program]

theorem cost_retained {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) (s : V → Input V B) (v : V) :
    ((program I B L Δ k t b n).runEncoded G s v).2.2 = (s v).2 := by rw [run_program]

theorem private_input_retained {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) (s : V → Input V B) (v : V) :
    ((program I B L Δ k t b n).runEncoded G s v).2.1.source.env.metadata.owned.input = (s v).1 := by
  rw [source_retained]
  exact GeneralCoveringOwnerRoleFrames.private_input_retained G I L Δ (outerRadius k n) k (frameRadius k n) (fun u => (s u).1) v

theorem keys {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) (s : V → Input V B) (v : V) :
    TaggedDictionary.keys ((program I B L Δ k t b n).runEncoded G s v).1 =
      TaskRoleId.space (frames G I L Δ k n s v).anchors (metadataCount Δ k b n) := by
  rw [run_program, build_keys]

/-- Actual dictionary lookup uses the exact canonical frame delivered at its anchor. -/
theorem value_frame {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) (s : V → Input V B)
    (v : V) (role : Role V Δ k b n) (hr : (ofLex role).1 ∈ (frames G I L Δ k n s v).anchors) :
    value I Δ k t b n (frames G I L Δ k n s v) (s v).2 role =
      GeneralCoveringOwnerFrameTaskData.input
        (compute I Δ k t b n (ofLex role).1 (ofLex role).2
          (GeneralCoveringOwnerRoleFrames.canonical G I L Δ (outerRadius k n) (frameRadius k n)
            (fun u => (s u).1) v (ofLex role).1))
        (frames G I L Δ k n s v).source.env.metadata (s v).2 := by
  dsimp only [value, frames]
  rw [GeneralCoveringOwnerRoleFrames.frame_lookup G I L Δ (outerRadius k n) k (frameRadius k n)
    (fun u => (s u).1) v (ofLex role).1 hr]
  rfl

/-- The genuine support/degree geometry supplies the sparse-client capacity. -/
theorem key_bound {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v) (v : V) :
    (TaggedDictionary.keys ((program I B L Δ k t b n).runEncoded G s v).1).card ≤ capacity L Δ k b n := by
  rw [keys, TaskRoleId.card_space]
  exact Nat.mul_le_mul_right _ (GeneralCoveringOwnerRoleFrames.anchors_card G C targets D R L Δ
    (outerRadius k n) k (frameRadius k n) hinc hlocal (fun u => (s u).1) hD hR hC hTargets I
    (Nat.le_add_right _ _) v)

theorem rounds {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) :
    (program I B L Δ k t b n).rounds = 12 + 4 * outerRadius k n := by
  simp only [program, Program.rounds, ProgramMemory.rounds, GeneralCoveringOwnerRoleFrames.rounds, Nat.add_zero]

theorem maxBits_eq {ids : ℕ} (I : BitCode V ids) (B L Δ k t b n : ℕ) :
    (program I B L Δ k t b n).maxBits =
      (GeneralCoveringOwnerRoleFrames.program I L Δ (outerRadius k n) k (frameRadius k n)).maxBits := by
  simp only [program, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero]

end Paper.GeneralCoveringOwnerFrameTaskInputs

#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.build_keys
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.build_consistent
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.build_lookup
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.value_cost
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.value_candidates
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.value_targets
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.run_program
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.source_retained
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.cost_retained
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.private_input_retained
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.keys
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.rounds
#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.maxBits_eq

#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.key_bound

#print axioms Paper.GeneralCoveringOwnerFrameTaskInputs.value_frame
