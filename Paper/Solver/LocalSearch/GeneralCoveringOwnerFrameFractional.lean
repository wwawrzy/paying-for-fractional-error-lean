import Paper.Solver.LocalSearch.GeneralCoveringOwnerFrameTaskInputs
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalSolve
import Paper.Preliminaries.SparseParallelCorrect
import Paper.Preliminaries.RoleNumerator

/-! Executable sparse fractional solves for all locally decoded finite roles.
The owner-frame producer runs once. Every role uses the accepted actual-C
normalized fractional client, with genuine private cost/incidence payloads.
The own output is a bounded natural sum with a fixed public denominator.
Its equality to the mean of physical random outcomes remains a later theorem. -/
namespace Paper.GeneralCoveringOwnerFrameFractional
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]
open GeneralCoveringOwnerFrameTaskData GeneralCoveringOwnerFrameTaskInputs

/-- Subset masks select task parts; only coin configurations enter the mean. -/
def denominator (Δ k b n q : ℕ) : ℕ :=
  q * (2 ^ b) ^ OwnerRoleMetadata.slots (partSlots Δ k) n (frameSlots Δ k n)

def numeratorBound (L Δ a B k b n q : ℕ) : ℕ :=
  capacity L Δ k b n * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q

abbrev SparseOutput (V : Type) (L Δ a B k b n q : ℕ) :=
  (List (Role V Δ k b n × Fin (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q + 1)) ×
    SparseRolePrepare.Env V (Role V Δ k b n)) × Saved V B L Δ k n

abbrev Output (V : Type) (L Δ a B k b n q : ℕ) :=
  Fin (numeratorBound L Δ a B k b n q + 1) × SparseOutput V L Δ a B k b n q

def sparse {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (SparseOutput V L Δ a B k b n q) :=
  .seq (GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n)
    (ProgramMemory.carry (X := Saved V B L Δ k n)
      (SparseParallel.execute (TaskRoleId.code I (metadataCount Δ k b n)) (capacity L Δ k b n)
        (GeneralCoveringTaskFractionalSolve.program I a B k q hB)))

def program {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V L Δ a B k b n q) :=
  .seq (sparse I L Δ a B k t b n q hB) (.local fun _ _ s =>
    (RoleNumerator.output (capacity L Δ k b n) (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) s.1.1, s))

theorem denominator_pos (Δ k b n q : ℕ) (hq : 0 < q) : 0 < denominator Δ k b n q :=
  Nat.mul_pos hq (pow_pos (pow_pos (by omega) _) _)

theorem denominator_card (Δ k b n q : ℕ) : denominator Δ k b n q =
    q * Fintype.card (Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n) := by
  rw [denominator, Fintype.card_fun, Fintype.card_fin, GeneralCoveringOwnerFramePartitionCounts.card_bits]
  congr 1
  rw [← pow_mul, ← pow_mul]
  apply congrArg (fun z => 2 ^ z)
  simp only [OwnerRoleMetadata.slots, partSlots, GeneralCoveringOwnerFramePartitionCounts.vertexBits]
  ring

theorem output_bound {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → Input V B) (v : V) :
    (((program I L Δ a B k t b n q hB).runEncoded G s v).1).val ≤ numeratorBound L Δ a B k b n q :=
  Nat.le_of_lt_succ (Fin.isLt _)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def prepared {ids B : ℕ} (I : BitCode V ids) (L Δ k t b n : ℕ) (s : V → Input V B) :=
  (GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).runEncoded G s

theorem run_sparse {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    (sparse I L Δ a B k t b n q hB).runEncoded G s = fun v =>
      ((SparseParallel.execute (TaskRoleId.code I (metadataCount Δ k b n)) (capacity L Δ k b n)
          (GeneralCoveringTaskFractionalSolve.program I a B k q hB)).runEncoded G
        (fun u => (prepared G I L Δ k t b n s u).1) v, (prepared G I L Δ k t b n s v).2) := by
  rw [Program.runEncoded_eq_run]
  change (ProgramMemory.carry (SparseParallel.execute (TaskRoleId.code I (metadataCount Δ k b n)) (capacity L Δ k b n)
    (GeneralCoveringTaskFractionalSolve.program I a B k q hB))).run G
      ((GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).run G s) = _
  have he : (GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).run G s =
      fun v => (((GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).run G s v).1,
        ((GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).run G s v).2) := rfl
  rw [he, ProgramMemory.run]
  simp only [prepared, Program.runEncoded_eq_run]

theorem run_program {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) (s : V → Input V B) :
    (program I L Δ a B k t b n q hB).runEncoded G s = fun v =>
      (RoleNumerator.output (capacity L Δ k b n) (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q)
        (((sparse I L Δ a B k t b n q hB).runEncoded G s v).1.1),
        (sparse I L Δ a B k t b n q hB).runEncoded G s v) := rfl

theorem keys {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) (s : V → Input V B) (v : V) :
    TaggedDictionary.keys (((sparse I L Δ a B k t b n q hB).runEncoded G s v).1.1) =
      TaskRoleId.space (frames G I L Δ k n s v).anchors (metadataCount Δ k b n) := by
  rw [run_sparse, Program.runEncoded_eq_run, SparseParallelCorrect.execute_keys]
  exact GeneralCoveringOwnerFrameTaskInputs.keys G I B L Δ k t b n s v

/-- Exact accepted fractional-client execution for every locally present role.
Its carrier is computed from actual frame dictionaries, never supplied. -/
theorem lookup_role {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v)
    (v : V) (role : Role V Δ k b n) (hr : (ofLex role).1 ∈ (frames G I L Δ k n s v).anchors) :
    TaggedDictionary.lookup (((sparse I L Δ a B k t b n q hB).runEncoded G s v).1.1) role =
      some ((GeneralCoveringTaskFractionalSolve.program I a B k q hB).runEncoded
        (MaskedTaskGraph.graph G (SparseRolePrepare.vertices
          (fun u => TaggedDictionary.keys (prepared G I L Δ k t b n s u).1) role))
        (fun u => value I Δ k t b n (frames G I L Δ k n s u) (s u).2 role) v) := by
  have hstate : ∀ u, TaggedDictionary.Consistent
      (value I Δ k t b n (frames G I L Δ k n s u) (s u).2)
      (prepared G I L Δ k t b n s u).1 := by
    intro u
    unfold prepared
    rw [GeneralCoveringOwnerFrameTaskInputs.run_program]
    exact build_consistent I Δ k t b n _ _
  have hkey : role ∈ TaggedDictionary.keys (prepared G I L Δ k t b n s v).1 := by
    unfold prepared
    rw [GeneralCoveringOwnerFrameTaskInputs.keys]
    exact (TaskRoleId.mem_space _ _ role).mpr hr
  have he := SparseParallelCorrect.execute_correct G (TaskRoleId.code I (metadataCount Δ k b n))
    (capacity L Δ k b n) (GeneralCoveringTaskFractionalSolve.program I a B k q hB)
    (fun u => (prepared G I L Δ k t b n s u).1)
    (fun u => GeneralCoveringOwnerFrameTaskInputs.key_bound G I B L Δ k t b n C targets D R
      hinc hlocal s hD hR hC hTargets u)
    (fun u => value I Δ k t b n (frames G I L Δ k n s u) (s u).2) hstate v role hkey
  rw [run_sparse, Program.runEncoded_eq_run]
  simpa only [Program.runEncoded_eq_run] using he

/-- No multiplicity from repeated packet entries enters the natural sum. -/
theorem exact_sum {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B)
    (C targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v u, u ∈ targets v ↔ v ∈ C u) (hlocal : ∀ u ∈ R, C u ⊆ closed G u)
    (s : V → Input V B)
    (hD : ∀ v, (s v).1.center = decide (v ∈ D)) (hR : ∀ v, (s v).1.demand = decide (v ∈ R))
    (hC : ∀ v, (s v).1.candidates = C v) (hTargets : ∀ v, (s v).1.targets = targets v) (v : V) :
    (((program I L Δ a B k t b n q hB).runEncoded G s v).1).val =
      ∑ role ∈ TaskRoleId.space (frames G I L Δ k n s v).anchors (metadataCount Δ k b n),
        ((TaggedDictionary.lookup (((sparse I L Δ a B k t b n q hB).runEncoded G s v).1.1) role).getD 0).val := by
  rw [run_program]
  rw [RoleNumerator.output_eq _ _ _ (by
    rw [keys, ← GeneralCoveringOwnerFrameTaskInputs.keys G I B L Δ k t b n s v]
    exact GeneralCoveringOwnerFrameTaskInputs.key_bound G I B L Δ k t b n C targets D R
      hinc hlocal s hD hR hC hTargets v)]
  rw [RoleNumerator.raw, keys]

/-- Public role keys enumerate each anchor/metadata pair exactly once. -/
theorem role_sum (anchors : Finset V) (M : ℕ) (f : TaskRoleId.Id V M → ℕ) :
    (∑ role ∈ TaskRoleId.space anchors M, f role) =
      ∑ a ∈ anchors, ∑ i : Fin M, f (TaskRoleId.make a i) := by
  rw [TaskRoleId.space, Finset.sum_image (g := (toLex : V × Fin M → TaskRoleId.Id V M))
      (fun p _ q _ h => congrArg (ofLex : TaskRoleId.Id V M → V × Fin M) h),
    Finset.sum_product]
  rfl

/-- Weighted actual role answers, grouped by local Boolean configurations.
The equality applies to runtime answers, without supplying task scores. -/
theorem role_metadata_sum (anchors : Finset V) (Δ k b n : ℕ) (f : Role V Δ k b n → ℕ) :
    (∑ role ∈ TaskRoleId.space anchors (metadataCount Δ k b n), f role) =
      ∑ a ∈ anchors,
        ∑ ω : Fin (frameSlots Δ k n) → ActiveFiniteBitPartition.Bits Δ k b n,
          ∑ mask : Fin (partSlots Δ k) → Bool, f (TaskRoleId.make a (encode Δ k b n mask ω)) := by
  rw [role_sum]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [encode_decode] using sum_metadata Δ k b n
    (fun mask ω => f (TaskRoleId.make a (encode Δ k b n mask ω)))

theorem rounds {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (program I L Δ a B k t b n q hB).rounds =
      14 + 4 * outerRadius k n + RecursiveSearch.roundBound (4 * k) a
        (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) := by
  simp only [program, sparse, Program.rounds, ProgramMemory.rounds,
    GeneralCoveringOwnerFrameTaskInputs.rounds, SparseParallel.execute_rounds, GeneralCoveringTaskFractionalSolve.rounds]
  omega

theorem maxBits {ids : ℕ} (I : BitCode V ids) (L Δ a B k t b n q : ℕ) (hB : 1 ≤ B) :
    (program I L Δ a B k t b n q hB).maxBits ≤
      max (GeneralCoveringOwnerFrameTaskInputs.program I B L Δ k t b n).maxBits
        (capacity L Δ k b n * (ids + metadataCount Δ k b n +
          (GeneralCoveringTaskFractionalSolve.program I a B k q hB).maxBits + 1)) := by
  simp only [program, sparse, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero]
  exact max_le_max (le_refl _) (SparseParallel.execute_maxBits (TaskRoleId.code I (metadataCount Δ k b n))
    (capacity L Δ k b n) (GeneralCoveringTaskFractionalSolve.program I a B k q hB))

end Paper.GeneralCoveringOwnerFrameFractional

#print axioms Paper.GeneralCoveringOwnerFrameFractional.denominator_pos
#print axioms Paper.GeneralCoveringOwnerFrameFractional.output_bound
#print axioms Paper.GeneralCoveringOwnerFrameFractional.run_sparse
#print axioms Paper.GeneralCoveringOwnerFrameFractional.run_program
#print axioms Paper.GeneralCoveringOwnerFrameFractional.keys
#print axioms Paper.GeneralCoveringOwnerFrameFractional.exact_sum

#print axioms Paper.GeneralCoveringOwnerFrameFractional.lookup_role

#print axioms Paper.GeneralCoveringOwnerFrameFractional.denominator_card

#print axioms Paper.GeneralCoveringOwnerFrameFractional.role_sum
#print axioms Paper.GeneralCoveringOwnerFrameFractional.role_metadata_sum

#print axioms Paper.GeneralCoveringOwnerFrameFractional.rounds
#print axioms Paper.GeneralCoveringOwnerFrameFractional.maxBits
