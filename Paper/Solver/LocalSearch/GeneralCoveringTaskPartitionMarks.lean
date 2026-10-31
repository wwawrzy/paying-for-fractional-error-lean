import Paper.Partitions.Local.DeterministicPartitionBoundaryProgram
import Paper.Partitions.Local.PublicPartitionPullback
import Paper.Solver.LocalSearch.GeneralCoveringTaskRoles

/-! Actual computed partition/boundary labels produce local canonical center
roles and interior marks. Private active/cost input survives by ProgramMemory.
The executable never receives a partition, full label, boundary or inverse
embedding. PublicEmbedding is a virtual-graph execution interface only; its
physical owner routing and the actual high/low producer are separate gates. -/
namespace Paper.GeneralCoveringTaskPartitionMarks
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [LinearOrder V]

abbrev Input (B : ℕ) := Bool × Fin (B + 1)

def prepare (B : ℕ) : Program V (Input B) (Bool × Input B) :=
  .local (fun _ _ s => (s.1, s))

def marks {B : ℕ} (s : Input B) (label : Finset V) (boundary : Bool) : GeneralCoveringTaskRoles.Fields V B :=
  GeneralCoveringTaskRoles.fromLabel s.2 (if s.1 then label else ∅) (s.1 && !boundary)

def finish (B : ℕ) : Program V ((Finset V × Bool) × Input B) (GeneralCoveringTaskRoles.Fields V B) :=
  .local (fun _ _ s => marks s.2 s.1.1 s.1.2)

/-- Public natural program, independent of graph and any partition data. -/
def program {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) :
    Program V (Input B) (GeneralCoveringTaskRoles.Fields V B) :=
  .seq (prepare B) (.seq (ProgramMemory.carry (X := Input B)
    (DeterministicPartitionBoundaryProgram.program ids Δ k t T)) (finish B))

section Graph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem carry_run {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (s : V → Input B) :
    (ProgramMemory.carry (X := Input B) (DeterministicPartitionBoundaryProgram.program ids Δ k t T)).runEncoded G
      (fun v => ((s v).1, s v)) = fun v =>
        ((DeterministicPartitionBoundaryProgram.program ids Δ k t T).runEncoded G (fun u => (s u).1) v, s v) := by
  rw [Program.runEncoded_eq_run G (ProgramMemory.carry (X := Input B)
    (DeterministicPartitionBoundaryProgram.program ids Δ k t T)), ProgramMemory.run,
    Program.runEncoded_eq_run G (DeterministicPartitionBoundaryProgram.program ids Δ k t T)]

theorem run_program {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (s : V → Input B) (v : V) :
    (program ids Δ k t T B).runEncoded G s v =
      marks (s v) ((DeterministicPartitionBoundaryProgram.program ids Δ k t T).runEncoded G
        (fun u => (s u).1) v).1 ((DeterministicPartitionBoundaryProgram.program ids Δ k t T).runEncoded G
          (fun u => (s u).1) v).2 := by
  change (finish B).runEncoded G ((ProgramMemory.carry (X := Input B)
    (DeterministicPartitionBoundaryProgram.program ids Δ k t T)).runEncoded G (fun u => ((s u).1, s u))) v = _
  rw [carry_run]
  rfl

theorem cost {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (s : V → Input B) (v : V) :
    ((program ids Δ k t T B).runEncoded G s v).cost = (s v).2 :=
  congrArg (fun f : GeneralCoveringTaskRoles.Fields V B => f.cost) (run_program G ids Δ k t T B s v)

/-- Exclusion follows from the private inactive bit even outside the geometric contract. -/
theorem inactive {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (s : V → Input B) (v : V)
    (hv : (s v).1 = false) :
    (program ids Δ k t T B).runEncoded G s v = ⟨(s v).2, none, false⟩ := by
  rw [run_program]
  simp [marks, hv, GeneralCoveringTaskRoles.fromLabel, MaskedMinimum.minimum]

/-- Full fields refer to the same actual computed partition and exact boundary. -/
theorem correct {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ v, G.degree v ≤ Δ) (S : Finset V) (c : V → Fin (B + 1)) (v : V) :
    (program ids Δ k t T B).runEncoded G (fun u => (decide (u ∈ S), c u)) v =
      GeneralCoveringTaskRoles.fromLabel (c v)
        (DisjointPartLabels.label (DeterministicPartitionComputedProgram.partition G ids Δ hdeg k hk t ht S T).parts v)
        (decide (v ∈ S ∧ v ∉ BoundaryOwners.vertices G S
          (DeterministicPartitionComputedProgram.partition G ids Δ hdeg k hk t ht S T).parts)) := by
  rw [run_program, DeterministicPartitionBoundaryProgram.correct G ids Δ k t T hk ht hdeg S v]
  by_cases hv : v ∈ S
  · by_cases hb : v ∈ BoundaryOwners.vertices G S
        (DeterministicPartitionComputedProgram.partition G ids Δ hdeg k hk t ht S T).parts
    · simp [marks, hv, hb]
    · simp [marks, hv, hb]
  · have hl := DisjointPartLabels.outside G S k
      (DeterministicPartitionComputedProgram.partition G ids Δ hdeg k hk t ht S T) v hv
    simp [marks, hv, hl]

theorem empty_active {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (c : V → Fin (B + 1)) (v : V) :
    (program ids Δ k t T B).runEncoded G (fun u => (decide (u ∈ (∅ : Finset V)), c u)) v =
      ⟨c v, none, false⟩ := by
  apply inactive G ids Δ k t T B _ v
  rfl

theorem empty_public [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (s : V → Input B) :
    (program ids Δ k t T B).runEncoded G s = fun v => (⟨(s v).2, none, false⟩ : GeneralCoveringTaskRoles.Fields V B) := by
  funext v
  exact isEmptyElim v

end Graph

theorem rounds_eq {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) :
    (program ids Δ k t T B).rounds = (DeterministicPartitionBoundaryProgram.program ids Δ k t T).rounds := by
  simp only [program, prepare, finish, Program.rounds, ProgramMemory.rounds, Nat.zero_add, Nat.add_zero]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) :
    (program ids Δ k t T B).maxBits = (DeterministicPartitionBoundaryProgram.program ids Δ k t T).maxBits := by
  simp only [program, prepare, finish, Program.maxBits, ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]

theorem costs [Fintype V] {bits : ℕ} (ids : BitCode V bits) (Δ k t T B c p d M : ℕ)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ d) :
    (program ids Δ k t T B).rounds ≤ DeterministicPartitionBoundaryProgram.roundCoefficient Δ k T c p d *
      (1 + DeterministicColorReductionLogStar.logStar (Fintype.card V)) ∧
    (program ids Δ k t T B).maxBits ≤ DeterministicPartitionBoundaryProgram.bitCoefficient Δ k c p d *
      Nat.clog 2 (Fintype.card V + 2) := by
  rw [rounds_eq, maxBits_eq]
  exact DeterministicPartitionBoundaryProgram.costs ids Δ k t T c p d M hbits hM

section Public
variable [Fintype V] {W : Type} [Fintype W] [DecidableEq W]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)

noncomputable local instance mappedAdj : DecidableRel (PublicEmbedding.graph J e).Adj :=
  fun _ _ => Classical.propDecidable _

def activeImage : Finset V := Finset.univ.image e

theorem activeImage_iff (v : V) : v ∈ activeImage e ↔ v ∈ Set.range e := by
  simp only [activeImage, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]

noncomputable def publicPartition {bits : ℕ} (ids : BitCode V bits) (Δ k t T : ℕ)
    (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ w, J.degree w ≤ Δ) :
    SmallParts.Data (PublicEmbedding.graph J e) (activeImage e) k :=
  DeterministicPartitionComputedProgram.partition (PublicEmbedding.graph J e) ids Δ
    (PublicEmbedding.degree_bound J e Δ hdeg) k hk t ht (activeImage e) T

noncomputable def pulledPartition {bits : ℕ} (ids : BitCode V bits) (Δ k t T : ℕ)
    (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ w, J.degree w ≤ Δ) : SmallParts.Data J Finset.univ k :=
  PublicPartitionPullback.data J e (activeImage e) k (activeImage_iff e)
    (publicPartition J e ids Δ k t T hk ht hdeg)

/-- No public IDs are lost when an actual public part is pulled back. -/
theorem image_part (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) (I : Finset V) (hI : I ∈ P.parts) :
    (PublicPartPullback.pull e I).image e = I :=
  PublicPartPullback.image_pull e I (fun v hv => (hS v).mp (P.subset I hI hv))

theorem label_part_image (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) (U : Finset W)
    (hU : U ∈ (PublicPartitionPullback.data J e S k hS P).parts) (w : W) (hw : w ∈ U) :
    DisjointPartLabels.label P.parts (e w) = U.image e := by
  change U ∈ P.parts.image (PublicPartPullback.pull e) at hU
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hU
  exact (DisjointPartLabels.eq_of_mem P.parts P.disjoint I hI (e w) ((PublicPartPullback.mem_pull e I w).mp hw)).trans
    (image_part J e S k hS P I hI).symm

/-- Complete label equality, including the actual pullback label at each virtual vertex. -/
theorem label_image (S : Finset V) (k : ℕ) (hS : ∀ v, v ∈ S ↔ v ∈ Set.range e)
    (P : SmallParts.Data (PublicEmbedding.graph J e) S k) (w : W) :
    (DisjointPartLabels.label (PublicPartitionPullback.data J e S k hS P).parts w).image e =
      DisjointPartLabels.label P.parts (e w) := by
  let Q := PublicPartitionPullback.data J e S k hS P
  obtain ⟨U, hU, hw⟩ := Q.covers w (Finset.mem_univ w)
  rw [DisjointPartLabels.eq_of_mem Q.parts Q.disjoint U hU w hw]
  exact (label_part_image J e S k hS P U hU w hw).symm

/-- Fields are computed on the public embedded graph and name exactly the
image of the actual pulled-back part. Boundary is the exact pulled-back boundary. -/
theorem embedded_part {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ)
    (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ w, J.degree w ≤ Δ) (c : V → Fin (B + 1))
    (U : Finset W) (hU : U ∈ (pulledPartition J e ids Δ k t T hk ht hdeg).parts) (w : W) (hw : w ∈ U) :
    (program ids Δ k t T B).runEncoded (PublicEmbedding.graph J e)
      (fun v => (decide (v ∈ activeImage e), c v)) (e w) =
      GeneralCoveringTaskRoles.fromLabel (c (e w)) (U.image e)
        (decide (w ∉ BoundaryOwners.vertices J Finset.univ
          (pulledPartition J e ids Δ k t T hk ht hdeg).parts)) := by
  have he := correct (PublicEmbedding.graph J e) ids Δ k t T B hk ht
    (PublicEmbedding.degree_bound J e Δ hdeg) (activeImage e) c (e w)
  have hl := label_part_image J e (activeImage e) k (activeImage_iff e)
    (publicPartition J e ids Δ k t T hk ht hdeg) U hU w hw
  have hb := PublicPartitionPullback.boundary J e (activeImage e) k (activeImage_iff e)
    (publicPartition J e ids Δ k t T hk ht hdeg) w
  have ha : e w ∈ activeImage e := (activeImage_iff e (e w)).mpr ⟨w, rfl⟩
  have hm : decide (e w ∈ activeImage e ∧ e w ∉ BoundaryOwners.vertices (PublicEmbedding.graph J e)
      (activeImage e) (publicPartition J e ids Δ k t T hk ht hdeg).parts) =
      decide (w ∉ BoundaryOwners.vertices J Finset.univ (pulledPartition J e ids Δ k t T hk ht hdeg).parts) := by
    apply Bool.decide_congr
    exact ⟨fun h => fun hbad => h.2 (hb.mp hbad), fun h => ⟨ha, fun hbad => h (hb.mpr hbad)⟩⟩
  change _ = GeneralCoveringTaskRoles.fromLabel (c (e w)) (U.image e)
    (decide (w ∉ BoundaryOwners.vertices J Finset.univ (pulledPartition J e ids Δ k t T hk ht hdeg).parts))
  exact he.trans (congrArg₂ (GeneralCoveringTaskRoles.fromLabel (c (e w))) hl hm)

theorem embedded_interior {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ)
    (hk : 0 < k) (ht : 0 < t) (hdeg : ∀ w, J.degree w ≤ Δ) (c : V → Fin (B + 1)) (w : W) :
    ((program ids Δ k t T B).runEncoded (PublicEmbedding.graph J e)
      (fun v => (decide (v ∈ activeImage e), c v)) (e w)).interior =
      decide (w ∉ BoundaryOwners.vertices J Finset.univ (pulledPartition J e ids Δ k t T hk ht hdeg).parts) := by
  obtain ⟨U, hU, hw⟩ := (pulledPartition J e ids Δ k t T hk ht hdeg).covers w (Finset.mem_univ w)
  exact congrArg (fun f : GeneralCoveringTaskRoles.Fields V B => f.interior)
    (embedded_part J e ids Δ k t T B hk ht hdeg c U hU w hw)

theorem outside_image {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (c : V → Fin (B + 1))
    (v : V) (hv : v ∉ Set.range e) :
    (program ids Δ k t T B).runEncoded (PublicEmbedding.graph J e)
      (fun u => (decide (u ∈ activeImage e), c u)) v = ⟨c v, none, false⟩ := by
  apply inactive (PublicEmbedding.graph J e) ids Δ k t T B _ v
  have hn : v ∉ activeImage e := fun h => hv ((activeImage_iff e v).mp h)
  simp only [hn, decide_false]

theorem empty_virtual [IsEmpty W] {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ)
    (c : V → Fin (B + 1)) (v : V) :
    (program ids Δ k t T B).runEncoded (PublicEmbedding.graph J e)
      (fun u => (decide (u ∈ activeImage e), c u)) v = ⟨c v, none, false⟩ := by
  apply outside_image J e ids Δ k t T B c v
  rintro ⟨w, _⟩
  exact isEmptyElim w

end Public

section Low
variable [Fintype V]

def lowEmbedding (D : Finset V) (Q : Finset D) : Low D Q ↪ V where
  toFun i := i.val.val
  inj' _ _ h := Subtype.ext (Subtype.ext h)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowMappedAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicEmbedding.graph (graph G cover D R L Q) (lowEmbedding D Q)).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The exact low-owner names/interior correspondence consumed by Roles and
TaskAggregate. The graph here is virtual; no physical routing is claimed. -/
theorem low_fields (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    {bits : ℕ} (ids : BitCode V bits) (Δ k t T B : ℕ) (hk : 0 < k) (ht : 0 < t)
    (hdeg : ∀ i : Low D Q, (graph G cover D R L Q).degree i ≤ Δ) (c : V → Fin (B + 1)) :
    let J := graph G cover D R L Q
    let e := lowEmbedding D Q
    let P := pulledPartition J e ids Δ k t T hk ht hdeg
    let fields := (program ids Δ k t T B).runEncoded (PublicEmbedding.graph J e)
      (fun v => (decide (v ∈ activeImage e), c v))
    (∀ v, (fields v).cost = c v) ∧
      (∀ (U : Finset (Low D Q)) (hU : U ∈ P.parts) (i : Low D Q), i ∈ U →
        (fields i.val.val).role = some (GeneralCoveringTaskRoles.name D Q U (P.nonempty U hU))) ∧
      (∀ d : D, d ∈ Q → (fields d.val).role = none) ∧
      (∀ i : Low D Q, (fields i.val.val).interior =
        decide (i ∉ BoundaryOwners.vertices J Finset.univ P.parts)) := by
  dsimp only
  let J := graph G cover D R L Q
  let e := lowEmbedding D Q
  let P := pulledPartition J e ids Δ k t T hk ht hdeg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    exact cost (PublicEmbedding.graph J e) ids Δ k t T B _ v
  · intro U hU i hi
    have he := congrArg (fun f : GeneralCoveringTaskRoles.Fields V B => f.role)
      (embedded_part J e ids Δ k t T B hk ht hdeg c U hU i hi)
    exact he.trans (GeneralCoveringTaskRoles.name_option D Q U (P.nonempty U hU))
  · intro d hd
    have hn : d.val ∉ Set.range e := by
      rintro ⟨i, hi⟩
      have hid : i.val = d := Subtype.ext hi
      exact i.property (hid.symm ▸ hd)
    exact congrArg (fun f : GeneralCoveringTaskRoles.Fields V B => f.role)
      (outside_image J e ids Δ k t T B c d.val hn)
  · intro i
    exact embedded_interior J e ids Δ k t T B hk ht hdeg c i

end Low
end Paper.GeneralCoveringTaskPartitionMarks

#print axioms Paper.GeneralCoveringTaskPartitionMarks.carry_run
#print axioms Paper.GeneralCoveringTaskPartitionMarks.run_program
#print axioms Paper.GeneralCoveringTaskPartitionMarks.cost
#print axioms Paper.GeneralCoveringTaskPartitionMarks.inactive
#print axioms Paper.GeneralCoveringTaskPartitionMarks.correct
#print axioms Paper.GeneralCoveringTaskPartitionMarks.empty_active
#print axioms Paper.GeneralCoveringTaskPartitionMarks.empty_public
#print axioms Paper.GeneralCoveringTaskPartitionMarks.rounds_eq
#print axioms Paper.GeneralCoveringTaskPartitionMarks.maxBits_eq
#print axioms Paper.GeneralCoveringTaskPartitionMarks.costs
#print axioms Paper.GeneralCoveringTaskPartitionMarks.activeImage_iff
#print axioms Paper.GeneralCoveringTaskPartitionMarks.pulledPartition
#print axioms Paper.GeneralCoveringTaskPartitionMarks.image_part
#print axioms Paper.GeneralCoveringTaskPartitionMarks.label_part_image
#print axioms Paper.GeneralCoveringTaskPartitionMarks.label_image
#print axioms Paper.GeneralCoveringTaskPartitionMarks.embedded_part
#print axioms Paper.GeneralCoveringTaskPartitionMarks.embedded_interior
#print axioms Paper.GeneralCoveringTaskPartitionMarks.outside_image
#print axioms Paper.GeneralCoveringTaskPartitionMarks.empty_virtual
#print axioms Paper.GeneralCoveringTaskPartitionMarks.low_fields
