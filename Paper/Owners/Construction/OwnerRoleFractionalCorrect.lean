import Paper.Owners.Construction.OwnerRoleSolver
import Paper.Owners.Construction.OwnerRoleTaskSound
import Paper.Owners.Construction.OwnerRoleCoverage
import Paper.Preliminaries.RoleInputSemantics
import Paper.Solver.LocalSearch.SuperSparseFractionalCorrect

/-! Full original physical-task LP guarantee for every valid role of the
actual role-construction/sparse-solver program. No role-input/capacity/task
correctness premise replaces the actual construction. -/
namespace Paper.OwnerRoleFractionalCorrect
open BroadcastModel SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (D R : Finset V) (L : ℕ) :
    DecidableRel (OwnerInteraction.graph G D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance lowAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (OwnerTasks.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance publicAdj (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (PublicOwners.graph G D R L Q).Adj := fun _ _ => Classical.propDecidable _

set_option maxHeartbeats 1000000 in
theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (hcover : R ⊆ covered G D)
    (L Δ r k : ℕ) (hk : 0 < k) (t : ℕ) (ht : 0 < t) (Q T s : ℕ) (hQ : 0 < Q)
    (hks : k + s ≤ r) (hs : k + (T * (3 * k + 1) + 1) ≤ s)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (c : V → Fin (B + 1)) (hc : ∀ v, 1 ≤ (c v).val) (ξ : ℝ) (hξ : 0 < ξ)
    (role : TaskRoleId.Id V (OwnerRoleInputs.metadataCount Δ k Q T s))
    (hanchor : (ofLex role).1 ∈ PublicOwners.image D (OwnerVirtualFacts.high G D R L Δ))
    (hvalid : (OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ role).valid = true) :
    let d := OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ role
    let Qlow := OwnerVirtualFacts.high G D R L Δ
    ∃ ζ : V → PriorityPartitionBroadcast.Table Δ k Q T,
      let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
      let boundary := BoundaryOwners.vertices (PublicOwners.graph G D R L Qlow) (PublicOwners.image D Qlow) P.parts
      let I := OwnerPublicTasks.pull D Qlow d.owners
      let J := OwnerPublicTasks.pull D Qlow boundary
      let H := PhysicalTasks.vertices G D R L Qlow I
      let q := LocalSolverMath.denominator a ξ
      let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
      let p := fun v => ((TaggedDictionary.lookup
        (((OwnerRoleSolver.program C L Δ r k t Q T s a B q M hQ).run G
          (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u)) v).1) role).getD 0).val
      let z := fun v : ↥(H : Set V) => (p v.val : ℝ) / q
      PartialOptimum.Feasible (G.induce (H : Set V)) (InducedSubsets.lift H (OwnerTasks.demands G D R L Qlow I J)) z ∧
        PartialOptimum.objective (fun v : ↥(H : Set V) => ((c v.val).val : ℝ)) z ≤
          (1 + ξ) * TaskOptimum.number G D R L Qlow I J (fun v => ((c v).val : ℝ)) ∧
        ∀ v, (q : ℝ) * z v = p v.val := by
  let d := OwnerRoleInputsCorrect.task G C D R L Δ k t Q T s hQ role
  let Qlow := OwnerVirtualFacts.high G D R L Δ
  obtain ⟨ζ, hz⟩ := OwnerRoleTaskSound.sound G C D R L Δ k hk t ht Q T s hQ hs (ofLex role).1 hanchor (ofLex role).2
  obtain ⟨hpart, hboundary⟩ := hz hvalid
  let P := OwnerRoleTaskSound.partition G D R L Δ k hk t Q T hQ ζ
  let boundary := BoundaryOwners.vertices (PublicOwners.graph G D R L Qlow) (PublicOwners.image D Qlow) P.parts
  let I := OwnerPublicTasks.pull D Qlow d.owners
  let J := OwnerPublicTasks.pull D Qlow boundary
  have hsub : d.owners ⊆ PublicOwners.image D Qlow := P.subset d.owners hpart
  have hI : ((OwnerTasks.graph G D R L Qlow).induce (I : Set _)).Connected :=
    OwnerPublicTasks.connected G D R L Qlow d.owners hsub (P.connected d.owners hpart)
  have hsize : I.card ≤ k := by
    rw [OwnerPublicTasks.card D Qlow d.owners hsub]
    exact P.size d.owners hpart
  let xs := (OwnerRoleInputs.program C L Δ r k t Q T s B hQ).run G
    (fun u => ((decide (u ∈ D), decide (u ∈ R)), c u))
  let family := OwnerRoleInputsCorrect.expected G C D R L Δ k t Q T s B hQ c
  have hK : ∀ v, (TaggedDictionary.keys (xs v)).card ≤ OwnerRoleInputs.capacity L Δ k Q T s :=
    fun v => OwnerRoleInputs.key_bound G C D R hcover L Δ r k t Q T s B hQ (by omega) c v
  have hfamily : ∀ v, TaggedDictionary.Consistent (family v) (xs v) :=
    fun v => OwnerRoleInputsCorrect.consistent G C D R hcover L Δ r k t Q T s B hQ hks c v
  have hroles : ∀ v ∈ PhysicalTasks.vertices G D R L Qlow I, role ∈ TaggedDictionary.keys (xs v) := by
    apply OwnerRoleCoverage.task_covered G C D R hcover L Δ r k t Q T s B hQ (by omega) c role I hI hsize
    rw [OwnerPublicTasks.centers D Qlow d.owners hsub]
    exact RoleTaskChecks.valid_anchor C Δ k t Q T ((Δ + 1) ^ s) hQ (ofLex role).1 (ofLex role).2 _ hvalid
  refine ⟨ζ, ?_⟩
  exact SuperSparseFractionalCorrect.spec G D R L Qlow I J hI k hsize a ha hden B c hc ξ hξ C
    (TaskRoleId.code C (OwnerRoleInputs.metadataCount Δ k Q T s)) (OwnerRoleInputs.capacity L Δ k Q T s)
    xs hK family hfamily role hroles
    (fun v => RoleInputSemantics.active G D R L Qlow d hvalid hsub c v)
    (fun v => RoleInputSemantics.cost G D R L d c v)
    (fun v => RoleInputSemantics.demand G D R L Qlow d hvalid hsub boundary hboundary c v)

end Paper.OwnerRoleFractionalCorrect
