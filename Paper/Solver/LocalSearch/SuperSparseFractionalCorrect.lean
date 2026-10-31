import Paper.Solver.LocalSearch.SparseFractional
import Paper.Solver.LocalSearch.SuperMaskedFractionalSearch

/-! Every valid actual task role in a sparse parallel execution inherits
the complete original-task fractional guarantee. Role construction remains
a separate dependency, expressed here by exact local record membership. -/
namespace Paper.SuperSparseFractionalCorrect
open BroadcastModel SevenFoundation
variable {V Role : Type} [Fintype V] [LinearOrder V] [LinearOrder Role]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem spec (D R : Finset V) (L : ℕ) (Q : Finset D) (I J : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (a : ℕ) (ha' : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (c : V → Fin (B + 1)) (hc' : ∀ v, 1 ≤ (c v).val) (ξ : ℝ) (hξ : 0 < ξ)
    {b d : ℕ} (C : BitCode V b) (CR : BitCode Role d) (K : ℕ)
    (xs : V → List (Role × FractionalSearch.Input V B))
    (hK : ∀ v, (TaggedDictionary.keys (xs v)).card ≤ K)
    (s : V → Role → FractionalSearch.Input V B) (hs : ∀ v, TaggedDictionary.Consistent (s v) (xs v))
    (r : Role) (hr : ∀ v ∈ PhysicalTasks.vertices G D R L Q I, r ∈ TaggedDictionary.keys (xs v))
    (ha : ∀ v, (s v r).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v r).cost = c v)
    (hd : ∀ v, (s v r).demand = decide (v ∈ OwnerTasks.demands G D R L Q I J)) :
    let H := PhysicalTasks.vertices G D R L Q I
    let q := LocalSolverMath.denominator a ξ
    let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
    let p := fun v => ((TaggedDictionary.lookup
      (((SparseFractional.program C CR K (4 * k) a B q M).run G xs v).1) r).getD 0).val
    let z := fun v : ↥(H : Set V) => (p v.val : ℝ) / q
    PartialOptimum.Feasible (G.induce (H : Set V))
        (InducedSubsets.lift H (OwnerTasks.demands G D R L Q I J)) z ∧
      PartialOptimum.objective (fun v : ↥(H : Set V) => ((c v.val).val : ℝ)) z ≤
        (1 + ξ) * TaskOptimum.number G D R L Q I J (fun v => ((c v).val : ℝ)) ∧
      ∀ v, (q : ℝ) * z v = p v.val := by
  dsimp only
  let H := PhysicalTasks.vertices G D R L Q I
  let q := LocalSolverMath.denominator a ξ
  let M := ⌈(q + 2 * (a : ℝ)) * ((B : ℝ) * k)⌉₊
  let F := SparseRolePrepare.vertices (fun u => TaggedDictionary.keys (xs u)) r
  have hHF : H ⊆ F := fun v hv => (SparseRolePrepare.mem_vertices _ r v).mpr (hr v hv)
  have hscalar := SuperMaskedFractionalSearch.spec G D R L Q I J hI k hsize F hHF a ha' hden B c hc' ξ hξ C
    (fun v => s v r) ha hc hd
  have hp : ∀ v ∈ H, (TaggedDictionary.lookup
      (((SparseFractional.program C CR K (4 * k) a B q M).run G xs v).1) r).getD 0 =
        (FractionalSearch.program C (4 * k) a B q M).run (MaskedTaskGraph.graph G F) (fun u => s u r) v := by
    intro v hv
    rw [SparseFractional.key_run G C CR K (4 * k) a B q M xs hK s hs v r (hr v hv)]
    rfl
  have he : (fun v : ↥(H : Set V) =>
      (((TaggedDictionary.lookup (((SparseFractional.program C CR K (4 * k) a B q M).run G xs v.val).1) r).getD 0).val : ℝ) / q) =
        (fun v : ↥(H : Set V) =>
          (((FractionalSearch.program C (4 * k) a B q M).run (MaskedTaskGraph.graph G F) (fun u => s u r) v.val).val : ℝ) / q) := by
    funext v
    rw [hp v.val v.property]
  rw [he]
  refine ⟨hscalar.1, hscalar.2.1, ?_⟩
  intro v
  rw [hp v.val v.property]
  exact hscalar.2.2.1 v
end Paper.SuperSparseFractionalCorrect
