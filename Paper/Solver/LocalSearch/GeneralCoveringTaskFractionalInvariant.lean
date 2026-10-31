import Paper.Solver.LocalSearch.GeneralCoveringFractionalInvariant
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalParallel
import Paper.Averaging.Tasks.SuperMaskedTask

/-! Extra inactive sparse-role participants preserve the exact accepted
task numerator. All connectivity, demanded rows and normalization broadcasts
are derived for the actual original-C physical task. -/
namespace Paper.GeneralCoveringTaskFractionalInvariant
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inactive {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringFractional.Input V B) (v : V) (hv : (s v).active = false) :
    (GeneralCoveringTaskFractionalSolve.program ids a B k q hB).runEncoded G s v = 0 := by
  rw [GeneralCoveringTaskFractionalSolve.run_program, Program.runEncoded_eq_run,
    GeneralCoveringFractional.run_program]
  have hn : (GeneralCoveringNormalizedFractional.normalized G B hB s v).active = false :=
    (GeneralCoveringInputNormalization.metadata G B hB s v).1.trans hv
  simp only [hn, Bool.false_eq_true, if_false]

noncomputable def context (K : ActiveTask.Context G) (F : Finset V) (hF : K.vertices ⊆ F) :
    ActiveTask.Context (MaskedTaskGraph.graph G F) where
  vertices := K.vertices
  nonempty := K.nonempty
  diameter := K.diameter
  paths := by
    intro x y
    rw [SuperMaskedTask.induced_eq G F K.vertices hF]
    exact K.paths x y

theorem masked (K : ActiveTask.Context G) (F : Finset V) (hF : K.vertices ⊆ F)
    (cover targets : V → Finset V) (T : Finset V) (hT : T ⊆ K.vertices)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ T, cover r ⊆ closed G r)
    (hrows : ∀ r ∈ T, cover r ⊆ K.vertices)
    {bits : ℕ} (ids : BitCode V bits) (a B q M : ℕ) (hB : 1 ≤ B)
    (cost : V → Fin (B + 1)) :
    (GeneralCoveringNormalizedFractional.program ids K.diameter a B q M hB).runEncoded
        (MaskedTaskGraph.graph G F)
        (GeneralCoveringTaskFractionalParallel.taskInput cover targets K.vertices T cost) =
      (GeneralCoveringNormalizedFractional.program ids K.diameter a B q M hB).runEncoded
        (MaskedTaskGraph.graph G K.vertices)
        (GeneralCoveringTaskFractionalParallel.taskInput cover targets K.vertices T cost) := by
  let KF := context G K F hF
  let KH := context G K K.vertices (Finset.Subset.refl _)
  have hFG : ∀ r ∈ T, cover r ⊆ closed (MaskedTaskGraph.graph G F) r := by
    intro r hr
    rw [MaskedTaskGraph.closed_inside G F r (hF (hT hr))]
    exact Finset.subset_inter (hlocal r hr) (fun _ hu => hF (hrows r hr hu))
  have hHG : ∀ r ∈ T, cover r ⊆ closed (MaskedTaskGraph.graph G K.vertices) r := by
    intro r hr
    rw [MaskedTaskGraph.closed_inside G K.vertices r (hT hr)]
    exact Finset.subset_inter (hlocal r hr) (hrows r hr)
  exact GeneralCoveringFractionalInvariant.normalized
    (MaskedTaskGraph.graph G F) (MaskedTaskGraph.graph G K.vertices) KF KH rfl
    (fun u hu v hv => ⟨fun h => ⟨h.1, hu, hv⟩, fun h => ⟨h.1, hF hu, hF hv⟩⟩)
    cover targets T hT hinc hFG hHG ids a B q M hB
    (GeneralCoveringTaskFractionalParallel.taskInput cover targets K.vertices T cost)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The right side is the literal per-part client used by the accepted
physical randomized pipeline; no score or output equality is assumed. -/
theorem part {bits L B : ℕ} {s : V → GeneralCoveringTaskFractionalParallel.Input V B}
    (ids : BitCode V bits) (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (F : Finset V)
    (hF : vertices G g.cover g.D g.R L g.Q I ⊆ F)
    (a q : ℕ) (hB : 1 ≤ B) :
    (GeneralCoveringTaskFractionalSolve.program ids a B g.k q hB).runEncoded
        (MaskedTaskGraph.graph G F)
        (GeneralCoveringTaskFractionalParallel.taskInput g.cover g.targets
          (vertices G g.cover g.D g.R L g.Q I)
          (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun v => (s v).2.cost)) =
      GeneralCoveringTaskFractionalParallel.clientOutput G ids g I a q hB := by
  let K := GeneralCoveringTaskDiameter.partContext G g.cover g.D g.R L g.Q g.local_rows g.k g.P I hI
  exact masked G K F hF g.cover g.targets _
    (demands_in_vertices G g.cover g.D g.R L g.Q I g.Bdy) g.incidence
    (fun r hr => g.local_rows r (demands_subset G g.cover g.D g.R L g.Q I g.Bdy hr))
    (rows_in_vertices G g.cover g.D g.R L g.Q I g.Bdy g.local_rows)
    ids a B q (GeneralCoveringTaskFractionalSolve.numeratorBound a B g.k q) hB (fun v => (s v).2.cost)

/-- The actual sparse dictionary reconstructs the whole per-part vector,
including its zero value at absent participants, without LP assumptions. -/
theorem part_numerator {bits L B : ℕ} {s : V → GeneralCoveringTaskFractionalParallel.Input V B}
    (ids : BitCode V bits) (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (a q : ℕ) (hB : 1 ≤ B) :
    GeneralCoveringTaskFractionalParallel.numerator
      ((GeneralCoveringTaskFractionalParallel.program ids L a B g.k q hB).runEncoded G s)
      (GeneralCoveringTaskRoles.roleID G g I hI) =
        (fun v => (GeneralCoveringTaskFractionalParallel.clientOutput G ids g I a q hB v).val) := by
  funext v
  by_cases hv : v ∈ vertices G g.cover g.D g.R L g.Q I
  · simp only [GeneralCoveringTaskFractionalParallel.numerator,
      GeneralCoveringTaskFractionalParallel.lookup_part G ids g I hI a q hB v hv,
      Option.map_some, Option.getD_some, GeneralCoveringTaskFractionalParallel.clientOutput]
  · have hz := inactive (MaskedTaskGraph.graph G (vertices G g.cover g.D g.R L g.Q I))
      ids a B g.k q hB
      (GeneralCoveringTaskFractionalParallel.taskInput g.cover g.targets
        (vertices G g.cover g.D g.R L g.Q I) (demands G g.cover g.D g.R L g.Q I g.Bdy)
        (fun u => (s u).2.cost)) v (decide_eq_false hv)
    simp only [GeneralCoveringTaskFractionalParallel.numerator,
      GeneralCoveringTaskFractionalParallel.lookup_outside G ids g I hI a q hB v hv,
      Option.map_none, Option.getD_none]
    exact (congrArg Fin.val hz).symm

end Paper.GeneralCoveringTaskFractionalInvariant

#print axioms Paper.GeneralCoveringTaskFractionalInvariant.masked
#print axioms Paper.GeneralCoveringTaskFractionalInvariant.part
#print axioms Paper.GeneralCoveringTaskFractionalInvariant.inactive
#print axioms Paper.GeneralCoveringTaskFractionalInvariant.part_numerator
