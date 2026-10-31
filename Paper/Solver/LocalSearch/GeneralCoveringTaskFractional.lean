import Paper.Solver.LocalSearch.GeneralCoveringTaskGeometry

/-! Fractional restriction and LP sums for the exact arbitrary-C tasks.
Physical regions may overlap; only true useful service sets are disjoint.
The partition is analysis data, with no executable/oracle-partition claim.
Global nonnegative costs are explicit in the core LP statements. A proved
extension supplies that interface from costs known only on admissible vertices. -/
namespace Paper.GeneralCoveringTaskFractional
open SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]

theorem objective_nonneg (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v) :
    0 ≤ CoveringOptimum.objective c x :=
  Finset.sum_nonneg (fun v _ => mul_nonneg (hc v) (hx v))

theorem values_bddBelow (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) : BddBelow (CoveringOptimum.values C R c) := by
  refine ⟨0, ?_⟩
  rintro t ⟨x, hx, rfl⟩
  exact objective_nonneg c x hc hx.1

theorem number_le_objective (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (x : V → ℝ) (hx : CoveringOptimum.Feasible C R x) :
    CoveringOptimum.number C R c ≤ CoveringOptimum.objective c x := by
  exact csInf_le (values_bddBelow C R c hc) ⟨x, hx, rfl⟩

/-- The empty LP has value zero, proved with the zero vector rather than
assuming that an optimizer exists for a nonempty demand set. -/
theorem number_empty (C : V → Finset V) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    CoveringOptimum.number C ∅ c = 0 := by
  have hz : CoveringOptimum.Feasible C ∅ (fun _ => 0) := ⟨fun _ => le_rfl, by simp⟩
  have hl : IsLeast (CoveringOptimum.values C ∅ c) 0 := by
    refine ⟨⟨fun _ => 0, hz, by simp [CoveringOptimum.objective]⟩, ?_⟩
    rintro t ⟨x, hx, rfl⟩
    exact objective_nonneg c x hc hx.1
  exact hl.csInf_eq

def indicator (W : Finset V) (v : V) : ℝ := if v ∈ W then 1 else 0

theorem indicator_feasible (C : V → Finset V) (R W : Finset V)
    (hW : GeneralCoveringInitializerPass.Covers C R W) :
    CoveringOptimum.Feasible C R (indicator W) := by
  have hn : ∀ v, 0 ≤ indicator W v := by intro v; unfold indicator; split_ifs <;> norm_num
  refine ⟨hn, ?_⟩
  intro r hr
  obtain ⟨v, hvW, hvC⟩ := hW r hr
  have hs := Finset.single_le_sum (fun u (_ : u ∈ C r) => hn u) hvC
  simpa only [indicator, if_pos hvW] using hs

theorem indicator_objective (c : V → ℝ) (W : Finset V) :
    CoveringOptimum.objective c (indicator W) = ∑ v ∈ W, c v := by
  calc
    _ = ∑ v ∈ W, c v * indicator W v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ W)
      intro v _ hv
      simp only [indicator, if_neg hv, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [indicator, if_pos hv, mul_one]

/-- No assumption is made about the unused input costs. Dummy one is an
explicit analysis extension, not an asserted invariance for negative costs. -/
noncomputable def extendCost (C : V → Finset V) (R : Finset V) (c : V → ℝ) (v : V) : ℝ :=
  if v ∈ CoveringSupport.admissible C R then c v else 1

theorem extendCost_eq (C : V → Finset V) (R : Finset V) (c : V → ℝ) {v : V}
    (hv : v ∈ CoveringSupport.admissible C R) : extendCost C R c v = c v := if_pos hv

theorem extendCost_nonneg (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v) : ∀ v, 0 ≤ extendCost C R c v := by
  intro v
  unfold extendCost
  split_ifs with hv
  · exact hc v hv
  · exact zero_le_one

theorem supported_objective_congr (C : V → Finset V) (R : Finset V) (c d : V → ℝ)
    (hcd : ∀ v ∈ CoveringSupport.admissible C R, c v = d v) (x : V → ℝ)
    (hx : ∀ v ∉ CoveringSupport.admissible C R, x v = 0) :
    CoveringOptimum.objective c x = CoveringOptimum.objective d x := by
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ CoveringSupport.admissible C R
  · rw [hcd v hv]
  · rw [hx v hv, mul_zero, mul_zero]

/-- Only genuinely nonnegative extensions are identified as unrestricted LPs.
Supported optima are constructed by the existing finite LP theorem. -/
theorem number_congr_on_admissible (C : V → Finset V) (R : Finset V) (c d : V → ℝ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v, 0 ≤ c v) (hd : ∀ v, 0 ≤ d v)
    (hcd : ∀ v ∈ CoveringSupport.admissible C R, c v = d v) :
    CoveringOptimum.number C R c = CoveringOptimum.number C R d := by
  obtain ⟨x, hx, _, hxs, hxc⟩ := CoveringSupport.exists_supported_optimum C R c hrows hc
  obtain ⟨y, hy, _, hys, hyd⟩ := CoveringSupport.exists_supported_optimum C R d hrows hd
  apply le_antisymm
  · calc
      _ ≤ CoveringOptimum.objective c y := number_le_objective C R c hc y hy
      _ = CoveringOptimum.objective d y := supported_objective_congr C R c d hcd y hys
      _ = _ := hyd
  · calc
      _ ≤ CoveringOptimum.objective d x := number_le_objective C R d hd x hx
      _ = CoveringOptimum.objective c x :=
        supported_objective_congr C R d c (fun v hv => (hcd v hv).symm) x hxs
      _ = _ := hxc

theorem extendCost_number_eq (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (hc : ∀ v, 0 ≤ c v) :
    CoveringOptimum.number C R (extendCost C R c) = CoveringOptimum.number C R c :=
  number_congr_on_admissible C R _ c hrows
    (extendCost_nonneg C R c (fun v _ => hc v)) hc (fun _ hv => extendCost_eq C R c hv)

/-- With only admissible input costs nonnegative, the extension value is the
attained optimum of the original objective on supported feasible vectors. -/
theorem extendCost_attains_admissible (C : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hrows : ∀ r ∈ R, (C r).Nonempty)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 0 ≤ c v) :
    ∃ x : V → ℝ, CoveringOptimum.Feasible C R x ∧
      (∀ v ∉ CoveringSupport.admissible C R, x v = 0) ∧
      CoveringOptimum.objective c x = CoveringOptimum.number C R (extendCost C R c) ∧
      ∀ y, CoveringOptimum.Feasible C R y →
        (∀ v ∉ CoveringSupport.admissible C R, y v = 0) →
        CoveringOptimum.objective c x ≤ CoveringOptimum.objective c y := by
  have hec := extendCost_nonneg C R c hc
  obtain ⟨x, hx, _, hxs, hnum⟩ := CoveringSupport.exists_supported_optimum C R (extendCost C R c) hrows hec
  have hcx : CoveringOptimum.objective c x = CoveringOptimum.objective (extendCost C R c) x :=
    supported_objective_congr C R c _ (fun _ hv => (extendCost_eq C R c hv).symm) x hxs
  refine ⟨x, hx, hxs, hcx.trans hnum, ?_⟩
  intro y hy hys
  calc
    _ = CoveringOptimum.number C R (extendCost C R c) := hcx.trans hnum
    _ ≤ CoveringOptimum.objective (extendCost C R c) y := number_le_objective C R _ hec y hy
    _ = _ := supported_objective_congr C R _ c (fun _ hv => extendCost_eq C R c hv) y hys

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance taskAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def restricted (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (x : V → ℝ) : V → ℝ :=
  CoveringSupport.project C (demands G C D R L Q I Bdy) x

theorem restricted_feasible (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (x : V → ℝ) (hx : CoveringOptimum.Feasible C R x) :
    CoveringOptimum.Feasible C (demands G C D R L Q I Bdy) (restricted G C D R L Q I Bdy x) :=
  CoveringSupport.project_feasible C _ x
    ⟨hx.1, fun r hr => hx.2 r (demands_subset G C D R L Q I Bdy hr)⟩

theorem restricted_outside (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (x : V → ℝ) (v : V) (hv : v ∉ service G C D R L Q I Bdy) :
    restricted G C D R L Q I Bdy x v = 0 := by
  exact if_neg hv

theorem restricted_mem (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (x : V → ℝ) (v : V) (hv : v ∈ service G C D R L Q I Bdy) :
    restricted G C D R L Q I Bdy x v = x v := by
  exact if_pos hv

theorem restricted_outside_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (x : V → ℝ) (v : V) (hv : v ∉ vertices G C D R L Q I) :
    restricted G C D R L Q I Bdy x v = 0 :=
  restricted_outside G C D R L Q I Bdy x v
    (fun hs => hv (service_in_vertices G C D R L Q I Bdy hlocal hs))

theorem restricted_cost_extension (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (c x : V → ℝ) :
    CoveringOptimum.objective (extendCost C R c) (restricted G C D R L Q I Bdy x) =
      CoveringOptimum.objective c (restricted G C D R L Q I Bdy x) := by
  apply supported_objective_congr C R _ c (fun _ hv => extendCost_eq C R c hv)
  intro v hv
  exact restricted_outside G C D R L Q I Bdy x v
    (fun hs => hv (service_light G C D R L Q I Bdy hs).1)

theorem restricted_objective (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (c x : V → ℝ) :
    CoveringOptimum.objective c (restricted G C D R L Q I Bdy x) =
      ∑ v ∈ service G C D R L Q I Bdy, c v * x v := by
  calc
    _ = ∑ v ∈ service G C D R L Q I Bdy, c v * restricted G C D R L Q I Bdy x v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      rw [restricted_outside G C D R L Q I Bdy x v hv, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [restricted_mem G C D R L Q I Bdy x v hv]

theorem empty_task (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hempty : demands G C D R L Q I Bdy = ∅)
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    restricted G C D R L Q I Bdy x = (fun _ => 0) ∧
      CoveringOptimum.objective c (restricted G C D R L Q I Bdy x) = 0 ∧
      CoveringOptimum.number C (demands G C D R L Q I Bdy) c = 0 := by
  have hz : restricted G C D R L Q I Bdy x = (fun _ => 0) := by
    funext v
    simp [restricted, CoveringSupport.project, CoveringSupport.admissible, hempty]
  refine ⟨hz, ?_, ?_⟩
  · simpa only [hz] using (show CoveringOptimum.objective c (fun _ => 0) = 0 by simp [CoveringOptimum.objective])
  · simpa only [hempty] using number_empty C c hc

/-- The full-V LP has an optimum supported in the actual physical task.
This also applies to an empty task, whose value is explicitly zero above. -/
theorem exists_local_optimum (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (C r).Nonempty) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    ∃ y : V → ℝ, CoveringOptimum.Feasible C (demands G C D R L Q I Bdy) y ∧
      (∀ v ∉ service G C D R L Q I Bdy, y v = 0) ∧
      (∀ v ∉ vertices G C D R L Q I, y v = 0) ∧
      CoveringOptimum.objective c y = CoveringOptimum.number C (demands G C D R L Q I Bdy) c := by
  obtain ⟨y, hy, _, hys, hnum⟩ := CoveringSupport.exists_supported_optimum C
    (demands G C D R L Q I Bdy) c
    (fun r hr => hrows r (demands_subset G C D R L Q I Bdy hr)) hc
  refine ⟨y, hy, hys, ?_, hnum⟩
  intro v hv
  exact hys v (fun hs => hv (service_in_vertices G C D R L Q I Bdy hlocal hs))

/-- The TaskCostSum restriction argument, instantiated with true C-service.
No disjointness of the physical regions is required. -/
theorem sum_restricted (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k)
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : ∀ v, 0 ≤ x v) :
    let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
    (∑ I ∈ P.parts, CoveringOptimum.objective c (restricted G C D R L Q I Bdy x)) ≤
      CoveringOptimum.objective c x := by
  dsimp only
  let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
  let S := fun I => service G C D R L Q I Bdy
  have hd : (P.parts : Set (Finset (Low D Q))).PairwiseDisjoint S :=
    fun I hI J hJ hne => service_disjoint G C D R L Q hlocal k P I J hI hJ hne
  calc
    _ = ∑ I ∈ P.parts, ∑ v ∈ S I, c v * x v :=
      Finset.sum_congr rfl (fun I _ => restricted_objective G C D R L Q I Bdy c x)
    _ = ∑ v ∈ P.parts.biUnion S, c v * x v := (Finset.sum_biUnion hd).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => mul_nonneg (hc v) (hx v))

theorem vector_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k)
    (c x : V → ℝ) (hc : ∀ v, 0 ≤ c v) (hx : CoveringOptimum.Feasible C R x) :
    let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
    (∑ I ∈ P.parts, CoveringOptimum.number C (demands G C D R L Q I Bdy) c) ≤
      CoveringOptimum.objective c x := by
  dsimp only
  let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
  calc
    _ ≤ ∑ I ∈ P.parts, CoveringOptimum.objective c (restricted G C D R L Q I Bdy x) :=
      Finset.sum_le_sum (fun I _ => number_le_objective C _ c hc _
        (restricted_feasible G C D R L Q I Bdy x hx))
    _ ≤ _ := sum_restricted G C D R L Q hlocal k P c x hc hx.1

theorem optimum_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty) (k : ℕ)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
    (∑ I ∈ P.parts, CoveringOptimum.number C (demands G C D R L Q I Bdy) c) ≤
      CoveringOptimum.number C R c := by
  obtain ⟨x, hx, hnum⟩ := CoveringOptimum.exists_optimum_eq_number C R c hrows hc
  have hb := vector_bound G C D R L Q hlocal k P c x hc hx
  rwa [hnum] at hb

theorem local_number_bound (C : V → Finset V) (D R : Finset V) (L B k : ℕ) (Q : Finset D)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) (hD : D ⊆ CoveringSupport.admissible C R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (c : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B) :
    CoveringOptimum.number C (demands G C D R L Q I Bdy) c ≤ 2 * (B : ℝ) * k := by
  obtain ⟨W, _, _, hW, hcost⟩ := part_benchmark G C D R L B k Q P I Bdy hI hcover hD hlocal c hcB
  have hb := number_le_objective C (demands G C D R L Q I Bdy) c hc (indicator W)
    (indicator_feasible C _ W hW)
  rw [indicator_objective] at hb
  exact hb.trans hcost

/-- Actual initializer D0, with a stated nonnegative cost extension interface.
The global optimum vector is obtained internally, never assumed as input. -/
theorem initialized_spec (C : V → Finset V) (b h f T L B : ℕ) (hb : 1 ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v)
    (hcB : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    ∀ (Q : Finset D) (k : ℕ) (P : SmallParts.Data (graph G C D R L Q) Finset.univ k),
      let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
      (∑ I ∈ P.parts, CoveringOptimum.number C (demands G C D R L Q I Bdy) c) ≤
        CoveringOptimum.number C R c ∧
      ∀ I ∈ P.parts, CoveringOptimum.number C (demands G C D R L Q I Bdy) c ≤ 2 * (B : ℝ) * k := by
  dsimp only
  intro Q k P
  refine ⟨optimum_bound G C _ R L Q hlocal hrows k P c hc, ?_⟩
  intro I hI
  exact local_number_bound G C _ R L B k Q P I _ hI
    (GeneralCoveringInitializerRun.selected_covers C b h f R T hrows)
    (GeneralCoveringInitializerRun.selected_admissible C b h f hb R T) hlocal c hc hcB

/-- Original admissible-only positive bounded input costs. The extension is
constructed here, with its supported-objective/optimum meaning proved above.
No sign condition is silently imposed on the unused original coordinates. -/
theorem initialized_admissible_spec (C : V → Finset V) (b h f T L B : ℕ) (hb : 1 ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (c : V → ℝ) (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    let c' := extendCost C R c
    ∀ (Q : Finset D) (k : ℕ) (P : SmallParts.Data (graph G C D R L Q) Finset.univ k),
      let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
      (∑ I ∈ P.parts, CoveringOptimum.number C (demands G C D R L Q I Bdy) c') ≤
        CoveringOptimum.number C R c' ∧
      ∀ I ∈ P.parts, CoveringOptimum.number C (demands G C D R L Q I Bdy) c' ≤ 2 * (B : ℝ) * k := by
  have hn := extendCost_nonneg C R c (fun v hv => zero_le_one.trans (hc v hv).1)
  have hbounds : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ extendCost C R c v ∧ extendCost C R c v ≤ B := by
    intro v hv
    simpa only [extendCost_eq C R c hv] using hc v hv
  exact initialized_spec G C b h f T L B hb R hlocal hrows (extendCost C R c) hn hbounds

end Paper.GeneralCoveringTaskFractional

#print axioms Paper.GeneralCoveringTaskFractional.number_le_objective
#print axioms Paper.GeneralCoveringTaskFractional.number_empty
#print axioms Paper.GeneralCoveringTaskFractional.indicator_feasible
#print axioms Paper.GeneralCoveringTaskFractional.indicator_objective
#print axioms Paper.GeneralCoveringTaskFractional.extendCost_nonneg
#print axioms Paper.GeneralCoveringTaskFractional.supported_objective_congr
#print axioms Paper.GeneralCoveringTaskFractional.number_congr_on_admissible
#print axioms Paper.GeneralCoveringTaskFractional.extendCost_number_eq
#print axioms Paper.GeneralCoveringTaskFractional.extendCost_attains_admissible
#print axioms Paper.GeneralCoveringTaskFractional.restricted_feasible
#print axioms Paper.GeneralCoveringTaskFractional.restricted_outside
#print axioms Paper.GeneralCoveringTaskFractional.restricted_outside_vertices
#print axioms Paper.GeneralCoveringTaskFractional.restricted_cost_extension
#print axioms Paper.GeneralCoveringTaskFractional.restricted_objective
#print axioms Paper.GeneralCoveringTaskFractional.empty_task
#print axioms Paper.GeneralCoveringTaskFractional.exists_local_optimum
#print axioms Paper.GeneralCoveringTaskFractional.sum_restricted
#print axioms Paper.GeneralCoveringTaskFractional.vector_bound
#print axioms Paper.GeneralCoveringTaskFractional.optimum_bound
#print axioms Paper.GeneralCoveringTaskFractional.local_number_bound
#print axioms Paper.GeneralCoveringTaskFractional.initialized_spec
#print axioms Paper.GeneralCoveringTaskFractional.initialized_admissible_spec
