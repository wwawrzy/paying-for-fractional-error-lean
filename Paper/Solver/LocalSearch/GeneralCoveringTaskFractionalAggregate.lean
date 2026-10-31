import Paper.Solver.LocalSearch.GeneralCoveringTaskFractionalParallel

/-! Local, duplicate-safe sum of actual keyed fractional numerators. No new
broadcasts or global part enumeration enter the executable. The public bound
max(1,L)*M follows from the real role prefix. Analysis enumerates actual parts,
proves exact equality with their own outputs and uses true C-service LP
restrictions. Only the union of task demands is covered before repair. -/
namespace Paper.GeneralCoveringTaskFractionalAggregate
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringTaskFractionalParallel.Input V B

/-- Finite unique keys and actual first-match values; total even on malformed lists. -/
def aggregate {M : ℕ} (s : GeneralCoveringTaskFractionalParallel.Output V M) : ℕ :=
  ∑ r ∈ TaggedDictionary.keys s.1, ((TaggedDictionary.lookup s.1 r).map Fin.val).getD 0

def finish (M : ℕ) : Program V (GeneralCoveringTaskFractionalParallel.Output V M) ℕ :=
  .local (fun _ _ s => aggregate s)

def program {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) : Program V (Input V B) ℕ :=
  .seq (GeneralCoveringTaskFractionalParallel.program ids L a B k q hB)
    (finish (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q))

def fromOwners {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    Program V (GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) ℕ :=
  .seq (GeneralCoveringTaskFractionalParallel.fromOwners ids L a B k q hB)
    (finish (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q))

theorem lookup_none {A : Type} (xs : List (V × A)) (r : V) (hr : r ∉ TaggedDictionary.keys xs) :
    TaggedDictionary.lookup xs r = none := by
  simp only [TaggedDictionary.lookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro p hp he
  exact hr ((TaggedDictionary.mem_keys xs r).mpr ⟨p, hp, he⟩)

/-- Adding duplicate entries cannot change the sum when keys/first values agree. -/
theorem aggregate_congr {M : ℕ} (s t : GeneralCoveringTaskFractionalParallel.Output V M)
    (hk : TaggedDictionary.keys s.1 = TaggedDictionary.keys t.1)
    (hv : ∀ r ∈ TaggedDictionary.keys s.1, TaggedDictionary.lookup s.1 r = TaggedDictionary.lookup t.1 r) :
    aggregate s = aggregate t := by
  unfold aggregate
  apply Finset.sum_congr hk
  intro r hr
  rw [hv r (hk.symm ▸ hr)]

theorem aggregate_zero {M : ℕ} (s : GeneralCoveringTaskFractionalParallel.Output V M)
    (hz : ∀ r ∈ TaggedDictionary.keys s.1, TaggedDictionary.lookup s.1 r = some 0) : aggregate s = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  simp only [hz r hr, Option.map_some, Option.getD_some, Fin.val_zero]

theorem aggregate_le {M : ℕ} (s : GeneralCoveringTaskFractionalParallel.Output V M) :
    aggregate s ≤ (TaggedDictionary.keys s.1).card * M := by
  calc
    _ ≤ ∑ _r ∈ TaggedDictionary.keys s.1, M :=
      Finset.sum_le_sum (fun r _ => GeneralCoveringTaskFractionalParallel.numerator_le (fun _ => s) r r)
    _ = _ := by simp

theorem keys_card_le_length {A : Type} (xs : List (V × A)) : (TaggedDictionary.keys xs).card ≤ xs.length := by
  simpa only [TaggedDictionary.keys, List.length_map] using (List.toFinset_card_le (xs.map Prod.fst))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    (program ids L a B k q hB).runEncoded G s v =
      aggregate ((GeneralCoveringTaskFractionalParallel.program ids L a B k q hB).runEncoded G s v) := rfl

theorem fromOwners_run {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) (v : V) :
    (fromOwners ids L a B k q hB).runEncoded G s v =
      aggregate ((GeneralCoveringTaskFractionalParallel.fromOwners ids L a B k q hB).runEncoded G s v) := rfl

/-- Public numeric bound for EVERY actual run, including malformed metadata. -/
theorem output_bound {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    (program ids L a B k q hB).runEncoded G s v ≤
      max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q := by
  have hk : (TaggedDictionary.keys
      ((GeneralCoveringTaskFractionalParallel.program ids L a B k q hB).runEncoded G s v).1).card ≤ max 1 L := by
    rw [GeneralCoveringTaskFractionalParallel.keys]
    exact (keys_card_le_length _).trans (GeneralCoveringTaskRoles.length_output G ids L s v)
  rw [run_program]
  exact (aggregate_le _).trans (Nat.mul_le_mul_right _ hk)

noncomputable def partNumerator {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a q : ℕ) (hB : 1 ≤ B)
    (I : Finset (Low g.D g.Q)) (v : V) : ℕ :=
  if hI : I ∈ g.P.parts then
    GeneralCoveringTaskFractionalParallel.numerator
      ((GeneralCoveringTaskFractionalParallel.program ids L a B g.k q hB).runEncoded G s)
      (GeneralCoveringTaskRoles.roleID G g I hI) v else 0

theorem partNumerator_eq {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a q : ℕ) (hB : 1 ≤ B)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) (v : V) :
    partNumerator G ids g a q hB I v = GeneralCoveringTaskFractionalParallel.numerator
      ((GeneralCoveringTaskFractionalParallel.program ids L a B g.k q hB).runEncoded G s)
      (GeneralCoveringTaskRoles.roleID G g I hI) v := dif_pos hI

/-- Every valid role name represents exactly one genuine part. -/
theorem name_injective {L B : ℕ} {s : V → Input V B} (g : GeneralCoveringTaskRoles.Geometry G L B s) :
    Function.Injective (fun I : g.P.parts => GeneralCoveringTaskRoles.roleID G g I.val I.property) := by
  intro I J he
  apply Subtype.ext
  exact GeneralCoveringTaskRoles.name_injective g.D g.Q g.P.parts g.P.disjoint I.val J.val I.property J.property
    (g.P.nonempty I.val I.property) (g.P.nonempty J.val J.property) he

/-- Literal local sum equals the sum of all actual per-part own numerators. -/
theorem output_sum {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a q : ℕ) (hB : 1 ≤ B) (v : V) :
    (program ids L a B g.k q hB).runEncoded G s v = ∑ I ∈ g.P.parts, partNumerator G ids g a q hB I v := by
  let out := (GeneralCoveringTaskFractionalParallel.program ids L a B g.k q hB).runEncoded G s
  let names := g.P.parts.attach.image (fun I => GeneralCoveringTaskRoles.roleID G g I.val I.property)
  have hsub : TaggedDictionary.keys (out v).1 ⊆ names := by
    intro r hr
    obtain ⟨I, hI, he⟩ := GeneralCoveringTaskFractionalParallel.keys_valid G ids g a q hB v r hr
    exact Finset.mem_image.mpr ⟨⟨I, hI⟩, Finset.mem_attach _ _, he⟩
  calc
    _ = ∑ r ∈ TaggedDictionary.keys (out v).1, GeneralCoveringTaskFractionalParallel.numerator out r v := rfl
    _ = ∑ r ∈ names, GeneralCoveringTaskFractionalParallel.numerator out r v := by
      apply Finset.sum_subset hsub
      intro r _ hr
      simp only [GeneralCoveringTaskFractionalParallel.numerator, lookup_none _ _ hr,
        Option.map_none, Option.getD_none]
    _ = ∑ I ∈ g.P.parts.attach,
        GeneralCoveringTaskFractionalParallel.numerator out (GeneralCoveringTaskRoles.roleID G g I.val I.property) v :=
      Finset.sum_image (fun I _ J _ he => name_injective G g he)
    _ = ∑ I ∈ g.P.parts.attach, partNumerator G ids g a q hB I.val v := by
      apply Finset.sum_congr rfl
      intro I _
      exact (partNumerator_eq G ids g a q hB I.val I.property v).symm
    _ = _ := Finset.sum_attach g.P.parts (fun I => partNumerator G ids g a q hB I v)

noncomputable def taskDemands {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) : Finset V :=
  g.P.parts.biUnion (fun I => demands G g.cover g.D g.R L g.Q I g.Bdy)

noncomputable def taskService {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) : Finset V :=
  g.P.parts.biUnion (fun I => service G g.cover g.D g.R L g.Q I g.Bdy)

theorem taskService_eq_admissible {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) :
    taskService G g = CoveringSupport.admissible g.cover (taskDemands G g) := by
  ext v
  simp only [taskService, taskDemands, service, CoveringSupport.admissible, Finset.mem_biUnion]
  constructor
  · rintro ⟨I, hI, r, hr, hv⟩
    exact ⟨r, ⟨I, hI, hr⟩, hv⟩
  · rintro ⟨r, ⟨I, hI, hr⟩, hv⟩
    exact ⟨I, hI, r, hr, hv⟩

noncomputable def taskLP {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (c : V → ℝ) : ℝ :=
  ∑ I ∈ g.P.parts, GeneralCoveringNormalizedFractional.supportedNumber g.cover
    (demands G g.cover g.D g.R L g.Q I g.Bdy) c

theorem solution_sum {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a q : ℕ) (hB : 1 ≤ B) (v : V) :
    (((program ids L a B g.k q hB).runEncoded G s v : ℕ) : ℝ) / q =
      ∑ I ∈ g.P.parts, (partNumerator G ids g a q hB I v : ℝ) / q := by
  rw [output_sum G ids g a q hB v, Nat.cast_sum, Finset.sum_div]

/-- Each summand retains the accepted exact original-C per-part semantics. -/
theorem solved {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) :
    GeneralCoveringTaskFractionalParallel.Spec g.cover (vertices G g.cover g.D g.R L g.Q I)
      (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun v => (s v).2.cost) q ξ
      (partNumerator G ids g a q hB I) := by
  have he : partNumerator G ids g a q hB I = GeneralCoveringTaskFractionalParallel.numerator
      ((GeneralCoveringTaskFractionalParallel.program ids L a B g.k q hB).runEncoded G s)
      (GeneralCoveringTaskRoles.roleID G g I hI) :=
    funext (fun v => partNumerator_eq G ids g a q hB I hI v)
  rw [he]
  exact (GeneralCoveringTaskFractionalParallel.part_spec G ids g I hI hcover hD a ha hden q hB hq ξ haccuracy hc).2

theorem support_cover {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val) :
    (∀ v, v ∉ taskService G g → (program ids L a B g.k q hB).runEncoded G s v = 0) ∧
    (∀ v, v ∉ CoveringSupport.admissible g.cover g.R → (program ids L a B g.k q hB).runEncoded G s v = 0) ∧
    CoveringOptimum.Feasible g.cover (taskDemands G g)
      (fun v => (((program ids L a B g.k q hB).runEncoded G s v : ℕ) : ℝ) / q) := by
  have hs : ∀ v, v ∉ taskService G g → (program ids L a B g.k q hB).runEncoded G s v = 0 := by
    intro v hv
    rw [output_sum G ids g a q hB v]
    apply Finset.sum_eq_zero
    intro I hI
    exact (solved G ids g hcover hD a ha hden q hB hq ξ haccuracy hc I hI).2.2.2.1 v
      (fun hsvc => hv (Finset.mem_biUnion.mpr ⟨I, hI, hsvc⟩))
  refine ⟨hs, ?_, ⟨fun v => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg q), ?_⟩⟩
  · intro v hv
    apply hs v
    intro hsvc
    obtain ⟨I, _, hi⟩ := Finset.mem_biUnion.mp hsvc
    exact hv (service_light G g.cover g.D g.R L g.Q I g.Bdy hi).1
  · intro r hr
    obtain ⟨I, hI, hr⟩ := Finset.mem_biUnion.mp hr
    have hp (v : V) : (partNumerator G ids g a q hB I v : ℝ) / q ≤
        (((program ids L a B g.k q hB).runEncoded G s v : ℕ) : ℝ) / q := by
      rw [solution_sum G ids g a q hB v]
      exact Finset.single_le_sum (s := g.P.parts)
        (f := fun J => (partNumerator G ids g a q hB J v : ℝ) / q)
        (fun J _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg q)) hI
    exact ((solved G ids g hcover hD a ha hden q hB hq ξ haccuracy hc I hI).1.2 r hr).trans
      (Finset.sum_le_sum (fun v _ => hp v))

/-- Exact linear objective identity; physical regions need not be disjoint. -/
theorem objective_sum {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a q : ℕ) (hB : 1 ≤ B) (c : V → ℝ) :
    CoveringOptimum.objective c
      (fun v => (((program ids L a B g.k q hB).runEncoded G s v : ℕ) : ℝ) / q) =
      ∑ I ∈ g.P.parts, CoveringOptimum.objective c (fun v => (partNumerator G ids g a q hB I v : ℝ) / q) := by
  unfold CoveringOptimum.objective
  simp_rw [solution_sum G ids g a q hB, Finset.mul_sum]
  exact Finset.sum_comm

/-- Accepted true-service restriction/disjointness proves the task LP sum.
The boundary is that of this same partition; no target sum is a premise. -/
theorem sum_task_lp {L B : ℕ} {s : V → Input V B} (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts)
    (c : V → ℝ) (hc : ∀ v, 0 ≤ c v) :
    taskLP G g c ≤ GeneralCoveringNormalizedFractional.supportedNumber g.cover g.R c := by
  have hrows := GeneralCoveringTaskFractionalSolve.rows_nonempty g.cover g.D g.R hcover
  have hb := GeneralCoveringTaskFractional.optimum_bound G g.cover g.D g.R L g.Q g.local_rows hrows
    g.k g.P c hc
  dsimp only at hb
  rw [← hboundary] at hb
  calc
    _ = ∑ I ∈ g.P.parts, CoveringOptimum.number g.cover (demands G g.cover g.D g.R L g.Q I g.Bdy) c := by
      apply Finset.sum_congr rfl
      intro I _
      exact GeneralCoveringNormalizedFractional.supportedNumber_eq_number g.cover _ c
        (fun r hr => hrows r (demands_subset G g.cover g.D g.R L g.Q I g.Bdy hr)) hc
    _ ≤ CoveringOptimum.number g.cover g.R c := hb
    _ = _ := (GeneralCoveringNormalizedFractional.supportedNumber_eq_number g.cover g.R c hrows hc).symm

/-- Concrete aggregate contract: support, union-of-task coverage and the two
relative-cost inequalities. This does not assert original-R coverage. -/
def Spec {B : ℕ} (cover : V → Finset V) (R T S : Finset V) (c : V → Fin (B + 1))
    (q : ℕ) (ξ lp : ℝ) (p : V → ℕ) : Prop :=
  (∀ v, v ∉ S → p v = 0) ∧
  (∀ v, v ∉ CoveringSupport.admissible cover R → p v = 0) ∧
  CoveringOptimum.Feasible cover T (fun v => (p v : ℝ) / q) ∧
  CoveringOptimum.objective (fun v => ((c v).val : ℝ)) (fun v => (p v : ℝ) / q) ≤ (1 + ξ) * lp ∧
  (1 + ξ) * lp ≤ (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber cover R (fun v => ((c v).val : ℝ)) ∧
  (∀ v, (q : ℝ) * ((p v : ℝ) / q) = p v)

theorem aggregate_spec {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts) :
    Spec g.cover g.R (taskDemands G g) (taskService G g) (fun v => (s v).2.cost) q ξ
      (taskLP G g (fun v => ((s v).2.cost.val : ℝ))) ((program ids L a B g.k q hB).runEncoded G s) := by
  have hs := support_cover G ids g hcover hD a ha hden q hB hq ξ haccuracy hc
  have hnonneg : (0 : ℝ) ≤ 2 * (a : ℝ) / q := div_nonneg (by positivity) (Nat.cast_nonneg q)
  have hfactor : 0 ≤ 1 + ξ := by have hxi := hnonneg.trans haccuracy; linarith
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_, ?_, ?_⟩
  · rw [objective_sum G ids g a q hB]
    calc
      _ ≤ ∑ I ∈ g.P.parts, (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber g.cover
          (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun v => ((s v).2.cost.val : ℝ)) :=
        Finset.sum_le_sum (fun I hI => (solved G ids g hcover hD a ha hden q hB hq ξ haccuracy hc I hI).2.1)
      _ = _ := (Finset.mul_sum _ _ _).symm
  · exact mul_le_mul_of_nonneg_left (sum_task_lp G g hcover hboundary _ (fun v => Nat.cast_nonneg _)) hfactor
  · intro v
    have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    field_simp [hqn]

/-- Empty parts give zero actual local numerators, with no Context constructed. -/
theorem empty_parts {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (he : g.P.parts = ∅) (a q : ℕ) (hB : 1 ≤ B) :
    ∀ v, (program ids L a B g.k q hB).runEncoded G s v = 0 := by
  intro v
  rw [output_sum G ids g a q hB v, he, Finset.sum_empty]

theorem fromOwners_correct {bits B : ℕ} (ids : BitCode V bits) (L a k q : ℕ) (hB : 1 ≤ B)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    (fromOwners ids L a B k q hB).runEncoded G (fun v => (s v, fields v)) =
      (program ids L a B k q hB).runEncoded G (fun v =>
        (GeneralCoveringOwnerSupport.expected G cover D R L
          (fun u => ⟨s u, GeneralCoveringOwners.owner cover D R u⟩) v, fields v)) := by
  exact congrArg (fun out : V → GeneralCoveringTaskFractionalParallel.Output V
      (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) => fun v => aggregate (out v))
    (GeneralCoveringTaskFractionalParallel.fromOwners_correct G ids L a k q hB
      cover targets D R hinc hlocal s fields hD hR hC ht)

/-- Total public numeric bound also from original private Owners inputs. -/
theorem fromOwners_bound {bits B : ℕ} (ids : BitCode V bits) (L a k q : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) (v : V) :
    (fromOwners ids L a B k q hB).runEncoded G s v ≤
      max 1 L * GeneralCoveringTaskFractionalSolve.numeratorBound a B k q := by
  have he := congrFun (GeneralCoveringTaskFractionalParallel.fromOwners_run G ids L a B k q hB
    (fun u => (s u).1) (fun u => (s u).2)) v
  rw [fromOwners_run]
  change aggregate ((GeneralCoveringTaskFractionalParallel.fromOwners ids L a B k q hB).runEncoded G
    (fun u => ((s u).1, (s u).2)) v) ≤ _
  rw [he]
  exact output_bound G ids L a B k q hB
    (fun u => ((GeneralCoveringOwnerSupport.program ids L).runEncoded G (fun w => (s w).1) u, (s u).2)) v

/-- Native original-input producer, simultaneous masked fractional solve and
local sum. Full local part/interior fields remain explicit intermediate data. -/
theorem fromOwners_spec {bits B : ℕ} (ids : BitCode V bits) (L a k q : ℕ) (hB : 1 ≤ B)
    (cover targets : V → Finset V) (D R : Finset V) (Q : Finset D)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k) (Bdy : Finset (Low D Q))
    (hboundary : Bdy = BoundaryOwners.vertices (graph G cover D R L Q) Finset.univ P.parts)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D) (hadm : D ⊆ CoveringSupport.admissible cover R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hq : 1 ≤ q)
    (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (fields v).cost.val)
    (hrole : ∀ (J : Finset (Low D Q)) (hJ : J ∈ P.parts) (i : Low D Q), i ∈ J →
      (fields i.val.val).role = some (GeneralCoveringTaskRoles.name D Q J (P.nonempty J hJ)))
    (hexcluded : ∀ d : D, d ∈ Q → (fields d.val).role = none)
    (hinterior : ∀ i : Low D Q, (fields i.val.val).interior = decide (i ∉ Bdy)) :
    Spec cover R (P.parts.biUnion (fun I => demands G cover D R L Q I Bdy))
      (P.parts.biUnion (fun I => service G cover D R L Q I Bdy)) (fun v => (fields v).cost) q ξ
      (∑ I ∈ P.parts, GeneralCoveringNormalizedFractional.supportedNumber cover
        (demands G cover D R L Q I Bdy) (fun v => ((fields v).cost.val : ℝ)))
      ((fromOwners ids L a B k q hB).runEncoded G (fun v => (s v, fields v))) := by
  rw [fromOwners_correct G ids L a k q hB cover targets D R hinc hlocal s fields hD hR hC ht]
  let t : V → Input V B := fun v =>
    (GeneralCoveringOwnerSupport.expected G cover D R L
      (fun u => ⟨s u, GeneralCoveringOwners.owner cover D R u⟩) v, fields v)
  let g : GeneralCoveringTaskRoles.Geometry G L B t :=
    { cover := cover
      targets := targets
      D := D
      R := R
      Q := Q
      k := k
      P := P
      Bdy := Bdy
      local_rows := hlocal
      owner := fun _ => rfl
      admissible := fun _ => rfl
      heavy := fun _ => rfl
      residual := fun _ => rfl
      candidates := hC
      inverse := ht
      incidence := hinc
      low_role := hrole
      excluded_role := hexcluded
      interior := hinterior }
  exact aggregate_spec G ids g hcover hadm a ha hden q hB hq ξ haccuracy hc hboundary

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids L a B k q hB).rounds = RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 4 := by
  simp only [program, finish, Program.rounds, Nat.add_zero, GeneralCoveringTaskFractionalParallel.rounds]

theorem fromOwners_rounds {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    (fromOwners ids L a B k q hB).rounds = RecursiveSearch.roundBound (4 * k) a (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 8 := by
  simp only [fromOwners, finish, Program.rounds, Nat.add_zero, GeneralCoveringTaskFractionalParallel.fromOwners_rounds]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids L a B k q hB).maxBits = (GeneralCoveringTaskFractionalParallel.program ids L a B k q hB).maxBits := by
  change max _ 0 = _
  exact Nat.max_zero _

theorem fromOwners_maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B) :
    (fromOwners ids L a B k q hB).maxBits = (GeneralCoveringTaskFractionalParallel.fromOwners ids L a B k q hB).maxBits := by
  change max _ 0 = _
  exact Nat.max_zero _

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L a B k q : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    let K := max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B q (GeneralCoveringTaskFractionalSolve.numeratorBound a B k q) + 1) + 1))
    (program ids L a B k q hB).maxBits ≤ K * Nat.clog 2 (n + 2) ∧
      (fromOwners ids L a B k q hB).maxBits ≤ K * Nat.clog 2 (n + 2) := by
  dsimp only
  rw [maxBits_eq, fromOwners_maxBits_eq]
  exact GeneralCoveringTaskFractionalParallel.logarithmic_bits ids L a B k q hB n c hids

end Paper.GeneralCoveringTaskFractionalAggregate

#print axioms Paper.GeneralCoveringTaskFractionalAggregate.lookup_none
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.aggregate_congr
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.aggregate_zero
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.aggregate_le
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.keys_card_le_length
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.run_program
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.fromOwners_run
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.output_bound
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.partNumerator_eq
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.name_injective
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.output_sum
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.taskService_eq_admissible
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.solution_sum
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.solved
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.support_cover
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.objective_sum
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.sum_task_lp
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.aggregate_spec
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.empty_parts
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.fromOwners_correct
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.fromOwners_bound
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.fromOwners_spec
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.rounds
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.fromOwners_rounds
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.maxBits_eq
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.fromOwners_maxBits_eq
#print axioms Paper.GeneralCoveringTaskFractionalAggregate.logarithmic_bits
