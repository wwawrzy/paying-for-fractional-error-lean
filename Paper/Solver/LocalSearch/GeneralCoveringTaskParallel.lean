import Paper.Solver.LocalSearch.GeneralCoveringTaskRoles
import Paper.Solver.LocalSearch.GeneralCoveringTaskIntegral
import Paper.Preliminaries.SparseParallelCorrect

/-! Shared role acquisition on the physical graph, followed by the actual
sparse compiler with TaskIntegral as its only masked client. Owner geometry,
demands and the genuine benchmark are always those of the original graph.
Local center part names/interior marks remain an intermediate input; their
production and aggregation of the parallel answers are separate gates. -/
namespace Paper.GeneralCoveringTaskParallel
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringTaskRoles.Input V B
abbrev Output (V : Type) := List (V × Bool) × SparseRolePrepare.Env V V

def program {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Output V) :=
  .seq (GeneralCoveringTaskRoles.program ids L B)
    (SparseParallel.execute ids (max 1 L) (GeneralCoveringTaskIntegral.program ids a B k hB))

def fromOwners {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    Program V (GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) (Output V) :=
  .seq (GeneralCoveringTaskRoles.fromOwners ids L B)
    (SparseParallel.execute ids (max 1 L) (GeneralCoveringTaskIntegral.program ids a B k hB))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def chosen (out : V → Output V) (r : V) : Finset V :=
  Finset.univ.filter (fun v => TaggedDictionary.lookup (out v).1 r = some true)

theorem mem_chosen (out : V → Output V) (r v : V) :
    v ∈ chosen out r ↔ TaggedDictionary.lookup (out v).1 r = some true := by
  simp only [chosen, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Original-C support, service, cover and optimum, including its genuine budget. -/
def Spec (cover : V → Finset V) (H T : Finset V) (c : V → ℕ) (M : ℕ) (O : Finset V) : Prop :=
  O ⊆ H ∧ O ⊆ CoveringSupport.admissible cover T ∧
    GeneralCoveringNormalizedIntegral.Covers cover T O ∧ (∑ v ∈ O, c v) ≤ M ∧
    ∀ W : Finset V, W ⊆ CoveringSupport.admissible cover T →
      GeneralCoveringNormalizedIntegral.Covers cover T W → (∑ v ∈ O, c v) ≤ ∑ v ∈ W, c v

/-- Proof-side description of the full per-role state, also outside its region. -/
def taskInput {B : ℕ} (cover targets : V → Finset V) (H T : Finset V)
    (c : V → Fin (B + 1)) (v : V) : GeneralCoveringFractional.Input V B :=
  ⟨decide (v ∈ H), c v, decide (v ∈ T), cover v, targets v⟩

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program ids L a B k hB).runEncoded G s =
      (SparseParallel.execute ids (max 1 L) (GeneralCoveringTaskIntegral.program ids a B k hB)).runEncoded G
        ((GeneralCoveringTaskRoles.program ids L B).runEncoded G s) := rfl

/-- No client, including a malformed one, can invent dictionary keys. -/
theorem keys {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    TaggedDictionary.keys ((program ids L a B k hB).runEncoded G s v).1 =
      TaggedDictionary.keys ((GeneralCoveringTaskRoles.program ids L B).runEncoded G s v) := by
  rw [run_program, Program.runEncoded_eq_run]
  exact SparseParallelCorrect.execute_keys G ids (max 1 L)
    (GeneralCoveringTaskIntegral.program ids a B k hB) _ v

theorem lookup_absent {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v r : V)
    (hr : r ∉ TaggedDictionary.keys ((GeneralCoveringTaskRoles.program ids L B).runEncoded G s v)) :
    TaggedDictionary.lookup ((program ids L a B k hB).runEncoded G s v).1 r = none := by
  have hn : r ∉ TaggedDictionary.keys ((program ids L a B k hB).runEncoded G s v).1 := by
    rw [keys]
    exact hr
  simp only [TaggedDictionary.lookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
  intro p hp he
  exact hn ((TaggedDictionary.mem_keys _ r).mpr ⟨p, hp, he⟩)

theorem role_region {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) :
    SparseRolePrepare.vertices
      (fun v => TaggedDictionary.keys ((GeneralCoveringTaskRoles.program ids L B).runEncoded G s v))
      (GeneralCoveringTaskRoles.roleID G g I hI) = vertices G g.cover g.D g.R L g.Q I := by
  ext v
  rw [SparseRolePrepare.mem_vertices]
  exact GeneralCoveringTaskRoles.keys_part G ids g I hI v

theorem full_input {L B : ℕ} {s : V → Input V B} (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) :
    (fun v => GeneralCoveringTaskRoles.payload (GeneralCoveringTaskRoles.routed g.cover g.D g.R s v)
      (GeneralCoveringTaskRoles.keysAt G g.cover g.D g.R s v) (GeneralCoveringTaskRoles.roleID G g I hI)) =
      taskInput g.cover g.targets (vertices G g.cover g.D g.R L g.Q I)
        (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun v => (s v).2.cost) := by
  funext v
  exact GeneralCoveringTaskRoles.payload_part G g I hI v

theorem keys_part {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts)
    (a : ℕ) (hB : 1 ≤ B) (v : V) :
    GeneralCoveringTaskRoles.roleID G g I hI ∈
      TaggedDictionary.keys ((program ids L a B g.k hB).runEncoded G s v).1 ↔
        v ∈ vertices G g.cover g.D g.R L g.Q I := by
  rw [keys]
  exact GeneralCoveringTaskRoles.keys_part G ids g I hI v

theorem keys_valid {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a : ℕ) (hB : 1 ≤ B) (v r : V)
    (hr : r ∈ TaggedDictionary.keys ((program ids L a B g.k hB).runEncoded G s v).1) :
    ∃ I : Finset (Low g.D g.Q), ∃ hI : I ∈ g.P.parts, GeneralCoveringTaskRoles.roleID G g I hI = r := by
  rw [keys] at hr
  exact GeneralCoveringTaskRoles.keys_valid G ids g v r hr

/-- Exact encoded answer at every actual participant; capacity and delivery
are consequences of accepted role acquisition and sparse simulation. -/
theorem lookup_part {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts)
    (a : ℕ) (hB : 1 ≤ B) (v : V) (hv : v ∈ vertices G g.cover g.D g.R L g.Q I) :
    TaggedDictionary.lookup ((program ids L a B g.k hB).runEncoded G s v).1
      (GeneralCoveringTaskRoles.roleID G g I hI) =
      some ((GeneralCoveringTaskIntegral.program ids a B g.k hB).runEncoded
        (MaskedTaskGraph.graph G (vertices G g.cover g.D g.R L g.Q I))
        (taskInput g.cover g.targets (vertices G g.cover g.D g.R L g.Q I)
          (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun u => (s u).2.cost)) v) := by
  have hr := (GeneralCoveringTaskRoles.keys_part G ids g I hI v).mpr hv
  have h := SparseParallelCorrect.execute_correct G ids (max 1 L)
    (GeneralCoveringTaskIntegral.program ids a B g.k hB)
    ((GeneralCoveringTaskRoles.program ids L B).runEncoded G s)
    (fun u => GeneralCoveringTaskRoles.capacity G ids L g.cover g.D g.R s g.owner g.local_rows
      g.admissible g.heavy u)
    (fun u r => GeneralCoveringTaskRoles.payload (GeneralCoveringTaskRoles.routed g.cover g.D g.R s u)
      (GeneralCoveringTaskRoles.keysAt G g.cover g.D g.R s u) r)
    (fun u => GeneralCoveringTaskRoles.consistent G ids L g.cover g.D g.R s g.owner g.local_rows u)
    v (GeneralCoveringTaskRoles.roleID G g I hI) hr
  rw [role_region G ids g I hI, full_input G g I hI] at h
  rw [run_program, Program.runEncoded_eq_run G (SparseParallel.execute ids (max 1 L)
    (GeneralCoveringTaskIntegral.program ids a B g.k hB)),
    Program.runEncoded_eq_run (MaskedTaskGraph.graph G (vertices G g.cover g.D g.R L g.Q I))]
  exact h

noncomputable def clientOutput {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (a : ℕ) (hB : 1 ≤ B) : Finset V :=
  GeneralCoveringTaskIntegral.output (MaskedTaskGraph.graph G (vertices G g.cover g.D g.R L g.Q I))
    ids a B g.k hB (taskInput g.cover g.targets (vertices G g.cover g.D g.R L g.Q I)
      (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun v => (s v).2.cost))

/-- Direct specification on the masked graph. In particular, owner support,
partners and residual demands are not recomputed on that graph. -/
theorem masked_spec {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val) :
    Spec g.cover (vertices G g.cover g.D g.R L g.Q I) (demands G g.cover g.D g.R L g.Q I g.Bdy)
      (fun v => (s v).2.cost.val) (2 * B * g.k) (clientOutput G ids g I a hB) := by
  let H := vertices G g.cover g.D g.R L g.Q I
  let T := demands G g.cover g.D g.R L g.Q I g.Bdy
  let K := GeneralCoveringTaskDiameter.maskedContext G g.cover g.D g.R L g.Q I g.local_rows
    (g.P.connected I hI) g.k (g.P.size I hI)
  let Z := GeneralCoveringTaskIntegral.witness G g.cover g.D g.R L g.Q I g.Bdy
  have hT : T ⊆ H := demands_in_vertices G g.cover g.D g.R L g.Q I g.Bdy
  have hrows : ∀ r ∈ T, g.cover r ⊆ H :=
    rows_in_vertices G g.cover g.D g.R L g.Q I g.Bdy g.local_rows
  have hlocal : ∀ r ∈ T, g.cover r ⊆ closed (MaskedTaskGraph.graph G H) r := by
    intro r hr
    rw [MaskedTaskGraph.closed_inside G H r (hT hr)]
    exact Finset.subset_inter (g.local_rows r (demands_subset G g.cover g.D g.R L g.Q I g.Bdy hr))
      (hrows r hr)
  have hpositive : ∀ v ∈ CoveringSupport.admissible g.cover T, 1 ≤ (s v).2.cost.val := by
    intro v hv
    exact hc v (service_light G g.cover g.D g.R L g.Q I g.Bdy hv).1
  have hZcost : (∑ v ∈ Z, (s v).2.cost.val) ≤ 2 * B * g.k :=
    GeneralCoveringTaskIntegral.witness_cost G g.cover g.D g.R L B g.k g.Q g.P I g.Bdy hI hD
      (fun v => (s v).2.cost) hc
  have hs := GeneralCoveringNormalizedIntegral.optimal (MaskedTaskGraph.graph G H) K T hT
    g.cover g.targets g.incidence hlocal hrows a ha
    (MinorDensity.induced_bound (MaskedTaskGraph.graph G H) (MaskedTaskGraph.density G H hden))
    B (2 * B * g.k) hB (fun v => (s v).2.cost) hpositive ids
    (taskInput g.cover g.targets H T (fun v => (s v).2.cost))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    Z (GeneralCoveringTaskIntegral.witness_admissible G g.cover g.D g.R L g.Q I g.Bdy)
    (GeneralCoveringTaskIntegral.witness_covers G g.cover g.D g.R L g.Q I g.Bdy hcover) hZcost
  have hdiam : K.diameter = 4 * g.k := rfl
  rw [hdiam] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, hs.2.2.2⟩
  exact (hs.2.2.2 Z (GeneralCoveringTaskIntegral.witness_admissible G g.cover g.D g.R L g.Q I g.Bdy)
    (GeneralCoveringTaskIntegral.witness_covers G g.cover g.D g.R L g.Q I g.Bdy hcover)).trans hZcost

/-- The literal output dictionary realizes the complete masked-client answer,
and therefore has its original-C universal integral optimum. -/
theorem part_spec {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val) :
    chosen ((program ids L a B g.k hB).runEncoded G s) (GeneralCoveringTaskRoles.roleID G g I hI) =
      clientOutput G ids g I a hB ∧
    Spec g.cover (vertices G g.cover g.D g.R L g.Q I) (demands G g.cover g.D g.R L g.Q I g.Bdy)
      (fun v => (s v).2.cost.val) (2 * B * g.k)
      (chosen ((program ids L a B g.k hB).runEncoded G s) (GeneralCoveringTaskRoles.roleID G g I hI)) := by
  have hs := masked_spec G ids g I hI hcover hD a ha hden hB hc
  have he : chosen ((program ids L a B g.k hB).runEncoded G s) (GeneralCoveringTaskRoles.roleID G g I hI) =
      clientOutput G ids g I a hB := by
    ext v
    by_cases hv : v ∈ vertices G g.cover g.D g.R L g.Q I
    · rw [mem_chosen, lookup_part G ids g I hI a hB v hv, Option.some.injEq]
      exact (GeneralCoveringTaskIntegral.mem_output
        (MaskedTaskGraph.graph G (vertices G g.cover g.D g.R L g.Q I)) ids a B g.k hB _ v).symm
    · have hr : GeneralCoveringTaskRoles.roleID G g I hI ∉
          TaggedDictionary.keys ((GeneralCoveringTaskRoles.program ids L B).runEncoded G s v) :=
        fun hr => hv ((GeneralCoveringTaskRoles.keys_part G ids g I hI v).mp hr)
      constructor
      · intro hm
        have hf := (mem_chosen _ _ v).mp hm
        rw [lookup_absent G ids L a B g.k hB s v _ hr] at hf
        cases hf
      · intro hm
        exact False.elim (hv (hs.1 hm))
  exact ⟨he, he.symm ▸ hs⟩

theorem empty_demand {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (hT : demands G g.cover g.D g.R L g.Q I g.Bdy = ∅) :
    chosen ((program ids L a B g.k hB).runEncoded G s) (GeneralCoveringTaskRoles.roleID G g I hI) = ∅ := by
  have hs := (part_spec G ids g I hI hcover hD a ha hden hB hc).2.2.1
  have hn : chosen ((program ids L a B g.k hB).runEncoded G s) (GeneralCoveringTaskRoles.roleID G g I hI) ⊆ ∅ := by
    simpa only [hT, CoveringSupport.admissible, Finset.biUnion_empty] using hs
  exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (hn hv))

theorem empty_parts {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (he : g.P.parts = ∅)
    (a : ℕ) (hB : 1 ≤ B) (v : V) : ((program ids L a B g.k hB).runEncoded G s v).1 = [] := by
  have hk : TaggedDictionary.keys ((program ids L a B g.k hB).runEncoded G s v).1 = ∅ := by
    exact (keys G ids L a B g.k hB s v).trans
      (congrArg TaggedDictionary.keys (GeneralCoveringTaskRoles.empty_parts G ids g he v))
  cases hx : ((program ids L a B g.k hB).runEncoded G s v).1 with
  | nil => rfl
  | cons p ps =>
    have hp : p.1 ∈ TaggedDictionary.keys ((program ids L a B g.k hB).runEncoded G s v).1 :=
      (TaggedDictionary.mem_keys _ p.1).mpr ⟨p, by rw [hx]; simp, rfl⟩
    rw [hk] at hp
    exact False.elim (Finset.notMem_empty _ hp)

/-- Native physical owner discovery is outside every masked client. -/
theorem fromOwners_run {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B) :
    (fromOwners ids L a B k hB).runEncoded G (fun v => (s v, fields v)) =
      (program ids L a B k hB).runEncoded G
        (fun v => ((GeneralCoveringOwnerSupport.program ids L).runEncoded G s v, fields v)) := by
  exact congrArg
    (fun xs => (SparseParallel.execute ids (max 1 L)
      (GeneralCoveringTaskIntegral.program ids a B k hB)).runEncoded G xs)
    (GeneralCoveringTaskRoles.fromOwners_run G ids L s fields)

theorem fromOwners_keys {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) (v : V) :
    TaggedDictionary.keys ((fromOwners ids L a B k hB).runEncoded G s v).1 =
      TaggedDictionary.keys ((GeneralCoveringTaskRoles.fromOwners ids L B).runEncoded G s v) := by
  change TaggedDictionary.keys (((SparseParallel.execute ids (max 1 L)
    (GeneralCoveringTaskIntegral.program ids a B k hB)).runEncoded G
    ((GeneralCoveringTaskRoles.fromOwners ids L B).runEncoded G s) v).1) = _
  rw [Program.runEncoded_eq_run]
  exact SparseParallelCorrect.execute_keys G ids (max 1 L)
    (GeneralCoveringTaskIntegral.program ids a B k hB) _ v

theorem fromOwners_correct {bits B : ℕ} (ids : BitCode V bits) (L a k : ℕ) (hB : 1 ≤ B)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    (fromOwners ids L a B k hB).runEncoded G (fun v => (s v, fields v)) =
      (program ids L a B k hB).runEncoded G (fun v =>
        (GeneralCoveringOwnerSupport.expected G cover D R L
          (fun u => ⟨s u, GeneralCoveringOwners.owner cover D R u⟩) v, fields v)) := by
  exact congrArg
    (fun xs => (SparseParallel.execute ids (max 1 L)
      (GeneralCoveringTaskIntegral.program ids a B k hB)).runEncoded G xs)
    (GeneralCoveringTaskRoles.fromOwners_correct G ids cover targets D R L hinc hlocal s fields hD hR hC ht)

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _

/-- Native per-part specification. Only truthful private original inputs and
local center name/interior fields enter, never active masks or capacity. -/
theorem fromOwners_spec {bits B : ℕ} (ids : BitCode V bits) (L a k : ℕ) (hB : 1 ≤ B)
    (cover targets : V → Finset V) (D R : Finset V) (Q : Finset D)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k) (Bdy : Finset (Low D Q))
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D)
    (hadm : D ⊆ CoveringSupport.admissible cover R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (fields v).cost.val)
    (hrole : ∀ (J : Finset (Low D Q)) (hJ : J ∈ P.parts) (i : Low D Q), i ∈ J →
      (fields i.val.val).role = some (GeneralCoveringTaskRoles.name D Q J (P.nonempty J hJ)))
    (hexcluded : ∀ d : D, d ∈ Q → (fields d.val).role = none)
    (hinterior : ∀ i : Low D Q, (fields i.val.val).interior = decide (i ∉ Bdy))
    (I : Finset (Low D Q)) (hI : I ∈ P.parts) :
    Spec cover (vertices G cover D R L Q I) (demands G cover D R L Q I Bdy)
      (fun v => (fields v).cost.val) (2 * B * k)
      (chosen ((fromOwners ids L a B k hB).runEncoded G (fun v => (s v, fields v)))
        (GeneralCoveringTaskRoles.name D Q I (P.nonempty I hI))) := by
  rw [fromOwners_correct G ids L a k hB cover targets D R hinc hlocal s fields hD hR hC ht]
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
  exact (part_spec G ids g I hI hcover hadm a ha hden hB hc).2

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (program ids L a B k hB).rounds = RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4 := by
  simp only [program, Program.rounds, GeneralCoveringTaskRoles.rounds, SparseParallel.execute_rounds,
    GeneralCoveringTaskIntegral.rounds]
  omega

theorem fromOwners_rounds {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (fromOwners ids L a B k hB).rounds = RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 8 := by
  simp only [fromOwners, Program.rounds, GeneralCoveringTaskRoles.fromOwners_rounds,
    SparseParallel.execute_rounds, GeneralCoveringTaskIntegral.rounds]
  omega

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (program ids L a B k hB).maxBits ≤ max (bits + 2)
      (max 1 L * (bits + (GeneralCoveringTaskIntegral.program ids a B k hB).maxBits + 1)) := by
  change max (GeneralCoveringTaskRoles.program ids L B).maxBits
    (SparseParallel.execute ids (max 1 L) (GeneralCoveringTaskIntegral.program ids a B k hB)).maxBits ≤ _
  rw [GeneralCoveringTaskRoles.maxBits]
  exact max_le_max (le_refl _) (SparseParallel.execute_maxBits ids (max 1 L) _)

theorem fromOwners_maxBits {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (fromOwners ids L a B k hB).maxBits ≤ max (bits + 2)
      (max 1 L * (bits + (GeneralCoveringTaskIntegral.program ids a B k hB).maxBits + 1)) := by
  change max (GeneralCoveringTaskRoles.fromOwners ids L B).maxBits
    (SparseParallel.execute ids (max 1 L) (GeneralCoveringTaskIntegral.program ids a B k hB)).maxBits ≤ _
  rw [GeneralCoveringTaskRoles.fromOwners_maxBits]
  exact max_le_max (le_refl _) (SparseParallel.execute_maxBits ids (max 1 L) _)

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    let K := max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k) + 1) + 1))
    (program ids L a B k hB).maxBits ≤ K * Nat.clog 2 (n + 2) ∧
      (fromOwners ids L a B k hB).maxBits ≤ K * Nat.clog 2 (n + 2) := by
  dsimp only
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hp : bits + 2 ≤ (c + 2) * Nat.clog 2 (n + 2) := by nlinarith
  have hc := GeneralCoveringTaskIntegral.logarithmic_bits ids a B k hB n c hids
  have hm : bits + (GeneralCoveringTaskIntegral.program ids a B k hB).maxBits + 1 ≤
      (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k) + 1) + 1) *
        Nat.clog 2 (n + 2) := by nlinarith
  have hbound := max_le_max hp (Nat.mul_le_mul_left (max 1 L) hm)
  rw [← Nat.mul_assoc, Nat.mul_max_mul_right] at hbound
  exact ⟨(maxBits ids L a B k hB).trans hbound,
    (fromOwners_maxBits ids L a B k hB).trans hbound⟩

end Paper.GeneralCoveringTaskParallel

#print axioms Paper.GeneralCoveringTaskParallel.run_program
#print axioms Paper.GeneralCoveringTaskParallel.keys
#print axioms Paper.GeneralCoveringTaskParallel.lookup_absent
#print axioms Paper.GeneralCoveringTaskParallel.role_region
#print axioms Paper.GeneralCoveringTaskParallel.full_input
#print axioms Paper.GeneralCoveringTaskParallel.keys_part
#print axioms Paper.GeneralCoveringTaskParallel.keys_valid
#print axioms Paper.GeneralCoveringTaskParallel.lookup_part
#print axioms Paper.GeneralCoveringTaskParallel.masked_spec
#print axioms Paper.GeneralCoveringTaskParallel.part_spec
#print axioms Paper.GeneralCoveringTaskParallel.empty_demand
#print axioms Paper.GeneralCoveringTaskParallel.empty_parts
#print axioms Paper.GeneralCoveringTaskParallel.fromOwners_run
#print axioms Paper.GeneralCoveringTaskParallel.fromOwners_keys
#print axioms Paper.GeneralCoveringTaskParallel.fromOwners_correct
#print axioms Paper.GeneralCoveringTaskParallel.fromOwners_spec
#print axioms Paper.GeneralCoveringTaskParallel.rounds
#print axioms Paper.GeneralCoveringTaskParallel.fromOwners_rounds
#print axioms Paper.GeneralCoveringTaskParallel.maxBits
#print axioms Paper.GeneralCoveringTaskParallel.fromOwners_maxBits
#print axioms Paper.GeneralCoveringTaskParallel.logarithmic_bits
