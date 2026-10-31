import Paper.Solver.LocalSearch.GeneralCoveringTaskParallel

/-! Local selection from actual sparse output dictionaries. The analysis union
enumerates actual owner parts only in proofs, never in the executable. For the
actual boundary of that same partition, disjoint true service sets charge the
sum of all simultaneously computed integral optima to any original C-cover.
This covers the union of task demands, not the unrepaired original instance. -/
namespace Paper.GeneralCoveringTaskAggregate
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input (V : Type) (B : ℕ) := GeneralCoveringTaskParallel.Input V B

/-- Inspect keys and their actual first-match lookup, not arbitrary stored values. -/
def select (s : GeneralCoveringTaskParallel.Output V) : Bool :=
  (TaggedDictionary.keys s.1).sort.any (fun r => decide (TaggedDictionary.lookup s.1 r = some true))

def finish : Program V (GeneralCoveringTaskParallel.Output V) Bool :=
  .local (fun _ _ s => select s)

def program {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) Bool :=
  .seq (GeneralCoveringTaskParallel.program ids L a B k hB) finish

def fromOwners {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    Program V (GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) Bool :=
  .seq (GeneralCoveringTaskParallel.fromOwners ids L a B k hB) finish

theorem select_iff (s : GeneralCoveringTaskParallel.Output V) :
    select s = true ↔ ∃ r ∈ TaggedDictionary.keys s.1, TaggedDictionary.lookup s.1 r = some true := by
  simp only [select, List.any_eq_true, Finset.mem_sort, decide_eq_true_eq]

theorem lookup_key (xs : List (V × Bool)) (r : V) (h : TaggedDictionary.lookup xs r = some true) :
    r ∈ TaggedDictionary.keys xs := by
  by_contra hn
  have hf : TaggedDictionary.lookup xs r = none := by
    simp only [TaggedDictionary.lookup, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq]
    intro p hp he
    exact hn ((TaggedDictionary.mem_keys xs r).mpr ⟨p, hp, he⟩)
  rw [hf] at h
  cases h

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G cover D R L Q).Adj := fun _ _ => Classical.propDecidable _

theorem run_program {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    (program ids L a B k hB).runEncoded G s v =
      select ((GeneralCoveringTaskParallel.program ids L a B k hB).runEncoded G s v) := rfl

theorem fromOwners_run {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) (v : V) :
    (fromOwners ids L a B k hB).runEncoded G s v =
      select ((GeneralCoveringTaskParallel.fromOwners ids L a B k hB).runEncoded G s v) := rfl

def output {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => (program ids L a B k hB).runEncoded G s v)

def fromOwners_output {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → GeneralCoveringOwners.Input V × GeneralCoveringTaskRoles.Fields V B) : Finset V :=
  Finset.univ.filter (fun v => (fromOwners ids L a B k hB).runEncoded G s v)

theorem mem_output {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    v ∈ output G ids L a B k hB s ↔ (program ids L a B k hB).runEncoded G s v = true := by
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A total analysis family; no name or default vertex is invented for nonparts. -/
noncomputable def partChosen {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a : ℕ) (hB : 1 ≤ B)
    (I : Finset (Low g.D g.Q)) : Finset V :=
  if hI : I ∈ g.P.parts then
    GeneralCoveringTaskParallel.chosen ((GeneralCoveringTaskParallel.program ids L a B g.k hB).runEncoded G s)
      (GeneralCoveringTaskRoles.roleID G g I hI)
  else ∅

theorem partChosen_eq {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a : ℕ) (hB : 1 ≤ B)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) :
    partChosen G ids g a hB I =
      GeneralCoveringTaskParallel.chosen ((GeneralCoveringTaskParallel.program ids L a B g.k hB).runEncoded G s)
        (GeneralCoveringTaskRoles.roleID G g I hI) := dif_pos hI

/-- Each acquired output key identifies exactly one genuine owner part. -/
theorem key_part_unique {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a : ℕ) (hB : 1 ≤ B) (v r : V)
    (hr : r ∈ TaggedDictionary.keys ((GeneralCoveringTaskParallel.program ids L a B g.k hB).runEncoded G s v).1) :
    ∃ I : Finset (Low g.D g.Q), ∃ hI : I ∈ g.P.parts,
      GeneralCoveringTaskRoles.roleID G g I hI = r ∧
        ∀ J : Finset (Low g.D g.Q), ∀ hJ : J ∈ g.P.parts,
          GeneralCoveringTaskRoles.roleID G g J hJ = r → J = I := by
  obtain ⟨I, hI, he⟩ := GeneralCoveringTaskParallel.keys_valid G ids g a hB v r hr
  refine ⟨I, hI, he, ?_⟩
  intro J hJ hJr
  exact GeneralCoveringTaskRoles.name_injective g.D g.Q g.P.parts g.P.disjoint J I hJ hI
    (g.P.nonempty J hJ) (g.P.nonempty I hI) (hJr.trans he.symm)

/-- Literal aggregate output equals the union of the actual per-part chosen sets. -/
theorem output_union {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (a : ℕ) (hB : 1 ≤ B) :
    output G ids L a B g.k hB s = g.P.parts.biUnion (partChosen G ids g a hB) := by
  ext v
  rw [mem_output, run_program, select_iff, Finset.mem_biUnion]
  constructor
  · rintro ⟨r, hr, hf⟩
    obtain ⟨I, hI, he, _⟩ := key_part_unique G ids g a hB v r hr
    refine ⟨I, hI, ?_⟩
    rw [partChosen_eq G ids g a hB I hI]
    apply (GeneralCoveringTaskParallel.mem_chosen _ _ v).mpr
    rw [he]
    exact hf
  · rintro ⟨I, hI, hv⟩
    rw [partChosen_eq G ids g a hB I hI] at hv
    have hf := (GeneralCoveringTaskParallel.mem_chosen _ _ v).mp hv
    exact ⟨GeneralCoveringTaskRoles.roleID G g I hI, lookup_key _ _ hf, hf⟩

noncomputable def taskDemands {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) : Finset V :=
  g.P.parts.biUnion (fun I => demands G g.cover g.D g.R L g.Q I g.Bdy)

noncomputable def taskService {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) : Finset V :=
  g.P.parts.biUnion (fun I => service G g.cover g.D g.R L g.Q I g.Bdy)

theorem solved {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (I : Finset (Low g.D g.Q)) (hI : I ∈ g.P.parts) :
    GeneralCoveringTaskParallel.Spec g.cover (vertices G g.cover g.D g.R L g.Q I)
      (demands G g.cover g.D g.R L g.Q I g.Bdy) (fun v => (s v).2.cost.val)
      (2 * B * g.k) (partChosen G ids g a hB I) := by
  rw [partChosen_eq G ids g a hB I hI]
  exact (GeneralCoveringTaskParallel.part_spec G ids g I hI hcover hD a ha hden hB hc).2

theorem support_cover {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val) :
    output G ids L a B g.k hB s ⊆ taskService G g ∧
      output G ids L a B g.k hB s ⊆ CoveringSupport.admissible g.cover g.R ∧
      GeneralCoveringNormalizedIntegral.Covers g.cover (taskDemands G g) (output G ids L a B g.k hB s) := by
  have hs : output G ids L a B g.k hB s ⊆ taskService G g := by
    intro v hv
    rw [output_union G ids g a hB] at hv
    obtain ⟨I, hI, hv⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨I, hI, (solved G ids g hcover hD a ha hden hB hc I hI).2.1 hv⟩
  refine ⟨hs, ?_, ?_⟩
  · intro v hv
    obtain ⟨I, _, hv⟩ := Finset.mem_biUnion.mp (hs hv)
    exact (service_light G g.cover g.D g.R L g.Q I g.Bdy hv).1
  · intro r hr
    obtain ⟨I, hI, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨v, hv, hvr⟩ := (solved G ids g hcover hD a ha hden hB hc I hI).2.2.1 r hr
    refine ⟨v, ?_, hvr⟩
    rw [output_union G ids g a hB]
    exact Finset.mem_biUnion.mpr ⟨I, hI, hv⟩

/-- A restriction of any original integral cover covers the corresponding task. -/
theorem restriction_covers {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (W : Finset V)
    (hW : GeneralCoveringNormalizedIntegral.Covers g.cover g.R W) (I : Finset (Low g.D g.Q)) :
    GeneralCoveringNormalizedIntegral.Covers g.cover (demands G g.cover g.D g.R L g.Q I g.Bdy)
      (W ∩ service G g.cover g.D g.R L g.Q I g.Bdy) := by
  intro r hr
  obtain ⟨v, hv, hvr⟩ := hW r (demands_subset G g.cover g.D g.R L g.Q I g.Bdy hr)
  exact ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_biUnion.mpr ⟨r, hr, hvr⟩⟩, hvr⟩

/-- Disjointness is derived from the actual boundary of this exact partition. -/
theorem services_disjoint {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts) :
    Set.PairwiseDisjoint (↑g.P.parts) (fun I => service G g.cover g.D g.R L g.Q I g.Bdy) := by
  intro I hI J hJ hne
  rw [hboundary]
  exact service_disjoint G g.cover g.D g.R L g.Q g.local_rows g.k g.P I J hI hJ hne

theorem sum_restrictions {L B : ℕ} {s : V → Input V B}
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts)
    (c : V → ℕ) (W : Finset V) :
    (∑ I ∈ g.P.parts, ∑ v ∈ W ∩ service G g.cover g.D g.R L g.Q I g.Bdy, c v) ≤ ∑ v ∈ W, c v := by
  have hd : Set.PairwiseDisjoint (↑g.P.parts) (fun I => W ∩ service G g.cover g.D g.R L g.Q I g.Bdy) := by
    intro I hI J hJ hne
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    exact Finset.disjoint_left.mp (services_disjoint G g hboundary hI hJ hne)
      (Finset.mem_inter.mp hvI).2 (Finset.mem_inter.mp hvJ).2
  calc
    _ = ∑ v ∈ g.P.parts.biUnion (fun I => W ∩ service G g.cover g.D g.R L g.Q I g.Bdy), c v :=
      (Finset.sum_biUnion hd).symm
    _ ≤ ∑ v ∈ W, c v := Finset.sum_le_sum_of_subset (by
      intro v hv
      obtain ⟨I, _, hv⟩ := Finset.mem_biUnion.mp hv
      exact (Finset.mem_inter.mp hv).1)

/-- Sum of the actual simultaneously computed optimum costs, not supplied OPTs. -/
theorem sum_optimal {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts)
    (W : Finset V) (hW : GeneralCoveringNormalizedIntegral.Covers g.cover g.R W) :
    (∑ I ∈ g.P.parts, ∑ v ∈ partChosen G ids g a hB I, (s v).2.cost.val) ≤ ∑ v ∈ W, (s v).2.cost.val := by
  calc
    _ ≤ ∑ I ∈ g.P.parts, ∑ v ∈ W ∩ service G g.cover g.D g.R L g.Q I g.Bdy, (s v).2.cost.val := by
      apply Finset.sum_le_sum
      intro I hI
      exact (solved G ids g hcover hD a ha hden hB hc I hI).2.2.2.2
        (W ∩ service G g.cover g.D g.R L g.Q I g.Bdy) Finset.inter_subset_right (restriction_covers G g W hW I)
    _ ≤ ∑ v ∈ W, (s v).2.cost.val := sum_restrictions G g hboundary (fun v => (s v).2.cost.val) W

theorem union_cost {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts) :
    (∑ v ∈ output G ids L a B g.k hB s, (s v).2.cost.val) =
      ∑ I ∈ g.P.parts, ∑ v ∈ partChosen G ids g a hB I, (s v).2.cost.val := by
  have hd : Set.PairwiseDisjoint (↑g.P.parts) (partChosen G ids g a hB) := by
    intro I hI J hJ hne
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    exact Finset.disjoint_left.mp (services_disjoint G g hboundary hI hJ hne)
      ((solved G ids g hcover hD a ha hden hB hc I hI).2.1 hvI)
      ((solved G ids g hcover hD a ha hden hB hc J hJ).2.1 hvJ)
  rw [output_union G ids g a hB]
  exact Finset.sum_biUnion hd

/-- Simultaneous exact tasks and their sumOPT bound against every original
integral cover. Original heavy/high/boundary repair is not asserted. -/
theorem aggregate_spec {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s)
    (hcover : GeneralCoveringInitializerPass.Covers g.cover g.R g.D)
    (hD : g.D ⊆ CoveringSupport.admissible g.cover g.R)
    (a : ℕ) (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ)) (hB : 1 ≤ B)
    (hc : ∀ v ∈ CoveringSupport.admissible g.cover g.R, 1 ≤ (s v).2.cost.val)
    (hboundary : g.Bdy = BoundaryOwners.vertices (graph G g.cover g.D g.R L g.Q) Finset.univ g.P.parts) :
    output G ids L a B g.k hB s ⊆ taskService G g ∧
      output G ids L a B g.k hB s ⊆ CoveringSupport.admissible g.cover g.R ∧
      GeneralCoveringNormalizedIntegral.Covers g.cover (taskDemands G g) (output G ids L a B g.k hB s) ∧
      ∀ W : Finset V, GeneralCoveringNormalizedIntegral.Covers g.cover g.R W →
        (∑ I ∈ g.P.parts, ∑ v ∈ partChosen G ids g a hB I, (s v).2.cost.val) ≤ ∑ v ∈ W, (s v).2.cost.val ∧
        (∑ v ∈ output G ids L a B g.k hB s, (s v).2.cost.val) ≤ ∑ v ∈ W, (s v).2.cost.val := by
  have hs := support_cover G ids g hcover hD a ha hden hB hc
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  intro W hW
  have hsum := sum_optimal G ids g hcover hD a ha hden hB hc hboundary W hW
  refine ⟨hsum, ?_⟩
  rw [union_cost G ids g hcover hD a ha hden hB hc hboundary]
  exact hsum

theorem empty_parts {bits L B : ℕ} {s : V → Input V B} (ids : BitCode V bits)
    (g : GeneralCoveringTaskRoles.Geometry G L B s) (he : g.P.parts = ∅) (a : ℕ) (hB : 1 ≤ B) :
    output G ids L a B g.k hB s = ∅ ∧ ∀ v, (program ids L a B g.k hB).runEncoded G s v = false := by
  have hout : output G ids L a B g.k hB s = ∅ := by
    rw [output_union G ids g a hB, he, Finset.biUnion_empty]
  refine ⟨hout, ?_⟩
  intro v
  cases hf : (program ids L a B g.k hB).runEncoded G s v with
  | false => rfl
  | true =>
    exfalso
    have hv := (mem_output G ids L a B g.k hB s v).mpr hf
    exact Finset.notMem_empty v (hout ▸ hv)

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
  exact congrArg (fun out : V → GeneralCoveringTaskParallel.Output V => fun v => select (out v))
    (GeneralCoveringTaskParallel.fromOwners_correct G ids L a k hB cover targets D R hinc hlocal s fields hD hR hC ht)

theorem fromOwners_output_eq {bits B : ℕ} (ids : BitCode V bits) (L a k : ℕ) (hB : 1 ≤ B)
    (cover targets : V → Finset V) (D R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    fromOwners_output G ids L a B k hB (fun v => (s v, fields v)) =
      output G ids L a B k hB (fun v =>
        (GeneralCoveringOwnerSupport.expected G cover D R L
          (fun u => ⟨s u, GeneralCoveringOwners.owner cover D R u⟩) v, fields v)) := by
  exact congrArg (fun labels : V → Bool => Finset.univ.filter (fun v => labels v))
    (fromOwners_correct G ids L a k hB cover targets D R hinc hlocal s fields hD hR hC ht)

/-- Native physical acquisition, simultaneous masked solve and local aggregation.
Only local center names/interior flags remain an intermediate interface. -/
theorem fromOwners_spec {bits B : ℕ} (ids : BitCode V bits) (L a k : ℕ) (hB : 1 ≤ B)
    (cover targets : V → Finset V) (D R : Finset V) (Q : Finset D)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k) (Bdy : Finset (Low D Q))
    (hboundary : Bdy = BoundaryOwners.vertices (graph G cover D R L Q) Finset.univ P.parts)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D) (hadm : D ⊆ CoveringSupport.admissible cover R)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (s : V → GeneralCoveringOwners.Input V) (fields : V → GeneralCoveringTaskRoles.Fields V B)
    (hD : ∀ v, (s v).center = decide (v ∈ D)) (hR : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (fields v).cost.val)
    (hrole : ∀ (J : Finset (Low D Q)) (hJ : J ∈ P.parts) (i : Low D Q), i ∈ J →
      (fields i.val.val).role = some (GeneralCoveringTaskRoles.name D Q J (P.nonempty J hJ)))
    (hexcluded : ∀ d : D, d ∈ Q → (fields d.val).role = none)
    (hinterior : ∀ i : Low D Q, (fields i.val.val).interior = decide (i ∉ Bdy)) :
    let O := fromOwners_output G ids L a B k hB (fun v => (s v, fields v))
    O ⊆ P.parts.biUnion (fun I => service G cover D R L Q I Bdy) ∧
      O ⊆ CoveringSupport.admissible cover R ∧
      GeneralCoveringNormalizedIntegral.Covers cover
        (P.parts.biUnion (fun I => demands G cover D R L Q I Bdy)) O ∧
      ∀ W : Finset V, GeneralCoveringNormalizedIntegral.Covers cover R W →
        (∑ v ∈ O, (fields v).cost.val) ≤ ∑ v ∈ W, (fields v).cost.val := by
  dsimp only
  rw [fromOwners_output_eq G ids L a k hB cover targets D R hinc hlocal s fields hD hR hC ht]
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
  have hs := aggregate_spec G ids g hcover hadm a ha hden hB hc hboundary
  exact ⟨hs.1, hs.2.1, hs.2.2.1, fun W hW => (hs.2.2.2 W hW).2⟩

theorem rounds {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (program ids L a B k hB).rounds = RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 4 := by
  simp only [program, finish, Program.rounds, Nat.add_zero, GeneralCoveringTaskParallel.rounds]

theorem fromOwners_rounds {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (fromOwners ids L a B k hB).rounds = RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 8 := by
  simp only [fromOwners, finish, Program.rounds, Nat.add_zero, GeneralCoveringTaskParallel.fromOwners_rounds]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (program ids L a B k hB).maxBits = (GeneralCoveringTaskParallel.program ids L a B k hB).maxBits := by
  change max _ 0 = _
  exact Nat.max_zero _

theorem fromOwners_maxBits_eq {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B) :
    (fromOwners ids L a B k hB).maxBits = (GeneralCoveringTaskParallel.fromOwners ids L a B k hB).maxBits := by
  change max _ 0 = _
  exact Nat.max_zero _

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (L a B k : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    let K := max (c + 2) (max 1 L * (c + (3 * c + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k) + 1) + 1))
    (program ids L a B k hB).maxBits ≤ K * Nat.clog 2 (n + 2) ∧
      (fromOwners ids L a B k hB).maxBits ≤ K * Nat.clog 2 (n + 2) := by
  dsimp only
  rw [maxBits_eq, fromOwners_maxBits_eq]
  exact GeneralCoveringTaskParallel.logarithmic_bits ids L a B k hB n c hids

end Paper.GeneralCoveringTaskAggregate

#print axioms Paper.GeneralCoveringTaskAggregate.select_iff
#print axioms Paper.GeneralCoveringTaskAggregate.lookup_key
#print axioms Paper.GeneralCoveringTaskAggregate.run_program
#print axioms Paper.GeneralCoveringTaskAggregate.fromOwners_run
#print axioms Paper.GeneralCoveringTaskAggregate.key_part_unique
#print axioms Paper.GeneralCoveringTaskAggregate.output_union
#print axioms Paper.GeneralCoveringTaskAggregate.solved
#print axioms Paper.GeneralCoveringTaskAggregate.support_cover
#print axioms Paper.GeneralCoveringTaskAggregate.restriction_covers
#print axioms Paper.GeneralCoveringTaskAggregate.services_disjoint
#print axioms Paper.GeneralCoveringTaskAggregate.sum_restrictions
#print axioms Paper.GeneralCoveringTaskAggregate.sum_optimal
#print axioms Paper.GeneralCoveringTaskAggregate.union_cost
#print axioms Paper.GeneralCoveringTaskAggregate.aggregate_spec
#print axioms Paper.GeneralCoveringTaskAggregate.empty_parts
#print axioms Paper.GeneralCoveringTaskAggregate.fromOwners_correct
#print axioms Paper.GeneralCoveringTaskAggregate.fromOwners_output_eq
#print axioms Paper.GeneralCoveringTaskAggregate.fromOwners_spec
#print axioms Paper.GeneralCoveringTaskAggregate.rounds
#print axioms Paper.GeneralCoveringTaskAggregate.fromOwners_rounds
#print axioms Paper.GeneralCoveringTaskAggregate.maxBits_eq
#print axioms Paper.GeneralCoveringTaskAggregate.fromOwners_maxBits_eq
#print axioms Paper.GeneralCoveringTaskAggregate.logarithmic_bits
