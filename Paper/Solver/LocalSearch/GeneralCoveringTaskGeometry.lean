import Paper.Solver.LocalSearch.GeneralCoveringPartners
import Paper.Owners.Construction.OwnerInteraction
import Paper.Owners.Construction.BoundaryOwners
import Paper.Preliminaries.PartMembership

/-! Concrete task geometry for the arbitrary-covering initializer output.
Only the generic interaction, partition uniqueness and boundary APIs are
reused. Every owner, support, residual and partner below is the accepted
original-C construction. Partitions in this file are proof-side data only;
no executable accepting a partition oracle is claimed. -/
namespace Paper.GeneralCoveringTaskGeometry
open SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lightSupport (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) : Finset V :=
  if v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L then
    GeneralCoveringOwnerSupport.support G C D R v else ∅

theorem mem_lightSupport (C : V → Finset V) (D R : Finset V) (L : ℕ) (v i : V) :
    i ∈ lightSupport G C D R L v ↔ v ∈ CoveringSupport.admissible C R ∧
      v ∉ GeneralCoveringOwnerSupport.heavy G C D R L ∧
      i ∈ GeneralCoveringOwnerSupport.support G C D R v := by
  by_cases hv : v ∈ CoveringSupport.admissible C R ∧
      v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · rw [lightSupport, if_pos hv]
    exact ⟨fun hi => ⟨hv.1, hv.2, hi⟩, fun hi => hi.2.2⟩
  · rw [lightSupport, if_neg hv]
    constructor
    · intro hi
      exact False.elim (Finset.notMem_empty _ hi)
    · intro hi
      exact False.elim (hv ⟨hi.1, hi.2.1⟩)

theorem lightSupport_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) :
    (lightSupport G C D R L v).card ≤ L := by
  by_cases hv : v ∈ CoveringSupport.admissible C R ∧
      v ∉ GeneralCoveringOwnerSupport.heavy G C D R L
  · rw [lightSupport, if_pos hv]
    have hn : ¬ L < (GeneralCoveringOwnerSupport.support G C D R v).card := by
      intro hlarge
      exact hv.2 (Finset.mem_filter.mpr ⟨hv.1, hlarge⟩)
    omega
  · simpa only [lightSupport, if_neg hv, Finset.card_empty] using (Nat.zero_le L)

theorem lightSupport_labels (C : V → Finset V) (D R : Finset V) (L : ℕ) (v : V) :
    lightSupport G C D R L v ⊆ D := by
  intro i hi
  exact GeneralCoveringOwnerSupport.support_labels G C D R v
    ((mem_lightSupport G C D R L v i).mp hi).2.2

noncomputable def ownerGraph (C : V → Finset V) (D R : Finset V) (L : ℕ) : SimpleGraph D :=
  OwnerInteraction.interaction D (lightSupport G C D R L)

abbrev Low (D : Finset V) (Q : Finset D) := {d : D // d ∉ Q}

noncomputable def graph (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    SimpleGraph (Low D Q) := (ownerGraph G C D R L).induce {d | d ∉ Q}

noncomputable local instance graphAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D) :
    DecidableRel (graph G C D R L Q).Adj := fun _ _ => Classical.propDecidable _

noncomputable def demands (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) : Finset V :=
  (GeneralCoveringOwnerSupport.residual G C D R L).filter (fun r =>
    ∃ i : Low D Q, i ∈ I ∧ i ∉ Bdy ∧ GeneralCoveringOwners.owner C D R r = some i.val.val)

/-- Useful service candidates use actual C-incidences, not closed neighborhoods. -/
noncomputable def service (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) : Finset V := (demands G C D R L Q I Bdy).biUnion C

/-- Physical communication vertices: full owner stars in I, together with
light admissible candidates whose physical S0 contains an owner in I. -/
noncomputable def vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) : Finset V :=
  I.biUnion (fun i => GeneralCoveringOwners.fiber C D R i.val.val) ∪
    Finset.univ.filter (fun v => ∃ i ∈ I, i.val.val ∈ lightSupport G C D R L v)

theorem demands_subset (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) : demands G C D R L Q I Bdy ⊆ R := by
  intro r hr
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1

theorem served_owner (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {v : V} (hv : v ∈ service G C D R L Q I Bdy) :
    ∃ i : Low D Q, i ∈ I ∧ i ∉ Bdy ∧ i.val.val ∈ lightSupport G C D R L v := by
  obtain ⟨r, hr, hvC⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨hrRes, i, hiI, hiB, ho⟩ := Finset.mem_filter.mp hr
  have hc := GeneralCoveringOwnerSupport.residual_candidates G C D R L hrRes hvC
  have hs := GeneralCoveringOwnerSupport.incidence_label G C D R hlocal
    (Finset.mem_filter.mp hrRes).1 hvC ho
  exact ⟨i, hiI, hiB, (mem_lightSupport G C D R L v i.val.val).mpr ⟨hc.1, hc.2.1, hs⟩⟩

theorem service_light (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) {v : V} (hv : v ∈ service G C D R L Q I Bdy) :
    v ∈ CoveringSupport.admissible C R ∧ v ∉ GeneralCoveringOwnerSupport.heavy G C D R L ∧
      (GeneralCoveringOwnerSupport.support G C D R v).card ≤ L := by
  obtain ⟨r, hr, hvC⟩ := Finset.mem_biUnion.mp hv
  exact GeneralCoveringOwnerSupport.residual_candidates G C D R L (Finset.mem_filter.mp hr).1 hvC

theorem demands_in_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) : demands G C D R L Q I Bdy ⊆ vertices G C D R L Q I := by
  intro r hr
  obtain ⟨hrRes, i, hiI, _, ho⟩ := Finset.mem_filter.mp hr
  have hrR := (Finset.mem_filter.mp hrRes).1
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hiI,
    Finset.mem_filter.mpr ⟨Finset.mem_union_left D hrR, ho⟩⟩)

theorem service_in_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    service G C D R L Q I Bdy ⊆ vertices G C D R L Q I := by
  intro v hv
  obtain ⟨i, hiI, _, hs⟩ := served_owner G C D R L Q I Bdy hlocal hv
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hiI, hs⟩)

theorem rows_in_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    ∀ r ∈ demands G C D R L Q I Bdy, C r ⊆ vertices G C D R L Q I := by
  intro r hr v hv
  exact service_in_vertices G C D R L Q I Bdy hlocal (Finset.mem_biUnion.mpr ⟨r, hr, hv⟩)

/-- The partition is proof-side data. Shared true service candidates force
an interaction edge, which cannot join distinct interior parts. -/
theorem service_disjoint (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k)
    (I J : Finset (Low D Q)) (hI : I ∈ P.parts) (hJ : J ∈ P.parts) (hne : I ≠ J) :
    let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
    Disjoint (service G C D R L Q I Bdy) (service G C D R L Q J Bdy) := by
  dsimp only
  let Bdy := BoundaryOwners.vertices (graph G C D R L Q) Finset.univ P.parts
  apply Finset.disjoint_left.mpr
  intro v hvI hvJ
  obtain ⟨i, hiI, hiB, his⟩ := served_owner G C D R L Q I Bdy hlocal hvI
  obtain ⟨j, hjJ, _, hjs⟩ := served_owner G C D R L Q J Bdy hlocal hvJ
  by_cases hij : i = j
  · exact hne (PartMembership.unique _ P hI hJ hiI (hij ▸ hjJ))
  · have ha : (graph G C D R L Q).Adj i j :=
      ⟨fun he => hij (Subtype.ext he), v, his, hjs⟩
    obtain ⟨U, hU, hiU, hjU⟩ := BoundaryOwners.same_part (graph G C D R L Q) Finset.univ P.parts
      (Finset.mem_univ i) (Finset.mem_univ j) ha hiB
    exact hne ((PartMembership.unique _ P hI hU hiI hiU).trans
      (PartMembership.unique _ P hU hJ hjU hjJ))

theorem owner_in_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) {i : Low D Q} (hi : i ∈ I) : i.val.val ∈ vertices G C D R L Q I :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr
    ⟨i, hi, GeneralCoveringOwners.fiber_center C D R i.val.property⟩)

theorem partner_in_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {i : Low D Q} (hi : i ∈ I) {v : V}
    (hp : GeneralCoveringPartners.partner G C D R L i.val.val = some v) :
    v ∈ vertices G C D R L Q I := by
  have hc := GeneralCoveringPartners.light_admissible G C D R L hp
  have hs := GeneralCoveringPartners.owner_in_support G C D R L hlocal hp
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi,
    (mem_lightSupport G C D R L v i.val.val).mpr ⟨hc.1, hc.2.1, hs⟩⟩)

noncomputable def benchmark (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) : Finset V :=
  I.biUnion (fun i => GeneralCoveringPartners.bundle G C D R L i.val.val)

theorem benchmark_in_vertices (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) :
    benchmark G C D R L Q I ⊆ vertices G C D R L Q I := by
  intro v hv
  obtain ⟨i, hi, hv⟩ := Finset.mem_biUnion.mp hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have he : v = i.val.val := Finset.mem_singleton.mp hv
    exact he.symm ▸ owner_in_vertices G C D R L Q I hi
  · have hp : GeneralCoveringPartners.partner G C D R L i.val.val = some v := by simpa using hv
    exact partner_in_vertices G C D R L Q I hlocal hi hp

theorem benchmark_covers (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hcover : GeneralCoveringInitializerPass.Covers C R D) :
    GeneralCoveringInitializerPass.Covers C (demands G C D R L Q I Bdy) (benchmark G C D R L Q I) := by
  intro r hr
  obtain ⟨hrRes, i, hiI, _, ho⟩ := Finset.mem_filter.mp hr
  obtain ⟨v, hv, hvC⟩ := GeneralCoveringPartners.bundle_covers G C D R L hcover i.val.property hrRes ho
  exact ⟨v, Finset.mem_biUnion.mpr ⟨i, hiI, hv⟩, hvC⟩

theorem bundle_admissible (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (hD : D ⊆ CoveringSupport.admissible C R) {i : V} (hi : i ∈ D) :
    GeneralCoveringPartners.bundle G C D R L i ⊆ CoveringSupport.admissible C R := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have he : v = i := Finset.mem_singleton.mp hv
    exact he.symm ▸ hD hi
  · have hp : GeneralCoveringPartners.partner G C D R L i = some v := by simpa using hv
    exact (GeneralCoveringPartners.light_admissible G C D R L hp).1

theorem benchmark_admissible (C : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q)) (hD : D ⊆ CoveringSupport.admissible C R) :
    benchmark G C D R L Q I ⊆ CoveringSupport.admissible C R := by
  intro v hv
  obtain ⟨i, _, hv⟩ := Finset.mem_biUnion.mp hv
  exact bundle_admissible G C D R L hD i.val.property hv

/-- The union cost is at most the sum with multiplicity; shared partners
therefore cause no extra charge. Costs need bounds only on admissible vertices. -/
theorem benchmark_cost (C : V → Finset V) (D R : Finset V) (L B : ℕ) (Q : Finset D)
    (c : V → ℝ) (hD : D ⊆ CoveringSupport.admissible C R)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B)
    (I : Finset (Low D Q)) :
    (∑ v ∈ benchmark G C D R L Q I, c v) ≤ 2 * (B : ℝ) * I.card := by
  induction I using Finset.induction_on with
  | empty => simp [benchmark]
  | @insert i I hi ih =>
    let A := GeneralCoveringPartners.bundle G C D R L i.val.val
    let W := benchmark G C D R L Q I
    have hA : A ⊆ CoveringSupport.admissible C R := bundle_admissible G C D R L hD i.val.property
    have he := Finset.sum_union_inter (s₁ := A) (s₂ := W) (f := c)
    have hn : 0 ≤ ∑ v ∈ A ∩ W, c v :=
      Finset.sum_nonneg (fun v hv => zero_le_one.trans (hc v (hA (Finset.mem_inter.mp hv).1)).1)
    have hu : (∑ v ∈ A ∪ W, c v) ≤ (∑ v ∈ A, c v) + ∑ v ∈ W, c v := by linarith
    have hAc : (∑ v ∈ A, c v) ≤ 2 * (B : ℝ) :=
      GeneralCoveringPartners.bundle_cost G C D R L B c hD i.val.property (fun v hv => (hc v hv).2)
    rw [benchmark, Finset.biUnion_insert]
    calc
      _ ≤ (∑ v ∈ A, c v) + ∑ v ∈ W, c v := hu
      _ ≤ 2 * (B : ℝ) + 2 * (B : ℝ) * I.card := add_le_add hAc ih
      _ = 2 * (B : ℝ) * (insert i I).card := by
        rw [Finset.card_insert_of_notMem hi]
        push_cast
        ring

theorem local_benchmark (C : V → Finset V) (D R : Finset V) (L B k : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hsize : I.card ≤ k)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) (hD : D ⊆ CoveringSupport.admissible C R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B) :
    ∃ W : Finset V, W ⊆ vertices G C D R L Q I ∧ W ⊆ CoveringSupport.admissible C R ∧
      GeneralCoveringInitializerPass.Covers C (demands G C D R L Q I Bdy) W ∧
      (∑ v ∈ W, c v) ≤ 2 * (B : ℝ) * k := by
  refine ⟨benchmark G C D R L Q I, benchmark_in_vertices G C D R L Q I hlocal,
    benchmark_admissible G C D R L Q I hD, benchmark_covers G C D R L Q I Bdy hcover, ?_⟩
  exact (benchmark_cost G C D R L B Q c hD hc I).trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) (by positivity))

/-- A partition part supplies the required public k bound directly. No
assumption about residual/output size or an optimal cover is introduced. -/
theorem part_benchmark (C : V → Finset V) (D R : Finset V) (L B k : ℕ) (Q : Finset D)
    (P : SmallParts.Data (graph G C D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (hcover : GeneralCoveringInitializerPass.Covers C R D) (hD : D ⊆ CoveringSupport.admissible C R)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B) :
    ∃ W : Finset V, W ⊆ vertices G C D R L Q I ∧ W ⊆ CoveringSupport.admissible C R ∧
      GeneralCoveringInitializerPass.Covers C (demands G C D R L Q I Bdy) W ∧
      (∑ v ∈ W, c v) ≤ 2 * (B : ℝ) * k :=
  local_benchmark G C D R L B k Q I Bdy (P.size I hI) hcover hD hlocal c hc

/-- Specialize to the literal accepted initializer's D0. The only remaining
part/interior data are proof-side geometry, not executable oracle inputs. -/
theorem initialized_benchmark (C : V → Finset V) (b h f T L B k : ℕ) (hb : 1 ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, C r ⊆ closed G r) (hrows : ∀ r ∈ R, (C r).Nonempty)
    (c : V → ℝ) (hc : ∀ v ∈ CoveringSupport.admissible C R, 1 ≤ c v ∧ c v ≤ B) :
    let D := GeneralCoveringInitializerRun.selected C b h f R T
    ∀ (Q : Finset D) (I Bdy : Finset (Low D Q)), I.card ≤ k →
      ∃ W : Finset V, W ⊆ vertices G C D R L Q I ∧ W ⊆ CoveringSupport.admissible C R ∧
        GeneralCoveringInitializerPass.Covers C (demands G C D R L Q I Bdy) W ∧
        (∑ v ∈ W, c v) ≤ 2 * (B : ℝ) * k := by
  dsimp only
  intro Q I Bdy hsize
  exact local_benchmark G C (GeneralCoveringInitializerRun.selected C b h f R T) R L B k Q I Bdy hsize
    (GeneralCoveringInitializerRun.selected_covers C b h f R T hrows)
    (GeneralCoveringInitializerRun.selected_admissible C b h f hb R T) hlocal c hc

end Paper.GeneralCoveringTaskGeometry

#print axioms Paper.GeneralCoveringTaskGeometry.mem_lightSupport
#print axioms Paper.GeneralCoveringTaskGeometry.lightSupport_bound
#print axioms Paper.GeneralCoveringTaskGeometry.lightSupport_labels
#print axioms Paper.GeneralCoveringTaskGeometry.served_owner
#print axioms Paper.GeneralCoveringTaskGeometry.service_light
#print axioms Paper.GeneralCoveringTaskGeometry.demands_in_vertices
#print axioms Paper.GeneralCoveringTaskGeometry.service_in_vertices
#print axioms Paper.GeneralCoveringTaskGeometry.rows_in_vertices
#print axioms Paper.GeneralCoveringTaskGeometry.service_disjoint
#print axioms Paper.GeneralCoveringTaskGeometry.partner_in_vertices
#print axioms Paper.GeneralCoveringTaskGeometry.benchmark_in_vertices
#print axioms Paper.GeneralCoveringTaskGeometry.benchmark_covers
#print axioms Paper.GeneralCoveringTaskGeometry.benchmark_admissible
#print axioms Paper.GeneralCoveringTaskGeometry.benchmark_cost
#print axioms Paper.GeneralCoveringTaskGeometry.local_benchmark
#print axioms Paper.GeneralCoveringTaskGeometry.part_benchmark
#print axioms Paper.GeneralCoveringTaskGeometry.initialized_benchmark
