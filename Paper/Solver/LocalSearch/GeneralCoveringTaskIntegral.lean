import Paper.Solver.LocalSearch.GeneralCoveringNormalizedIntegral
import Paper.Solver.LocalSearch.GeneralCoveringTaskDiameter
import Paper.Preliminaries.MinorDensity

/-! One actual arbitrary-C owner task, with public diameter 4k and budget 2Bk.
The program is the received normalized integral program on private inputs.
Owner/part geometry certifies its context and a genuine trimmed benchmark.
Private active/demand masks and true forward/inverse incidence lists must
already encode the stated task. Computing those masks, computing the owner
partition/boundary and simultaneous execution of overlapping physical tasks
are separate requirements, not executable oracle inputs introduced here. -/
namespace Paper.GeneralCoveringTaskIntegral
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input

def program {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) Bool :=
  GeneralCoveringNormalizedIntegral.program ids (4 * k) a B (2 * B * k) hB

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program ids a B k hB).runEncoded G s =
      (GeneralCoveringIntegral.program ids (4 * k) a B (2 * B * k)).runEncoded G
        ((GeneralCoveringInputNormalization.program B hB).runEncoded G s) :=
  GeneralCoveringNormalizedIntegral.run_program G ids (4 * k) a B (2 * B * k) hB s

def output {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) : Finset V :=
  GeneralCoveringNormalizedIntegral.output G ids (4 * k) a B (2 * B * k) hB s

theorem mem_output {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    v ∈ output G ids a B k hB s ↔ (program ids a B k hB).runEncoded G s v = true :=
  GeneralCoveringNormalizedIntegral.mem_output G ids (4 * k) a B (2 * B * k) hB s v

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ)
    (Q : Finset D) : DecidableRel (graph G cover D R L Q).Adj :=
  fun _ _ => Classical.propDecidable _

/-- Proof-side witness: remove benchmark vertices unused by this task. -/
noncomputable def witness (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) : Finset V :=
  benchmark G cover D R L Q I ∩ service G cover D R L Q I Bdy

theorem witness_admissible (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) :
    witness G cover D R L Q I Bdy ⊆
      CoveringSupport.admissible cover (demands G cover D R L Q I Bdy) :=
  Finset.inter_subset_right

theorem witness_covers (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I Bdy : Finset (Low D Q)) (hcover : GeneralCoveringInitializerPass.Covers cover R D) :
    GeneralCoveringNormalizedIntegral.Covers cover (demands G cover D R L Q I Bdy)
      (witness G cover D R L Q I Bdy) := by
  intro r hr
  obtain ⟨v, hv, hvr⟩ := benchmark_covers G cover D R L Q I Bdy hcover r hr
  exact ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_biUnion.mpr ⟨r, hr, hvr⟩⟩, hvr⟩

/-- Explicit Nat-cost bridge from the genuine owner/partner benchmark. -/
theorem witness_cost (cover : V → Finset V) (D R : Finset V) (L B k : ℕ) (Q : Finset D)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (hD : D ⊆ CoveringSupport.admissible cover R) (c : V → Fin (B + 1))
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val) :
    (∑ v ∈ witness G cover D R L Q I Bdy, (c v).val) ≤ 2 * B * k := by
  have hbounds : ∀ v ∈ CoveringSupport.admissible cover R,
      (1 : ℝ) ≤ (c v).val ∧ ((c v).val : ℝ) ≤ B := by
    intro v hv
    constructor
    · exact_mod_cast hc v hv
    · have hh : (c v).val ≤ B := by have ht := (c v).isLt; omega
      exact_mod_cast hh
  have hreal := benchmark_cost G cover D R L B Q (fun v => ((c v).val : ℝ)) hD hbounds I
  have hnat : (∑ v ∈ benchmark G cover D R L Q I, (c v).val) ≤ 2 * B * I.card := by
    exact_mod_cast hreal
  calc
    _ ≤ ∑ v ∈ benchmark G cover D R L Q I, (c v).val :=
      Finset.sum_le_sum_of_subset Finset.inter_subset_left
    _ ≤ 2 * B * I.card := hnat
    _ ≤ 2 * B * k := Nat.mul_le_mul_left (2 * B) (P.size I hI)

/-- A genuine part supplies context, service support and feasible budget.
Bdy is proof-side data and may in particular be the actual partition boundary. -/
theorem part_spec (cover targets : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D)
    (hD : D ⊆ CoveringSupport.admissible cover R)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (a : ℕ) (ha' : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (hB : 1 ≤ B) (c : V → Fin (B + 1))
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val)
    {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (ha : ∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q I))
    (hcost : ∀ v, (s v).cost = c v)
    (hd : ∀ v, (s v).demand = decide (v ∈ demands G cover D R L Q I Bdy))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    output G ids a B k hB s ⊆ vertices G cover D R L Q I ∧
      output G ids a B k hB s ⊆ service G cover D R L Q I Bdy ∧
      GeneralCoveringNormalizedIntegral.Covers cover (demands G cover D R L Q I Bdy)
        (output G ids a B k hB s) ∧
      (∑ v ∈ output G ids a B k hB s, (c v).val) ≤ 2 * B * k ∧
      ∀ O : Finset V, O ⊆ service G cover D R L Q I Bdy →
        GeneralCoveringNormalizedIntegral.Covers cover (demands G cover D R L Q I Bdy) O →
          (∑ v ∈ output G ids a B k hB s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  let K := GeneralCoveringTaskDiameter.partContext G cover D R L Q hlocal k P I hI
  let T := demands G cover D R L Q I Bdy
  let Z := witness G cover D R L Q I Bdy
  have hT : T ⊆ K.vertices := demands_in_vertices G cover D R L Q I Bdy
  have hTlocal : ∀ r ∈ T, cover r ⊆ closed G r := by
    intro r hr
    exact hlocal r (demands_subset G cover D R L Q I Bdy hr)
  have hTrows : ∀ r ∈ T, cover r ⊆ K.vertices := rows_in_vertices G cover D R L Q I Bdy hlocal
  have hTc : ∀ v ∈ CoveringSupport.admissible cover T, 1 ≤ (c v).val := by
    intro v hv
    exact hc v (service_light G cover D R L Q I Bdy hv).1
  have hZcost : (∑ v ∈ Z, (c v).val) ≤ 2 * B * k :=
    witness_cost G cover D R L B k Q P I Bdy hI hD c hc
  have hs := GeneralCoveringNormalizedIntegral.optimal G K T hT cover targets hinc hTlocal hTrows
    a ha' (MinorDensity.induced_bound G hden) B (2 * B * k) hB c hTc ids s ha hcost hd hC ht
    Z (witness_admissible G cover D R L Q I Bdy) (witness_covers G cover D R L Q I Bdy hcover) hZcost
  have hdiam : K.diameter = 4 * k := rfl
  rw [hdiam] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, hs.2.2.2⟩
  exact (hs.2.2.2 Z (witness_admissible G cover D R L Q I Bdy)
    (witness_covers G cover D R L Q I Bdy hcover)).trans hZcost

/-- A nonempty part may have no residual demands. Its derived context remains valid. -/
theorem empty_demand (cover targets : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (hT : demands G cover D R L Q I Bdy = ∅)
    (a : ℕ) (ha' : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B : ℕ) (hB : 1 ≤ B) {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (ha : ∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q I))
    (hd : ∀ v, (s v).demand = decide (v ∈ demands G cover D R L Q I Bdy))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    output G ids a B k hB s = ∅ ∧ ∀ v, (program ids a B k hB).runEncoded G s v = false := by
  let K := GeneralCoveringTaskDiameter.partContext G cover D R L Q hlocal k P I hI
  have hfalse : ∀ v, (s v).demand = false := by
    intro v
    rw [hd v, hT]
    rfl
  exact GeneralCoveringNormalizedIntegral.empty_demand G K cover targets hinc a ha'
    (MinorDensity.induced_bound G hden) B (2 * B * k) hB ids s ha hfalse hC ht

/-- All-inactive input is handled directly by the actual finishing program,
without manufacturing a nonempty ActiveTask.Context. -/
theorem all_inactive {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (ha : ∀ v, (s v).active = false) :
    output G ids a B k hB s = ∅ ∧ ∀ v, (program ids a B k hB).runEncoded G s v = false := by
  have hfalse : ∀ v, (program ids a B k hB).runEncoded G s v = false := by
    intro v
    rw [run_program, Program.runEncoded_eq_run]
    change decide (0 < ((GeneralCoveringFractional.program ids (4 * k) a B 1 (2 * B * k)).run G
      ((GeneralCoveringInputNormalization.program B hB).runEncoded G s) v).val) = false
    rw [GeneralCoveringFractional.run_program,
      (GeneralCoveringInputNormalization.metadata G B hB s v).1, ha v]
    rfl
  refine ⟨Finset.eq_empty_iff_forall_notMem.mpr ?_, hfalse⟩
  intro v hv
  have hh := (mem_output G ids a B k hB s v).mp hv
  simp only [hfalse v, Bool.false_eq_true] at hh

theorem empty_part (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (Bdy : Finset (Low D Q)) {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q ∅)) :
    vertices G cover D R L Q ∅ = ∅ ∧ demands G cover D R L Q ∅ Bdy = ∅ ∧
      output G ids a B k hB s = ∅ ∧ ∀ v, (program ids a B k hB).runEncoded G s v = false := by
  have he := GeneralCoveringTaskDiameter.empty_part G cover D R L Q
  have ha' : ∀ v, (s v).active = false := by
    intro v
    rw [ha v, he.1]
    rfl
  exact ⟨he.1, he.2 Bdy, all_inactive G ids a B k hB s ha'⟩

theorem rounds {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B) :
    (program ids a B k hB).rounds = RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 1 :=
  GeneralCoveringNormalizedIntegral.rounds ids (4 * k) a B (2 * B * k) hB

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B) :
    (program ids a B k hB).maxBits ≤ max 1 (3 * bits + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k)) :=
  GeneralCoveringNormalizedIntegral.maxBits ids (4 * k) a B (2 * B * k) hB

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B) :
    (program ids a B k hB).maxBits =
      max 1 (GeneralCoveringIntegral.program ids (4 * k) a B (2 * B * k)).maxBits :=
  GeneralCoveringNormalizedIntegral.maxBits_eq ids (4 * k) a B (2 * B * k) hB

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program ids a B k hB).maxBits ≤
      (3 * c + RecursiveSearch.extraBits (4 * k) a B 1 (2 * B * k) + 1) * Nat.clog 2 (n + 2) :=
  GeneralCoveringNormalizedIntegral.logarithmic_bits ids (4 * k) a B (2 * B * k) hB n c hids

theorem locality {bits : ℕ} (ids : BitCode V bits) (a B k : ℕ) (hB : 1 ≤ B)
    (N N' : V → Finset V) (s s' : V → Input V B) (v : V)
    (hn : ∀ u ∈ NeighborBalls.ball N v (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 1), N u = N' u)
    (hs : ∀ u ∈ NeighborBalls.ball N v (RecursiveSearch.roundBound (4 * k) a (2 * B * k) + 1), s u = s' u) :
    NeighborInterpreter.run N (program ids a B k hB) s v =
      NeighborInterpreter.run N' (program ids a B k hB) s' v :=
  GeneralCoveringNormalizedIntegral.locality ids (4 * k) a B (2 * B * k) hB N N' s s' v hn hs
end Paper.GeneralCoveringTaskIntegral

#print axioms Paper.GeneralCoveringTaskIntegral.run_program
#print axioms Paper.GeneralCoveringTaskIntegral.witness_admissible
#print axioms Paper.GeneralCoveringTaskIntegral.witness_covers
#print axioms Paper.GeneralCoveringTaskIntegral.witness_cost
#print axioms Paper.GeneralCoveringTaskIntegral.part_spec
#print axioms Paper.GeneralCoveringTaskIntegral.empty_demand
#print axioms Paper.GeneralCoveringTaskIntegral.all_inactive
#print axioms Paper.GeneralCoveringTaskIntegral.empty_part
#print axioms Paper.GeneralCoveringTaskIntegral.rounds
#print axioms Paper.GeneralCoveringTaskIntegral.maxBits
#print axioms Paper.GeneralCoveringTaskIntegral.maxBits_eq
#print axioms Paper.GeneralCoveringTaskIntegral.logarithmic_bits
#print axioms Paper.GeneralCoveringTaskIntegral.locality
