import Paper.Solver.LocalSearch.GeneralCoveringNormalizedFractional
import Paper.Solver.LocalSearch.GeneralCoveringTaskDiameter
import Paper.Solver.LocalSearch.GeneralCoveringTaskFractional
import Paper.Preliminaries.MinorDensity

/-! Literal normalized fractional execution for one actual arbitrary-C owner
task. Public diameter is 4k and public numerator bound is (q+2a)*2Bk.
The accepted owner/partner benchmark derives the LP budget; the accepted
physical geometry derives the Context. Private masks and incidence lists
must already interpret the stated task. Producing those masks/partitions
and parallel execution remain separate gates, not runtime oracle inputs. -/
namespace Paper.GeneralCoveringTaskFractionalSolve
open BroadcastModel SevenFoundation GeneralCoveringTaskGeometry
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input

/-- Exact natural bound, computed only from public parameters. -/
def numeratorBound (a B k q : ℕ) : ℕ := (q + 2 * a) * (2 * B * k)

def program {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Fin (numeratorBound a B k q + 1)) :=
  GeneralCoveringNormalizedFractional.program ids (4 * k) a B q (numeratorBound a B k q) hB

theorem ceil_budget (a B k q : ℕ) :
    ⌈(q + 2 * (a : ℝ)) * (2 * (B : ℝ) * k)⌉₊ = numeratorBound a B k q := by
  have he : (q + 2 * (a : ℝ)) * (2 * (B : ℝ) * k) = (numeratorBound a B k q : ℝ) := by
    simp only [numeratorBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [he, Nat.ceil_natCast]

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program ids a B k q hB).runEncoded G s =
      (GeneralCoveringFractional.program ids (4 * k) a B q (numeratorBound a B k q)).runEncoded G
        (GeneralCoveringNormalizedFractional.normalized G B hB s) :=
  GeneralCoveringNormalizedFractional.run_program G ids (4 * k) a B q (numeratorBound a B k q) hB s

theorem numerator_le {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    ((program ids a B k q hB).runEncoded G s v).val ≤ numeratorBound a B k q :=
  Nat.le_of_lt_succ ((program ids a B k q hB).runEncoded G s v).isLt

noncomputable local instance ownerAdj (cover : V → Finset V) (D R : Finset V) (L : ℕ)
    (Q : Finset D) : DecidableRel (graph G cover D R L Q).Adj :=
  fun _ _ => Classical.propDecidable _

/-- No nonempty-row oracle is needed: the genuine initializer cover supplies it. -/
theorem rows_nonempty (cover : V → Finset V) (D R : Finset V)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D) : ∀ r ∈ R, (cover r).Nonempty := by
  intro r hr
  obtain ⟨v, _, hvr⟩ := hcover r hr
  exact ⟨v, hvr⟩

/-- The exact original supported task LP has the genuine owner/partner budget.
Neither an optimum vector nor a desired budget inequality is a premise. -/
theorem task_budget (cover : V → Finset V) (D R : Finset V) (L B k : ℕ) (Q : Finset D)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D)
    (hD : D ⊆ CoveringSupport.admissible cover R)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) (c : V → Fin (B + 1))
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val) :
    GeneralCoveringNormalizedFractional.supportedNumber cover (demands G cover D R L Q I Bdy)
      (fun v => ((c v).val : ℝ)) ≤ 2 * (B : ℝ) * k := by
  have hrows := rows_nonempty cover D R hcover
  have hTrows : ∀ r ∈ demands G cover D R L Q I Bdy, (cover r).Nonempty :=
    fun r hr => hrows r (demands_subset G cover D R L Q I Bdy hr)
  have hbounds : ∀ v ∈ CoveringSupport.admissible cover R,
      (1 : ℝ) ≤ (c v).val ∧ ((c v).val : ℝ) ≤ B := by
    intro v hv
    constructor
    · exact_mod_cast hc v hv
    · have hh : (c v).val ≤ B := by have ht := (c v).isLt; omega
      exact_mod_cast hh
  rw [GeneralCoveringNormalizedFractional.supportedNumber_eq_number cover _ _ hTrows
    (fun v => Nat.cast_nonneg _)]
  exact GeneralCoveringTaskFractional.local_number_bound G cover D R L B k Q P I Bdy hI
    hcover hD hlocal (fun v => ((c v).val : ℝ)) (fun v => Nat.cast_nonneg _) hbounds

/-- One proof-side owner part, with Context and budget DERIVED from actual-C
geometry. Forward/inverse lists are original cover lists; only demand bits
restrict rows to the exact task. No partition is an executable input. -/
theorem part_spec (cover targets : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hcover : GeneralCoveringInitializerPass.Covers cover R D)
    (hD : D ⊆ CoveringSupport.admissible cover R)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (a : ℕ) (ha' : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (c : V → Fin (B + 1))
    (hc : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val)
    (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (ha : ∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q I))
    (hcost : ∀ v, (s v).cost = c v)
    (hd : ∀ v, (s v).demand = decide (v ∈ demands G cover D R L Q I Bdy))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    let T := demands G cover D R L Q I Bdy
    let p := fun v => ((program ids a B k q hB).runEncoded G s v).val
    let x := fun v => (p v : ℝ) / q
    CoveringOptimum.Feasible cover T x ∧
      CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
        (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber cover T (fun v => ((c v).val : ℝ)) ∧
      (∀ v, (q : ℝ) * x v = p v) ∧
      (∀ v, v ∉ service G cover D R L Q I Bdy → p v = 0) ∧
      SevenFoundation.approximates (GeneralCoveringFractionalCorrect.coverInstance T cover c) (1 + ξ) x ∧
      (∀ v, v ∉ vertices G cover D R L Q I → p v = 0) := by
  let K := GeneralCoveringTaskDiameter.partContext G cover D R L Q hlocal k P I hI
  let T := demands G cover D R L Q I Bdy
  have hT : T ⊆ K.vertices := demands_in_vertices G cover D R L Q I Bdy
  have hTlocal : ∀ r ∈ T, cover r ⊆ closed G r := by
    intro r hr
    exact hlocal r (demands_subset G cover D R L Q I Bdy hr)
  have hTvertices : ∀ r ∈ T, cover r ⊆ K.vertices := rows_in_vertices G cover D R L Q I Bdy hlocal
  have hTrows : ∀ r ∈ T, (cover r).Nonempty :=
    fun r hr => rows_nonempty cover D R hcover r (demands_subset G cover D R L Q I Bdy hr)
  have hTc : ∀ v ∈ CoveringSupport.admissible cover T, 1 ≤ (c v).val := by
    intro v hv
    exact hc v (service_light G cover D R L Q I Bdy hv).1
  have hbudget := task_budget G cover D R L B k Q P I Bdy hI hcover hD hlocal c hc
  have hs := GeneralCoveringNormalizedFractional.spec G K T hT cover targets hinc hTlocal hTvertices hTrows
    a ha' (MinorDensity.induced_bound G hden) B q hB hq c hTc (2 * (B : ℝ) * k) ξ haccuracy hbudget
    ids s ha hcost hd hC ht
  have hdiam : K.diameter = 4 * k := rfl
  dsimp only at hs ⊢
  rw [hdiam, ceil_budget] at hs
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2, ?_⟩
  intro v hv
  exact hs.2.2.2.1 v (fun hsvc => hv (service_in_vertices G cover D R L Q I Bdy hlocal hsvc))

/-- Specialization to the accepted initializer's actual D0. All cover and
admissibility hypotheses for D are discharged by its frozen theorems. -/
theorem initialized_spec (cover targets : V → Finset V) (b h f t L : ℕ) (hb : 1 ≤ b)
    (R : Finset V) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (cover r).Nonempty) :
    let D := GeneralCoveringInitializerRun.selected cover b h f R t
    ∀ (Q : Finset D) (k : ℕ) (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
      (I Bdy : Finset (Low D Q)), I ∈ P.parts →
      ∀ (a : ℕ), 1 ≤ a → MinorDensity.Bound G (a : ℝ) →
      ∀ (B q : ℕ) (hB : 1 ≤ B), 1 ≤ q → ∀ (c : V → Fin (B + 1)),
      (∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val) →
      ∀ (ξ : ℝ), 2 * (a : ℝ) / q ≤ ξ →
      ∀ {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B),
      (∀ v r, r ∈ targets v ↔ v ∈ cover r) →
      (∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q I)) →
      (∀ v, (s v).cost = c v) →
      (∀ v, (s v).demand = decide (v ∈ demands G cover D R L Q I Bdy)) →
      (∀ v, (s v).candidates = cover v) → (∀ v, (s v).targets = targets v) →
      let T := demands G cover D R L Q I Bdy
      let p := fun v => ((program ids a B k q hB).runEncoded G s v).val
      let x := fun v => (p v : ℝ) / q
      CoveringOptimum.Feasible cover T x ∧
        CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
          (1 + ξ) * GeneralCoveringNormalizedFractional.supportedNumber cover T (fun v => ((c v).val : ℝ)) ∧
        (∀ v, (q : ℝ) * x v = p v) ∧
        (∀ v, v ∉ service G cover D R L Q I Bdy → p v = 0) ∧
        SevenFoundation.approximates (GeneralCoveringFractionalCorrect.coverInstance T cover c) (1 + ξ) x ∧
        (∀ v, v ∉ vertices G cover D R L Q I → p v = 0) := by
  dsimp only
  intro Q k P I Bdy hI a ha' hden B q hB hq c hc ξ haccuracy bits ids s hinc ha hcost hd hC ht
  exact part_spec G cover targets _ R L Q
    (GeneralCoveringInitializerRun.selected_covers cover b h f R t hrows)
    (GeneralCoveringInitializerRun.selected_admissible cover b h f hb R t) hlocal k P I Bdy hI
    a ha' hden B q hB hq c hc ξ haccuracy ids s hinc ha hcost hd hC ht

/-- A nonempty connected owner part can have empty demand. Its genuine
physical Context remains available, and every actual encoded numerator is zero. -/
theorem empty_demand (cover targets : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r) (k : ℕ)
    (P : SmallParts.Data (graph G cover D R L Q) Finset.univ k)
    (I Bdy : Finset (Low D Q)) (hI : I ∈ P.parts)
    (hT : demands G cover D R L Q I Bdy = ∅)
    (a : ℕ) (ha' : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (B q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (ha : ∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q I))
    (hd : ∀ v, (s v).demand = decide (v ∈ demands G cover D R L Q I Bdy))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    ∀ v, ((program ids a B k q hB).runEncoded G s v).val = 0 := by
  let K := GeneralCoveringTaskDiameter.partContext G cover D R L Q hlocal k P I hI
  have hfalse : ∀ v, (s v).demand = false := by
    intro v
    simpa [hT] using hd v
  have hz := GeneralCoveringNormalizedFractional.empty_demand G K cover targets hinc
    a ha' (MinorDensity.induced_bound G hden) B q hB hq (2 * (B : ℝ) * k) ξ haccuracy
    (by positivity) ids s ha hfalse hC ht
  have hdiam : K.diameter = 4 * k := rfl
  dsimp only at hz
  rw [hdiam, ceil_budget] at hz
  exact hz

/-- All-inactive input is handled by the real finishing step, with no
manufactured nonempty Context and no assumptions about incidence/cost/demand. -/
theorem all_inactive {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (ha : ∀ v, (s v).active = false) :
    ∀ v, ((program ids a B k q hB).runEncoded G s v).val = 0 := by
  intro v
  rw [run_program, Program.runEncoded_eq_run]
  unfold GeneralCoveringNormalizedFractional.normalized
  simp only [GeneralCoveringFractional.run_program,
    (GeneralCoveringInputNormalization.metadata G B hB s v).1, ha v,
    Bool.false_eq_true, ↓reduceIte, Fin.val_zero]

theorem empty_part (cover : V → Finset V) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (Bdy : Finset (Low D Q)) {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ vertices G cover D R L Q ∅)) :
    vertices G cover D R L Q ∅ = ∅ ∧ demands G cover D R L Q ∅ Bdy = ∅ ∧
      ∀ v, ((program ids a B k q hB).runEncoded G s v).val = 0 := by
  have he := GeneralCoveringTaskDiameter.empty_part G cover D R L Q
  have ha' : ∀ v, (s v).active = false := by
    intro v
    simpa [he.1] using ha v
  exact ⟨he.1, he.2 Bdy, all_inactive G ids a B k q hB s ha'⟩

theorem rounds {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids a B k q hB).rounds =
      RecursiveSearch.roundBound (4 * k) a (numeratorBound a B k q) + 1 :=
  GeneralCoveringNormalizedFractional.rounds ids (4 * k) a B q (numeratorBound a B k q) hB

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids a B k q hB).maxBits =
      max 1 (GeneralCoveringFractional.program ids (4 * k) a B q (numeratorBound a B k q)).maxBits :=
  GeneralCoveringNormalizedFractional.maxBits_eq ids (4 * k) a B q (numeratorBound a B k q) hB

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B) :
    (program ids a B k q hB).maxBits ≤
      max 1 (3 * bits + RecursiveSearch.extraBits (4 * k) a B q (numeratorBound a B k q)) :=
  GeneralCoveringNormalizedFractional.maxBits ids (4 * k) a B q (numeratorBound a B k q) hB

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (a B k q : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program ids a B k q hB).maxBits ≤
      (3 * c + RecursiveSearch.extraBits (4 * k) a B q (numeratorBound a B k q) + 1) * Nat.clog 2 (n + 2) :=
  GeneralCoveringNormalizedFractional.logarithmic_bits ids (4 * k) a B q (numeratorBound a B k q) hB n c hids
end Paper.GeneralCoveringTaskFractionalSolve

#print axioms Paper.GeneralCoveringTaskFractionalSolve.ceil_budget
#print axioms Paper.GeneralCoveringTaskFractionalSolve.run_program
#print axioms Paper.GeneralCoveringTaskFractionalSolve.numerator_le
#print axioms Paper.GeneralCoveringTaskFractionalSolve.rows_nonempty
#print axioms Paper.GeneralCoveringTaskFractionalSolve.task_budget
#print axioms Paper.GeneralCoveringTaskFractionalSolve.part_spec
#print axioms Paper.GeneralCoveringTaskFractionalSolve.initialized_spec
#print axioms Paper.GeneralCoveringTaskFractionalSolve.empty_demand
#print axioms Paper.GeneralCoveringTaskFractionalSolve.all_inactive
#print axioms Paper.GeneralCoveringTaskFractionalSolve.empty_part
#print axioms Paper.GeneralCoveringTaskFractionalSolve.rounds
#print axioms Paper.GeneralCoveringTaskFractionalSolve.maxBits_eq
#print axioms Paper.GeneralCoveringTaskFractionalSolve.maxBits
#print axioms Paper.GeneralCoveringTaskFractionalSolve.logarithmic_bits
