import Paper.Solver.LocalSearch.GeneralCoveringInputNormalization
import Paper.Solver.LocalSearch.GeneralCoveringFractionalCorrect

/-! Literal normalization followed by the frozen arbitrary-C fractional
solver. Original costs need be positive only on original admissible vertices,
and original rows local only on R. Supported LP values are preserved exactly,
so the relative guarantee concerns the ORIGINAL LP. Active Context and genuine
K0 budget remain proof-side hypotheses; no optimum/orientation enters code. -/
namespace Paper.GeneralCoveringNormalizedFractional
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input

/-- Only public codec/natural parameters and private original input. -/
def program {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) (Fin (M + 1)) :=
  .seq (GeneralCoveringInputNormalization.program B hB)
    (GeneralCoveringFractional.program ids diam a B q M)

variable [Fintype V]

/-- The original LP restricts support to the actual union of demanded rows. -/
noncomputable def supportedValues (cover : V → Finset V) (R : Finset V) (c : V → ℝ) : Set ℝ :=
  {t | ∃ x, CoveringOptimum.Feasible cover R x ∧
    (∀ v, v ∉ CoveringSupport.admissible cover R → x v = 0) ∧ CoveringOptimum.objective c x = t}

noncomputable def supportedNumber (cover : V → Finset V) (R : Finset V) (c : V → ℝ) : ℝ :=
  sInf (supportedValues cover R c)

theorem number_le_objective (cover : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hc : ∀ v, 0 ≤ c v) (x : V → ℝ) (hx : CoveringOptimum.Feasible cover R x) :
    CoveringOptimum.number cover R c ≤ CoveringOptimum.objective c x := by
  unfold CoveringOptimum.number
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro t ⟨y, hy, rfl⟩
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (hc v) (hy.1 v))
  · exact ⟨x, hx, rfl⟩

/-- The optimum vector is obtained inside this proof, never assumed. -/
theorem supportedNumber_eq_number (cover : V → Finset V) (R : Finset V) (c : V → ℝ)
    (hrows : ∀ r ∈ R, (cover r).Nonempty) (hc : ∀ v, 0 ≤ c v) :
    supportedNumber cover R c = CoveringOptimum.number cover R c := by
  obtain ⟨x, hx, _, hs, he⟩ := CoveringSupport.exists_supported_optimum cover R c hrows hc
  have hl : IsLeast (supportedValues cover R c) (CoveringOptimum.number cover R c) := by
    refine ⟨⟨x, hx, hs, he⟩, ?_⟩
    rintro t ⟨y, hy, _, rfl⟩
    exact number_le_objective cover R c hc y hy
  exact hl.csInf_eq

/-- A real original supported feasible benchmark certifies the public K0;
no benchmark is passed to the executable or required to be optimal. -/
theorem budget_bound (cover : V → Finset V) (R : Finset V) {B : ℕ} (c : V → Fin (B + 1))
    (hrows : ∀ r ∈ R, (cover r).Nonempty) (y : V → ℝ)
    (hy : SevenFoundation.feasible (GeneralCoveringFractionalCorrect.coverInstance R cover c) y)
    (K0 : ℝ) (hcost : SevenFoundation.cost (GeneralCoveringFractionalCorrect.coverInstance R cover c) y ≤ K0) :
    supportedNumber cover R (fun v => ((c v).val : ℝ)) ≤ K0 := by
  rw [supportedNumber_eq_number cover R _ hrows (fun v => Nat.cast_nonneg _)]
  exact (number_le_objective cover R _ (fun v => Nat.cast_nonneg _) y ⟨hy.1, hy.2.2⟩).trans hcost

/-- No demand gives precisely the zero supported objective, for arbitrary costs. -/
theorem supportedValues_empty (cover : V → Finset V) (c : V → ℝ) :
    supportedValues cover ∅ c = {0} := by
  ext t
  constructor
  · rintro ⟨x, _, hs, rfl⟩
    have hz : x = fun _ => 0 := funext (fun v => hs v (by simp [CoveringSupport.admissible]))
    simp [CoveringOptimum.objective, hz]
  · intro ht
    have he : t = 0 := Set.mem_singleton_iff.mp ht
    subst t
    refine ⟨fun _ => 0, ⟨fun _ => le_rfl, ?_⟩, fun _ _ => rfl, ?_⟩
    · simp
    · simp [CoveringOptimum.objective]

theorem supportedNumber_empty (cover : V → Finset V) (c : V → ℝ) :
    supportedNumber cover ∅ c = 0 := by
  have hl : IsLeast (supportedValues cover ∅ c) 0 := by
    rw [supportedValues_empty]
    refine ⟨by simp only [Set.mem_singleton_iff], ?_⟩
    intro t ht
    exact le_of_eq (Set.mem_singleton_iff.mp ht).symm
  exact hl.csInf_eq

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def normalized (B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) : V → Input V B :=
  (GeneralCoveringInputNormalization.program B hB).runEncoded G s

def normalizedCover (B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) (r : V) : Finset V :=
  (normalized G B hB s r).candidates

def normalizedCost (B : ℕ) (hB : 1 ≤ B) (s : V → Input V B) (v : V) : Fin (B + 1) :=
  (normalized G B hB s v).cost

theorem run_program {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program ids diam a B q M hB).runEncoded G s =
      (GeneralCoveringFractional.program ids diam a B q M).runEncoded G (normalized G B hB s) := rfl

theorem rows_eq (cover : V → Finset V) (R : Finset V) {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (hC : ∀ v, (s v).candidates = cover v)
    {r : V} (hr : r ∈ R) : normalizedCover G B hB s r = cover r :=
  (GeneralCoveringInputNormalization.candidates_eq G cover R hB s hd hC r).trans (if_pos hr)

theorem feasible_iff (cover : V → Finset V) (R : Finset V) {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (hC : ∀ v, (s v).candidates = cover v) (x : V → ℝ) :
    CoveringOptimum.Feasible (normalizedCover G B hB s) R x ↔ CoveringOptimum.Feasible cover R x := by
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨hn, ?_⟩
    intro r hr
    simpa only [rows_eq G cover R hB s hd hC hr] using hf r hr
  · rintro ⟨hn, hf⟩
    refine ⟨hn, ?_⟩
    intro r hr
    simpa only [rows_eq G cover R hB s hd hC hr] using hf r hr

theorem admissible_eq (cover : V → Finset V) (R : Finset V) {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (hC : ∀ v, (s v).candidates = cover v) :
    CoveringSupport.admissible (normalizedCover G B hB s) R = CoveringSupport.admissible cover R :=
  GeneralCoveringInputNormalization.admissibility G cover R hB s hd hC

theorem objective_eq (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B) (c : V → Fin (B + 1))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (ht : ∀ v, (s v).targets = targets v) (x : V → ℝ)
    (hs : ∀ v, v ∉ CoveringSupport.admissible cover R → x v = 0) :
    CoveringOptimum.objective (fun v => ((normalizedCost G B hB s v).val : ℝ)) x =
      CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x := by
  change (∑ v, ((normalized G B hB s v).cost.val : ℝ) * x v) = ∑ v, ((c v).val : ℝ) * x v
  simpa only [normalized, hc] using
    GeneralCoveringInputNormalization.supported_objective G cover targets R hinc hlocal s hd ht hB x hs

/-- Supported feasible sets and objective VALUES agree, even when original
zero-demand rows are nonlocal and inadmissible costs are zero. -/
theorem supportedValues_eq (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B) (c : V → Fin (B + 1))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    supportedValues (normalizedCover G B hB s) R (fun v => ((normalizedCost G B hB s v).val : ℝ)) =
      supportedValues cover R (fun v => ((c v).val : ℝ)) := by
  have hadm := admissible_eq G cover R hB s hd hC
  ext t
  constructor
  · rintro ⟨x, hx, hs, he⟩
    have hs' : ∀ v, v ∉ CoveringSupport.admissible cover R → x v = 0 := by
      rw [← hadm]
      exact hs
    exact ⟨x, (feasible_iff G cover R hB s hd hC x).mp hx, hs',
      (objective_eq G cover targets R hinc hlocal hB s c hc hd ht x hs').symm.trans he⟩
  · rintro ⟨x, hx, hs, he⟩
    have hs' : ∀ v, v ∉ CoveringSupport.admissible (normalizedCover G B hB s) R → x v = 0 := by
      rw [hadm]
      exact hs
    exact ⟨x, (feasible_iff G cover R hB s hd hC x).mpr hx, hs',
      (objective_eq G cover targets R hinc hlocal hB s c hc hd ht x hs).trans he⟩

theorem supportedNumber_eq (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B) (c : V → Fin (B + 1))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    supportedNumber (normalizedCover G B hB s) R (fun v => ((normalizedCost G B hB s v).val : ℝ)) =
      supportedNumber cover R (fun v => ((c v).val : ℝ)) := by
  unfold supportedNumber
  rw [supportedValues_eq G cover targets R hinc hlocal hB s c hc hd hC ht]

/-- The frozen core's unrestricted normalized number equals the ORIGINAL
supported LP. Dummy inadmissible costs never change the optimum. -/
theorem normalized_number (cover targets : V → Finset V) (R : Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r) (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (hrows : ∀ r ∈ R, (cover r).Nonempty) {B : ℕ} (hB : 1 ≤ B) (s : V → Input V B) (c : V → Fin (B + 1))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    CoveringOptimum.number (normalizedCover G B hB s) R (fun v => ((normalizedCost G B hB s v).val : ℝ)) =
      supportedNumber cover R (fun v => ((c v).val : ℝ)) := by
  have hnrows : ∀ r ∈ R, (normalizedCover G B hB s r).Nonempty := by
    intro r hr
    rw [rows_eq G cover R hB s hd hC hr]
    exact hrows r hr
  calc
    _ = supportedNumber (normalizedCover G B hB s) R (fun v => ((normalizedCost G B hB s v).val : ℝ)) :=
      (supportedNumber_eq_number _ R _ hnrows (fun v => Nat.cast_nonneg _)).symm
    _ = _ := supportedNumber_eq G cover targets R hinc hlocal hB s c hc hd hC ht

/-- Relative approximation for ORIGINAL supported LP, with own natural
numerator and fixed public q. K and the original K0 inequality are explicit;
normalization derives global positive dummy costs only for the frozen core. -/
theorem spec (K : ActiveTask.Context G) (R : Finset V) (hR : R ⊆ K.vertices)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (htask : ∀ r ∈ R, cover r ⊆ K.vertices) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (c : V → Fin (B + 1))
    (hpositive : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val)
    (K0 ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hK0 : supportedNumber cover R (fun v => ((c v).val : ℝ)) ≤ K0)
    {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices)) (hc : ∀ v, (s v).cost = c v)
    (hd : ∀ v, (s v).demand = decide (v ∈ R)) (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v) :
    let M := ⌈(q + 2 * (a : ℝ)) * K0⌉₊
    let p := fun v => ((program ids K.diameter a B q M hB).runEncoded G s v).val
    let x := fun v => (p v : ℝ) / q
    CoveringOptimum.Feasible cover R x ∧
    CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
      (1 + ξ) * supportedNumber cover R (fun v => ((c v).val : ℝ)) ∧
    (∀ v, (q : ℝ) * x v = p v) ∧
    (∀ v, v ∉ CoveringSupport.admissible cover R → p v = 0) ∧
    SevenFoundation.approximates (GeneralCoveringFractionalCorrect.coverInstance R cover c) (1 + ξ) x := by
  dsimp only
  let M := ⌈(q + 2 * (a : ℝ)) * K0⌉₊
  let ns := normalized G B hB s
  let rows := normalizedCover G B hB s
  let inverse := fun v => (ns v).targets
  let nc := normalizedCost G B hB s
  let out := (program ids K.diameter a B q M hB).runEncoded G s
  let p := fun v => (out v).val
  let x := fun v => (p v : ℝ) / q
  have hninc : ∀ v r, r ∈ inverse v ↔ v ∈ rows r :=
    GeneralCoveringInputNormalization.agreement G cover targets R hinc hlocal hB s hd hC ht
  have hnclosed : ∀ r, rows r ⊆ closed G r :=
    GeneralCoveringInputNormalization.locality G cover R hlocal hB s hd hC
  have hntask : ∀ r ∈ R, rows r ⊆ K.vertices := by
    intro r hr
    change normalizedCover G B hB s r ⊆ K.vertices
    rw [rows_eq G cover R hB s hd hC hr]
    exact htask r hr
  have hnrows : ∀ r ∈ R, (rows r).Nonempty := by
    intro r hr
    change (normalizedCover G B hB s r).Nonempty
    rw [rows_eq G cover R hB s hd hC hr]
    exact hrows r hr
  have hnpositive : ∀ v, 1 ≤ (nc v).val :=
    GeneralCoveringInputNormalization.positive G cover targets R hinc hlocal s hd ht hB
      (fun v hv => by rw [hc v]; exact hpositive v hv)
  have hnactive (v : V) : (ns v).active = decide (v ∈ K.vertices) :=
    (GeneralCoveringInputNormalization.metadata G B hB s v).1.trans (ha v)
  have hndemand (v : V) : (ns v).demand = decide (v ∈ R) :=
    (GeneralCoveringInputNormalization.metadata G B hB s v).2.trans (hd v)
  have hadm : CoveringSupport.admissible rows R = CoveringSupport.admissible cover R :=
    admissible_eq G cover R hB s hd hC
  have htau : CoveringOptimum.number rows R (fun v => ((nc v).val : ℝ)) =
      supportedNumber cover R (fun v => ((c v).val : ℝ)) :=
    normalized_number G cover targets R hinc hlocal hrows hB s c hc hd hC ht
  have hKn : CoveringOptimum.number rows R (fun v => ((nc v).val : ℝ)) ≤ K0 := by
    rw [htau]
    exact hK0
  have hrun : out = (GeneralCoveringFractional.program ids K.diameter a B q M).run G ns :=
    (run_program G ids K.diameter a B q M hB s).trans (Program.runEncoded_eq_run G _ ns)
  have hcore := GeneralCoveringFractionalCorrect.spec G K R hR rows inverse hninc hnclosed hntask hnrows
    a ha' hden B q hq nc hnpositive K0 ξ haccuracy hKn ids ns hnactive (fun _ => rfl) hndemand
      (fun _ => rfl) (fun _ => rfl)
  dsimp only at hcore
  rw [← hrun] at hcore
  change CoveringOptimum.Feasible rows R x ∧
    CoveringOptimum.objective (fun v => ((nc v).val : ℝ)) x ≤
      (1 + ξ) * CoveringOptimum.number rows R (fun v => ((nc v).val : ℝ)) ∧
    (∀ v, (q : ℝ) * x v = p v) ∧ (∀ v, v ∉ CoveringSupport.admissible rows R → p v = 0) at hcore
  have hpsupport (v : V) (hv : v ∉ CoveringSupport.admissible cover R) : p v = 0 :=
    hcore.2.2.2 v (by rwa [hadm])
  have hxsupport (v : V) (hv : v ∉ CoveringSupport.admissible cover R) : x v = 0 := by
    change (p v : ℝ) / q = 0
    rw [hpsupport v hv]
    simp only [Nat.cast_zero, zero_div]
  have hfeasible : CoveringOptimum.Feasible cover R x := (feasible_iff G cover R hB s hd hC x).mp hcore.1
  have hobj := objective_eq G cover targets R hinc hlocal hB s c hc hd ht x hxsupport
  have hcost : CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
      (1 + ξ) * supportedNumber cover R (fun v => ((c v).val : ℝ)) := by
    calc
      _ = CoveringOptimum.objective (fun v => ((nc v).val : ℝ)) x := hobj.symm
      _ ≤ (1 + ξ) * CoveringOptimum.number rows R (fun v => ((nc v).val : ℝ)) := hcore.2.1
      _ = _ := congrArg (fun t : ℝ => (1 + ξ) * t) htau
  have hcn : ∀ v, (0 : ℝ) ≤ (c v).val := fun v => Nat.cast_nonneg _
  have hfactor : 0 ≤ 1 + ξ := by
    have hnonneg : (0 : ℝ) ≤ 2 * (a : ℝ) / q := div_nonneg (by positivity) (Nat.cast_nonneg q)
    have hxi : 0 ≤ ξ := hnonneg.trans haccuracy
    linarith
  refine ⟨hfeasible, hcost, hcore.2.2.1, hpsupport, ?_⟩
  refine ⟨GeneralCoveringFractionalCorrect.instance_feasible R cover c x hfeasible hxsupport, ?_⟩
  intro y hy
  change CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
    (1 + ξ) * CoveringOptimum.objective (fun v => ((c v).val : ℝ)) y
  have hmin : supportedNumber cover R (fun v => ((c v).val : ℝ)) ≤
      CoveringOptimum.objective (fun v => ((c v).val : ℝ)) y := by
    rw [supportedNumber_eq_number cover R _ hrows hcn]
    exact number_le_objective cover R _ hcn y ⟨hy.1, hy.2.2⟩
  exact hcost.trans (mul_le_mul_of_nonneg_left hmin hfactor)

/-- Empty original demand uses no original cost-positivity or locality
assumption. K is still a genuine nonempty active Context required by the
frozen solver; no nonempty demand or default vertex is inferred. -/
theorem empty_demand (K : ActiveTask.Context G) (cover targets : V → Finset V)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B q : ℕ) (hB : 1 ≤ B) (hq : 1 ≤ q) (K0 ξ : ℝ)
    (haccuracy : 2 * (a : ℝ) / q ≤ ξ) (hK0 : 0 ≤ K0)
    {bits : ℕ} (ids : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hd : ∀ v, (s v).demand = false) (hC : ∀ v, (s v).candidates = cover v)
    (ht : ∀ v, (s v).targets = targets v) :
    let M := ⌈(q + 2 * (a : ℝ)) * K0⌉₊
    ∀ v, ((program ids K.diameter a B q M hB).runEncoded G s v).val = 0 := by
  have hd' : ∀ v, (s v).demand = decide (v ∈ (∅ : Finset V)) := by
    intro v
    simpa using hd v
  have hb : supportedNumber cover ∅ (fun v => ((s v).cost.val : ℝ)) ≤ K0 := by
    rw [supportedNumber_empty]
    exact hK0
  have h := spec G K ∅ (by simp) cover targets hinc (by simp) (by simp) (by simp)
    a ha' hden B q hB hq (fun v => (s v).cost) (by simp [CoveringSupport.admissible])
    K0 ξ haccuracy hb ids s ha (fun _ => rfl) hd' hC ht
  dsimp only at h ⊢
  intro v
  exact h.2.2.2.1 v (by simp [CoveringSupport.admissible])

theorem rounds_eq {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B) :
    (program ids diam a B q M hB).rounds = (GeneralCoveringFractional.program ids diam a B q M).rounds + 1 := by
  change 1 + (GeneralCoveringFractional.program ids diam a B q M).rounds = _
  exact Nat.add_comm _ _

theorem rounds {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B) :
    (program ids diam a B q M hB).rounds = RecursiveSearch.roundBound diam a M + 1 := by
  rw [rounds_eq, GeneralCoveringFractional.rounds]

theorem maxBits_eq {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B) :
    (program ids diam a B q M hB).maxBits = max 1 (GeneralCoveringFractional.program ids diam a B q M).maxBits := rfl

theorem maxBits {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B) :
    (program ids diam a B q M hB).maxBits ≤ max 1 (3 * bits + RecursiveSearch.extraBits diam a B q M) := by
  rw [maxBits_eq]
  exact max_le_max le_rfl (GeneralCoveringFractional.maxBits ids diam a B q M)

theorem logarithmic_bits {bits : ℕ} (ids : BitCode V bits) (diam a B q M : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program ids diam a B q M hB).maxBits ≤
      (3 * c + RecursiveSearch.extraBits diam a B q M + 1) * Nat.clog 2 (n + 2) := by
  have hlog : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hcoef : 1 ≤ 3 * c + RecursiveSearch.extraBits diam a B q M + 1 := by omega
  have hold := GeneralCoveringFractional.logarithmic_bits ids diam a B q M n c hids
  rw [maxBits_eq]
  apply max_le
  · exact Nat.mul_le_mul hcoef hlog
  · exact hold.trans (Nat.mul_le_mul (Nat.le_succ _) le_rfl)

end Paper.GeneralCoveringNormalizedFractional

#print axioms Paper.GeneralCoveringNormalizedFractional.number_le_objective
#print axioms Paper.GeneralCoveringNormalizedFractional.supportedNumber_eq_number
#print axioms Paper.GeneralCoveringNormalizedFractional.budget_bound
#print axioms Paper.GeneralCoveringNormalizedFractional.supportedValues_empty
#print axioms Paper.GeneralCoveringNormalizedFractional.supportedNumber_empty
#print axioms Paper.GeneralCoveringNormalizedFractional.run_program
#print axioms Paper.GeneralCoveringNormalizedFractional.rows_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.feasible_iff
#print axioms Paper.GeneralCoveringNormalizedFractional.admissible_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.objective_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.supportedValues_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.supportedNumber_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.normalized_number
#print axioms Paper.GeneralCoveringNormalizedFractional.spec
#print axioms Paper.GeneralCoveringNormalizedFractional.empty_demand
#print axioms Paper.GeneralCoveringNormalizedFractional.rounds_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.rounds
#print axioms Paper.GeneralCoveringNormalizedFractional.maxBits_eq
#print axioms Paper.GeneralCoveringNormalizedFractional.maxBits
#print axioms Paper.GeneralCoveringNormalizedFractional.logarithmic_bits
