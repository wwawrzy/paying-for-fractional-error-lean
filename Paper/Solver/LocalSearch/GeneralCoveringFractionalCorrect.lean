import Paper.Solver.LocalSearch.GeneralCoveringFractional
import Paper.Certificates.Counting.CoveringCertificateOptimum

/-! Actual bounded-diameter fractional solver for arbitrary local covering
lists. The certificate and orientation are constructed only inside the proof. -/
namespace Paper.GeneralCoveringFractionalCorrect
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
/-- The paper's LP, with precisely the union of demanded covering lists
as its admissible coordinates. This is a proof-side instance, not program input. -/
noncomputable def coverInstance (R : Finset V) (cover : V → Finset V) {B : ℕ}
    (c : V → Fin (B + 1)) : CoverInstance V where
  demands := R
  candidates := CoveringSupport.admissible cover R
  eligible := cover
  eligible_subset := by
    intro r hr v hv
    exact Finset.mem_biUnion.mpr ⟨r, hr, hv⟩
  cost := fun v => ((c v).val : ℝ)
  cost_nonneg := fun _ => Nat.cast_nonneg _

theorem instance_feasible (R : Finset V) (cover : V → Finset V) {B : ℕ}
    (c : V → Fin (B + 1)) (x : V → ℝ) (hx : CoveringOptimum.Feasible cover R x)
    (hsupport : ∀ v, v ∉ CoveringSupport.admissible cover R → x v = 0) :
    feasible (coverInstance R cover c) x := ⟨hx.1, hsupport, hx.2⟩

theorem instance_cost (R : Finset V) (cover : V → Finset V) {B : ℕ}
    (c : V → Fin (B + 1)) (x : V → ℝ) :
    SevenFoundation.cost (coverInstance R cover c) x =
      CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x := rfl

variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 1000000 in
theorem spec (K : ActiveTask.Context G) (R : Finset V) (hR : R ⊆ K.vertices)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hclosed : ∀ r, cover r ⊆ closed G r)
    (htask : ∀ r ∈ R, cover r ⊆ K.vertices) (hrows : ∀ r ∈ R, (cover r).Nonempty)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B q : ℕ) (hq : 1 ≤ q) (c : V → Fin (B + 1)) (hpositive : ∀ v, 1 ≤ (c v).val)
    (K0 ξ : ℝ) (haccuracy : 2 * (a : ℝ) / q ≤ ξ)
    (hK0 : CoveringOptimum.number cover R (fun v => ((c v).val : ℝ)) ≤ K0)
    {bits : ℕ} (C : BitCode V bits) (s : V → GeneralCoveringFractional.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (htarget : ∀ v, (s v).targets = targets v) :
    let M := ⌈(q + 2 * (a : ℝ)) * K0⌉₊
    let p := fun v => ((GeneralCoveringFractional.program C K.diameter a B q M).run G s v).val
    let x := fun v => (p v : ℝ) / q
    CoveringOptimum.Feasible cover R x ∧
      CoveringOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
        (1 + ξ) * CoveringOptimum.number cover R (fun v => ((c v).val : ℝ)) ∧
      (∀ v, (q : ℝ) * x v = p v) ∧
      (∀ v, v ∉ CoveringSupport.admissible cover R → p v = 0) := by
  dsimp only
  let M := ⌈(q + 2 * (a : ℝ)) * K0⌉₊
  let b := TaskBenchmark.demand (q := q) R
  let input := fun v => GeneralCoveringFractional.searchInput q (s v)
  let solver := GeneralCoveringSearch.program C K.diameter a B q M
  have hai : ∀ v, (input v).base.active = decide (v ∈ K.vertices) := ha
  have hci : ∀ v, (input v).base.cost = c v := hc
  have hbi : ∀ v, (input v).base.value = b v := by
    intro v
    apply Fin.ext
    change (if (s v).demand then q else 0) = if v ∈ R then q else 0
    rw [hd v]
    by_cases hv : v ∈ R <;> simp [hv]
  have hz : ∀ v, v ∉ K.vertices → (b v).val = 0 := TaskBenchmark.demand_outside _ R hR
  have hspec := GeneralCoveringSearch.correct G K cover targets hinc
    (fun r _ => hclosed r) a ha' hden B q c C M b input hai hci hbi hz hC htarget
  obtain ⟨O⟩ := HallOrientation.exists_orientation_of_density G hden a le_rfl
  have hcn : ∀ v, 0 ≤ ((c v).val : ℝ) := fun v => Nat.cast_nonneg _
  obtain ⟨benchmark, hbenchcover, hbenchsupport, hbenchcost⟩ :=
    CoveringCertificateOptimum.exists_optimum_certificate G cover hclosed R hrows O ha' q
      (fun v => ((c v).val : ℝ)) hcn
  have hbenchsize : (∑ v, benchmark v) ≤ M := by
    have hcostsize := CoveringCertificate.copies_le_cost (fun v => ((c v).val : ℝ))
      (fun v => by
        change (1 : ℝ) ≤ ((c v).val : ℝ)
        exact_mod_cast (hpositive v)) benchmark
    have hbound : (∑ v, (benchmark v : ℝ)) ≤ M :=
      hcostsize.trans (hbenchcost.trans
        ((mul_le_mul_of_nonneg_left hK0 (by positivity)).trans (Nat.le_ceil _)))
    exact_mod_cast hbound
  have hsupport : ∀ v, v ∉ K.vertices → benchmark v = 0 := by
    intro v hv
    apply hbenchsupport v
    intro hadm
    obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.mp hadm
    exact hv (htask r hr hvr)
  have hcover : ∀ r, (b r).val ≤ ∑ v ∈ cover r, benchmark v := by
    intro r
    change (if r ∈ R then q else 0) ≤ _
    by_cases hr : r ∈ R
    · rw [if_pos hr]
      exact hbenchcover r hr
    · rw [if_neg hr]
      exact Nat.zero_le _
  obtain ⟨v0, hv0⟩ := K.nonempty
  obtain ⟨w, hw, hcostw⟩ := hspec.complete benchmark hbenchsize hsupport hcover v0 hv0
  have hvalid := hspec.sound v0 hv0 w hw
  have hrun : ∀ v ∈ K.vertices, solver.run G input v = some w :=
    fun v hv => (hspec.uniform v v0 hv hv0).trans hw
  have hcopies : ∀ v, ((GeneralCoveringFractional.program C K.diameter a B q M).run G s v).val =
      SolutionWord.copies w v := by
    intro v
    rw [GeneralCoveringFractional.run_program, ha v]
    by_cases hv : v ∈ K.vertices
    · simp only [decide_eq_true hv, ↓reduceIte]
      rw [hrun v hv]
      exact GeneralCoveringFractional.count_some w hvalid.1 v
    · have hzero := GeneralCoveringSpec.copies_support cover K.vertices c b M w hvalid v hv
      simp only [decide_eq_false hv, Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
      exact hzero.symm
  dsimp only [M] at hcopies
  simp_rw [hcopies]
  have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hcostreal : (SolutionWord.cost w : ℝ) ≤
      (q + 2 * (a : ℝ)) * CoveringOptimum.number cover R (fun v => ((c v).val : ℝ)) := by
    have hc' : (SolutionWord.cost w : ℝ) ≤
        ∑ v, ((c v).val : ℝ) * (benchmark v : ℝ) := by
      change SolutionWord.cost w ≤ ∑ v, (c v).val * benchmark v at hcostw
      exact_mod_cast hcostw
    exact hc'.trans hbenchcost
  have hnumber : 0 ≤ CoveringOptimum.number cover R (fun v => ((c v).val : ℝ)) := by
    obtain ⟨x, hx, he⟩ := CoveringOptimum.exists_optimum_eq_number cover R
      (fun v => ((c v).val : ℝ)) hrows hcn
    rw [← he]
    exact Finset.sum_nonneg (fun v _ => mul_nonneg (hcn v) (hx.1 v))
  refine ⟨⟨fun v => div_nonneg (Nat.cast_nonneg _) hqp.le, ?_⟩, ?_, ?_, ?_⟩
  · intro r hr
    have hh := hvalid.2.2.2 r
    change (if r ∈ R then q else 0) ≤ _ at hh
    rw [if_pos hr] at hh
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hqp).mpr
    simpa only [one_mul] using
      (show (q : ℝ) ≤ ∑ v ∈ cover r, (SolutionWord.copies w v : ℝ) by exact_mod_cast hh)
  · have he : CoveringOptimum.objective (fun v => ((c v).val : ℝ))
        (fun v => (SolutionWord.copies w v : ℝ) / q) = (SolutionWord.cost w : ℝ) / q := by
      have hnat := GeneralCoveringSpec.exact_cost cover K.vertices c b M w hvalid
      have hr : (∑ v, ((c v).val : ℝ) * (SolutionWord.copies w v : ℝ)) = SolutionWord.cost w := by
        change (∑ v, (c v).val * SolutionWord.copies w v) = SolutionWord.cost w at hnat
        exact_mod_cast hnat
      change (∑ v, ((c v).val : ℝ) * ((SolutionWord.copies w v : ℝ) / q)) = _
      rw [← hr, Finset.sum_div]
      simp only [mul_div_assoc]
    rw [he]
    calc
      _ ≤ ((q : ℝ) + 2 * (a : ℝ)) * CoveringOptimum.number cover R
          (fun v => ((c v).val : ℝ)) / q := div_le_div_of_nonneg_right hcostreal hqp.le
      _ = (1 + 2 * (a : ℝ) / q) * CoveringOptimum.number cover R
          (fun v => ((c v).val : ℝ)) := by field_simp [ne_of_gt hqp] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) haccuracy) hnumber
  · intro v
    field_simp [ne_of_gt hqp]
  · intro v hv
    by_contra hn
    have hp : 0 < SolutionWord.copies w v := Nat.pos_of_ne_zero hn
    obtain ⟨r, hr, hvr⟩ := GeneralCoveringSpec.used_is_admissible cover G solver K.vertices c b M input
      hspec (fun v => lt_of_lt_of_le Nat.zero_lt_one (hpositive v)) v0 hv0 w hw v hp
    have hrR : r ∈ R := by
      by_contra hnR
      change 0 < (if r ∈ R then q else 0) at hr
      rw [if_neg hnR] at hr
      omega
    exact hv (Finset.mem_biUnion.mpr ⟨r, hrR, hvr⟩)
end Paper.GeneralCoveringFractionalCorrect

#print axioms Paper.GeneralCoveringFractionalCorrect.spec

#print axioms Paper.GeneralCoveringFractionalCorrect.instance_feasible
