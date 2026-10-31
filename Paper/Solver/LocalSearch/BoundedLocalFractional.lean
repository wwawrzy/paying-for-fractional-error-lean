import Paper.Solver.LocalSearch.ActiveRecursiveSearch
import Paper.Solver.LocalSearch.FractionalSearch
import Paper.Communication.EncodedProgram
import Paper.Averaging.Tasks.KT0Compiler

/-! The bounded-diameter local fractional solver under induced-subgraph
density only. The executable program receives just a local demand bit and
bounded integer cost. Diameter, density, budget and denominator are public
numeric parameters; an optimum certificate is used only in the proof. -/
namespace Paper.BoundedLocalFractional
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def input {B : ℕ} (s : Fin (B + 1) × Bool) : FractionalSearch.Input V B :=
  ⟨true, s.1, s.2⟩

def program {bits : ℕ} (C : BitCode V bits) (D p B q M : ℕ) :
    Program V (Fin (B + 1) × Bool) (Fin (q + 1)) :=
  .seq (.local fun _ _ s => input s)
    (.seq (FractionalSearch.program C D p B q M)
      (.local fun _ _ n => ⟨min q n.val, Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def wholeContext (D : ℕ) (hG : G.Connected)
    (hD : ∀ x y, ∃ w : G.Walk x y, w.length ≤ D) : ActiveTask.Context G where
  vertices := Finset.univ
  nonempty := by letI := hG.nonempty; exact Finset.univ_nonempty
  diameter := D
  paths := by
    intro x y
    obtain ⟨w, hw⟩ := hD x.val y.val
    let f : G →g G.induce (↑(Finset.univ : Finset V) : Set V) :=
      { toFun := fun v => ⟨v, Finset.mem_univ v⟩
        map_rel' := fun h => h }
    exact ⟨w.map f, by simpa using hw⟩

/-- The untruncated executed multiplicities attain the fractional benchmark.
The hypothesis controls subgraphs, not arbitrary graph minors. -/
theorem raw_spec (D : ℕ) (hG : G.Connected)
    (hD : ∀ x y, ∃ w : G.Walk x y, w.length ≤ D)
    (a : ℝ) (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a)
    (p : ℕ) (hp : 1 ≤ p) (hap : a ≤ p) (B : ℕ) (c : V → Fin (B + 1))
    (hc : ∀ v, 1 ≤ (c v).val) (R : Finset V) (K ξ : ℝ) (hξ : 0 < ξ)
    (hK : PartialOptimum.number G R (fun v => ((c v).val : ℝ)) ≤ K)
    {bits : ℕ} (C : BitCode V bits) :
    let q := LocalSolverMath.denominator p ξ
    let M := ⌈(q + 2 * (p : ℝ)) * K⌉₊
    let s := fun v => input (V := V) (c v, decide (v ∈ R))
    let x := fun v => (((FractionalSearch.program C D p B q M).run G s v).val : ℝ) / q
    PartialOptimum.Feasible G R x ∧
      PartialOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
        (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) := by
  dsimp only
  let q := LocalSolverMath.denominator p ξ
  let M := ⌈(q + 2 * (p : ℝ)) * K⌉₊
  let s := fun v => input (V := V) (c v, decide (v ∈ R))
  let b := TaskBenchmark.demand (q := q) R
  let z := fun v => FractionalSearch.searchInput q (s v)
  let ctx := wholeContext G D hG hD
  have hcR : ∀ v, (1 : ℝ) ≤ (c v).val := fun v => Nat.one_le_cast.mpr (hc v)
  obtain ⟨benchmark, hbest, _, _, hcost, _⟩ := LocalSolverMath.local_solver G R a ha
    hden p hp hap (fun v => ((c v).val : ℝ)) hcR K ξ hξ hK
  have hvalid := TaskBenchmark.best_sound G a (fun v => ((c v).val : ℝ)) M
    (LocalFractional.demand R q) benchmark hbest
  have hpden : Incidence.InducedDensityBound G (p : ℝ) := by
    intro S
    exact (hden S).trans (mul_le_mul_of_nonneg_right hap (Nat.cast_nonneg _))
  have hz : ∀ r, (z r).value = b r := by
    intro r
    apply Fin.ext
    simp [z, s, input, FractionalSearch.searchInput, b, TaskBenchmark.demand]
  have hs := ActiveRecursiveSearch.correct G ctx p hp hpden B q c C M b z
    (fun v => by simp [z, s, input, FractionalSearch.searchInput, ctx, wholeContext])
    (fun _ => rfl) hz (fun r hr => False.elim (hr (Finset.mem_univ r)))
  obtain ⟨v0, hv0⟩ := ctx.nonempty
  obtain ⟨w, hw, hcw⟩ := hs.complete benchmark hvalid.1
    (fun r hr => False.elim (hr (Finset.mem_univ r))) hvalid.2 v0 hv0
  have hwvalid := hs.sound v0 hv0 w hw
  have hrun : ∀ v, (RecursiveSearch.program C D p B q M).run G z v = some w := by
    intro v
    exact (hs.uniform v v0 (Finset.mem_univ _) hv0).trans hw
  have hcopies : ∀ v, ((FractionalSearch.program C D p B q M).run G s v).val =
      SolutionWord.copies w v := by
    intro v
    rw [FractionalSearch.run_program]
    change (FractionalSearch.count M v
      ((RecursiveSearch.program C D p B q M).run G z v)).val = _
    rw [hrun]
    exact FractionalSearch.count_some w hwvalid.1 v
  change PartialOptimum.Feasible G R
      (fun v => (((FractionalSearch.program C D p B q M).run G s v).val : ℝ) / q) ∧
    PartialOptimum.objective (fun v => ((c v).val : ℝ))
      (fun v => (((FractionalSearch.program C D p B q M).run G s v).val : ℝ) / q) ≤ _
  simp_rw [hcopies]
  have hqp : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (LocalSolverMath.denominator_pos p ξ))
  refine ⟨⟨fun v => div_nonneg (Nat.cast_nonneg _) hqp.le, ?_⟩, ?_⟩
  · intro r hr
    have hh := hwvalid.2.2.2 r
    change (if r ∈ R then q else 0) ≤ _ at hh
    rw [if_pos hr] at hh
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hqp).mpr
    simpa only [one_mul] using (show (q : ℝ) ≤
      ∑ v ∈ closed G r, (SolutionWord.copies w v : ℝ) by exact_mod_cast hh)
  · have he : PartialOptimum.objective (fun v => ((c v).val : ℝ))
        (fun v => (SolutionWord.copies w v : ℝ) / q) = (SolutionWord.cost w : ℝ) / q := by
      rw [← SearchSpec.exact_cost G ctx.vertices c b M w hwvalid]
      simp [PartialOptimum.objective, IntegralTable.cost, mul_div_assoc, Finset.sum_div]
    rw [he]
    have hebench : (IntegralTable.cost (fun v => (c v).val) benchmark : ℝ) / q =
        ∑ v, ((c v).val : ℝ) * LocalFractional.vector q benchmark v := by
      simp [IntegralTable.cost, LocalFractional.vector, mul_div_assoc, Finset.sum_div]
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hcw) hqp.le).trans
      (hebench.trans_le hcost)

theorem capped_output {bits : ℕ} (C : BitCode V bits) (D p B q M : ℕ)
    (hq : 1 ≤ q) (s : V → Fin (B + 1) × Bool) :
    (fun v => (((program C D p B q M).runEncoded G s v).val : ℝ) / q) =
      PartialOptimum.cap (fun v =>
        (((FractionalSearch.program C D p B q M).run G (fun u => input (s u)) v).val : ℝ) / q) := by
  funext v
  rw [Program.runEncoded_eq_run]
  change ((min q ((FractionalSearch.program C D p B q M).run G
      (fun u => input (s u)) v).val : ℕ) : ℝ) / q = min 1 _
  have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Nat.cast_min, ← min_div_div_right (Nat.cast_nonneg q), div_self hqn]

/-- The paper's local-solver guarantee, including the actual encoded output,
its cap at one, and a common positive denominator. -/
theorem spec (D : ℕ) (hG : G.Connected)
    (hD : ∀ x y, ∃ w : G.Walk x y, w.length ≤ D)
    (a : ℝ) (ha : 1 ≤ a) (hden : Incidence.InducedDensityBound G a)
    (p : ℕ) (hp : 1 ≤ p) (hap : a ≤ p) (B : ℕ) (c : V → Fin (B + 1))
    (hc : ∀ v, 1 ≤ (c v).val) (R : Finset V) (K ξ : ℝ) (hξ : 0 < ξ)
    (hK : PartialOptimum.number G R (fun v => ((c v).val : ℝ)) ≤ K)
    {bits : ℕ} (C : BitCode V bits) :
    let q := LocalSolverMath.denominator p ξ
    let M := ⌈(q + 2 * (p : ℝ)) * K⌉₊
    let s := fun v => (c v, decide (v ∈ R))
    let n := fun v => ((program C D p B q M).runEncoded G s v).val
    let x := fun v => (n v : ℝ) / q
    PartialOptimum.Feasible G R x ∧
      PartialOptimum.objective (fun v => ((c v).val : ℝ)) x ≤
        (1 + ξ) * PartialOptimum.number G R (fun v => ((c v).val : ℝ)) ∧
      (∀ v, x v ≤ 1) ∧ ∀ v, (q : ℝ) * x v = n v := by
  dsimp only
  let q := LocalSolverMath.denominator p ξ
  let M := ⌈(q + 2 * (p : ℝ)) * K⌉₊
  let s := fun v => (c v, decide (v ∈ R))
  let x := fun v => (((FractionalSearch.program C D p B q M).run G
    (fun u => input (s u)) v).val : ℝ) / q
  have hraw := raw_spec G D hG hD a ha hden p hp hap B c hc R K ξ hξ hK C
  change PartialOptimum.Feasible G R x ∧
    PartialOptimum.objective (fun v => ((c v).val : ℝ)) x ≤ _ at hraw
  have he := capped_output G C D p B q M (LocalSolverMath.denominator_pos p ξ) s
  change PartialOptimum.Feasible G R
      (fun v => (((program C D p B q M).runEncoded G s v).val : ℝ) / q) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]
    exact PartialOptimum.cap_feasible G R x hraw.1
  · rw [he]
    exact (PartialOptimum.cap_cost_le (fun v => ((c v).val : ℝ)) x
      (fun v => Nat.cast_nonneg _)).trans hraw.2
  · intro v
    have hh := congrFun he v
    rw [hh]
    exact min_le_left _ _
  · intro v
    have hqn : (q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_one (LocalSolverMath.denominator_pos p ξ)))
    change (q : ℝ) * (_ / q) = _
    field_simp

theorem rounds {bits : ℕ} (C : BitCode V bits) (D p B q M : ℕ) :
    (program C D p B q M).rounds = RecursiveSearch.roundBound D p M := by
  simp only [program, Program.rounds, FractionalSearch.rounds, Nat.add_zero, Nat.zero_add]

theorem maxBits {bits : ℕ} (C : BitCode V bits) (D p B q M : ℕ) :
    (program C D p B q M).maxBits ≤ 3 * bits + RecursiveSearch.extraBits D p B q M := by
  simpa only [program, Program.maxBits, Nat.max_zero, Nat.zero_max] using
    FractionalSearch.maxBits C D p B q M

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (D p B q M n c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C D p B q M).maxBits ≤
      (3 * c + RecursiveSearch.extraBits D p B q M) * Nat.clog 2 (n + 2) := by
  have hl : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hc := Nat.mul_le_mul_left (RecursiveSearch.extraBits D p B q M) hl
  have hh := maxBits C D p B q M
  nlinarith

end Paper.BoundedLocalFractional
