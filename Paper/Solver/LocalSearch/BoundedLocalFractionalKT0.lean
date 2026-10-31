import Paper.Solver.LocalSearch.BoundedLocalFractional

/-! A uniform paper-facing local solver. All numeric parameters are selected
before the graph. A first own-ID broadcast removes initial neighbor-ID knowledge. -/
namespace Paper.BoundedLocalFractionalKT0
open BroadcastModel (BitCode)
open BoundedLocalFractional

variable {V : Type} [LinearOrder V]

def program {bits : ℕ} (C : BitCode V bits) (D p B q M : ℕ) :
    PortBroadcastModel.Program V (Fin (B + 1) × Bool) (Fin (q + 1)) :=
  KT0Compiler.program C (BoundedLocalFractional.program C D p B q M)

variable [Fintype V]

theorem rounds {bits : ℕ} (C : BitCode V bits) (D p B q M : ℕ) :
    (program C D p B q M).rounds = 1 + RecursiveSearch.roundBound D p M := by
  rw [program, KT0Compiler.program_rounds, BoundedLocalFractional.rounds]

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (D p B q M n c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C D p B q M).maxBits ≤
      max c (3 * c + RecursiveSearch.extraBits D p B q M) * Nat.clog 2 (n + 2) := by
  exact KT0Compiler.logarithmic_bits C (BoundedLocalFractional.program C D p B q M)
    n c _ hids (BoundedLocalFractional.logarithmic_bits C D p B q M n c hids)

/-- The complete bounded-diameter solver statement. A diameter bound is
expressed by bounded-length walks, so neither a spanning tree nor a solution
is supplied to the program. The denominator and search budget are graph-independent. -/
theorem local_solver (a : ℝ) (ha : 1 ≤ a) (B D : ℕ) (K : ℝ)
    (ξ : ℚ) (hξ : 0 < ξ) :
    ∃ p q M : ℕ, 1 ≤ q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.Connected → (∀ x y, ∃ w : G.Walk x y, w.length ≤ D) →
        Incidence.InducedDensityBound G a →
        ∀ (R : Finset V) (cost : V → Fin (B + 1)),
          (∀ v, 1 ≤ (cost v).val) →
          PartialOptimum.number G R (fun v => ((cost v).val : ℝ)) ≤ K →
          ∀ (ports : PortBroadcastModel.Numbering G) {bits : ℕ} (C : BitCode V bits),
          let s := fun v => (cost v, decide (v ∈ R))
          let numerator := fun v => ((program C D p B q M).runEncoded G ports s v).val
          let x := fun v => (numerator v : ℝ) / q
          PartialOptimum.Feasible G R x ∧
            PartialOptimum.objective (fun v => ((cost v).val : ℝ)) x ≤
              (1 + (ξ : ℝ)) * PartialOptimum.number G R (fun v => ((cost v).val : ℝ)) ∧
            (∀ v, x v ≤ 1) ∧ (∀ v, (q : ℝ) * x v = numerator v) ∧
            (program C D p B q M).rounds = 1 + RecursiveSearch.roundBound D p M ∧
            ∀ n c : ℕ, bits ≤ c * Nat.clog 2 (n + 2) →
              (program C D p B q M).maxBits ≤
                max c (3 * c + RecursiveSearch.extraBits D p B q M) * Nat.clog 2 (n + 2) := by
  let p := Nat.ceil a
  let q := LocalSolverMath.denominator p (ξ : ℝ)
  let M := ⌈(q + 2 * (p : ℝ)) * K⌉₊
  have hap : a ≤ (p : ℝ) := Nat.le_ceil a
  have hp : 1 ≤ p := by exact_mod_cast ha.trans hap
  have hξR : (0 : ℝ) < ξ := by exact_mod_cast hξ
  refine ⟨p, q, M, LocalSolverMath.denominator_pos p (ξ : ℝ), ?_⟩
  intro V _ _ G _ hG hD hden R cost hc hK ports bits C
  dsimp only
  have hs := BoundedLocalFractional.spec G D hG hD a ha hden p hp hap
    B cost hc R K (ξ : ℝ) hξR hK C
  have he := KT0Compiler.program_encoded_correct G C
    (BoundedLocalFractional.program C D p B q M) ports (fun v => (cost v, decide (v ∈ R)))
  change (program C D p B q M).runEncoded G ports _ = _ at he
  rw [he]
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, rounds C D p B q M,
    fun n c hids => logarithmic_bits C D p B q M n c hids⟩

end Paper.BoundedLocalFractionalKT0

#print axioms Paper.BoundedLocalFractionalKT0.local_solver
