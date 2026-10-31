import Paper.Solver.LocalSearch.GeneralFractionalBroadcast
import Paper.Endpoints.Rounding.NoncriticalOptimum
import Paper.Communication.FixedMappedProgram

/-! Actual whole-graph fractional cover, capped by an integer min at the
fixed common denominator. Capping adds no rounds or transmitted bits. -/
namespace Paper.CappedWholeProgram
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def cap (D : ℕ) {N : ℕ} (p : Fin N) : Fin (D + 1) :=
  ⟨min p.val D, Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem cap_value (D : ℕ) (hD : 0 < D) {N : ℕ} (p : Fin N) :
    ((cap D p).val : ℝ) / D = min 1 ((p.val : ℝ) / D) := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases h : p.val ≤ D
  · have hr : (p.val : ℝ) ≤ D := by exact_mod_cast h
    rw [min_eq_right ((div_le_one hd).mpr hr)]
    exact congrArg (fun n : ℕ => (n : ℝ) / D) (min_eq_left h)
  · have hr : (D : ℝ) ≤ p.val := by exact_mod_cast (le_of_not_ge h)
    rw [min_eq_left ((one_le_div hd).mpr hr)]
    change ((min p.val D : ℕ) : ℝ) / D = 1
    rw [min_eq_right (le_of_not_ge h), div_self (ne_of_gt hd)]

def program {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    Program V Unit (Fin (PartialFractionalProgram.denominator Δ k Q T s q + 1)) :=
  FixedMappedProgram.program (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 1 q M hQ)
    (true, (1 : Fin 2)) (cap (PartialFractionalProgram.denominator Δ k Q T s q))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s q M hQ).run G (fun _ => ()) = fun v =>
      cap (PartialFractionalProgram.denominator Δ k Q T s q)
        ((GeneralFractionalBroadcast.program C A L Δ r k t Q T s 1 q M hQ).run G (fun _ => (true, 1)) v) :=
  FixedMappedProgram.run G _ _ _

theorem rounds {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s q M hQ).rounds =
      (2 * A) * (4 + 2 * GeneralInitBroadcast.rank A) +
        (34 + 4 * OwnerBoundaryMean.radius k T + 4 * r + RecursiveSearch.roundBound (4 * k) A M) := by
  rw [program, FixedMappedProgram.rounds, GeneralFractionalBroadcast.rounds]

theorem maxBits {b : ℕ} (C : BitCode V b) (A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q) :
    (program C A L Δ r k t Q T s q M hQ).maxBits =
      (GeneralFractionalBroadcast.program C A L Δ r k t Q T s 1 q M hQ).maxBits := by
  rw [program, FixedMappedProgram.maxBits]

set_option maxHeartbeats 1000000 in
theorem parameters (a : ℝ) (ha : 1 ≤ a) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G a → ∀ {b : ℕ} (C : BitCode V b),
        let y := fun v => (((program C A L Δ r k t Q T s q M hQ).run G (fun _ => ()) v).val : ℝ) /
          PartialFractionalProgram.denominator Δ k Q T s q
        PartialOptimum.Feasible G Finset.univ y ∧ (∀ v, y v ≤ 1) ∧
          (∑ v, y v) ≤ (1 + δ) * fractionalNumber G := by
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ := GeneralFractionalBroadcast.parameters a ha 1 δ hδ
  refine ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hden b C
  have hraw := hrun G hden C Finset.univ (fun _ => (1 : Fin 2)) (fun _ => Nat.le_refl 1)
  dsimp only at hraw ⊢
  rw [Program.runEncoded_eq_run] at hraw
  have hin : (fun u : V => (decide (u ∈ (Finset.univ : Finset V)), (1 : Fin 2))) =
      (fun _ => (true, (1 : Fin 2))) := by funext u; simp only [Finset.mem_univ, decide_true]
  rw [hin] at hraw
  let x := fun v => (((GeneralFractionalBroadcast.program C A L Δ r k t Q T s 1 q M hQ).run G
    (fun _ => (true, 1)) v).val : ℝ) / PartialFractionalProgram.denominator Δ k Q T s q
  have he : (fun v => (((program C A L Δ r k t Q T s q M hQ).run G (fun _ => ()) v).val : ℝ) /
      PartialFractionalProgram.denominator Δ k Q T s q) = PartialOptimum.cap x := by
    rw [run]
    funext v
    exact cap_value _ (PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq) _
  have hc := PartialOptimum.cap_cost_le (fun _ : V => (1 : ℝ)) x (fun _ => zero_le_one)
  have hm : (∑ v, x v) ≤ (1 + δ) * fractionalNumber G := by
    simpa only [PartialOptimum.objective, Fin.val_one, Nat.cast_one, one_mul, NoncriticalOptimum.number_eq] using hraw.2
  have hcost : (∑ v, PartialOptimum.cap x v) ≤ ∑ v, x v := by
    simpa only [PartialOptimum.objective, one_mul] using hc
  have hspec : PartialOptimum.Feasible G Finset.univ (PartialOptimum.cap x) ∧
      (∀ v, PartialOptimum.cap x v ≤ 1) ∧ (∑ v, PartialOptimum.cap x v) ≤ (1 + δ) * fractionalNumber G :=
    ⟨PartialOptimum.cap_feasible G Finset.univ x hraw.1, fun v => min_le_left 1 (x v), hcost.trans hm⟩
  simpa only [← he] using hspec

end Paper.CappedWholeProgram
