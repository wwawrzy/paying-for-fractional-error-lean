import Paper.Endpoints.Girth.CurrentGirthOutput
import Paper.Endpoints.Bounds.CurrentCriticalKT0
import Paper.Preliminaries.PlanarDensity

/-! # Physical current-rounding endpoints at girths four and six -/

namespace Paper.CurrentGirthProgram

open BroadcastModel SevenFoundation

section Semantics

variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] {N : ℕ}

theorem correct_four (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 4 ≤ c.length)
    (D : ℕ) (hD : 0 < D) (P : Program V (Bool × Fin 6) (Fin N))
    (hraw : PartialOptimum.Feasible G (CurrentBudget.demands G 4)
        (fun v => ((CurrentCriticalProgram.raw G 4 P v).val : ℝ) / D) ∧
      PartialOptimum.objective (CurrentCriticalProgram.weights G 4)
        (fun v => ((CurrentCriticalProgram.raw G 4 P v).val : ℝ) / D) ≤
          (1 + (1 / 100 : ℝ)) *
            PartialOptimum.number G (CurrentBudget.demands G 4) (CurrentCriticalProgram.weights G 4)) :
    dominates G (CurrentCriticalProgram.output G 4 D P) ∧
      ((CurrentCriticalProgram.output G 4 D P).card : ℝ) ≤ 5 * fractionalNumber G := by
  let x := fun v => ((CurrentCriticalProgram.numerators G 4 D P v).val : ℝ) / D
  have he : x = CurrentBudget.restrict G 4
      (PartialOptimum.cap (fun v => ((CurrentCriticalProgram.raw G 4 P v).val : ℝ) / D)) :=
    CurrentCriticalProgram.project_value G 4 D hD (CurrentCriticalProgram.raw G 4 P)
  have hs := CurrentCriticalProgram.cap_restrict_spec G 4 _ hraw.1 (1 / 100) hraw.2
  rw [← he] at hs
  have hc : ∀ v ∈ CurrentBudget.candidates G 4, x v ≤ 1 := fun v _ => hs.2.1 v
  have ho := CurrentThresholdProgram.output_eq G 4 D (D + 1) hD 2 (by norm_num)
    (CurrentCriticalProgram.numerators G 4 D P) hs.1 hc
  have hb := CurrentGirthOutput.rounded_four G x hs.1 hc hplanar hgirth hs.2.2
  have hout := (CurrentCriticalProgram.output_eq_threshold G 4 D P).trans ho
  rw [hout]
  exact hb

theorem correct_six (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length)
    (D : ℕ) (hD : 0 < D) (P : Program V (Bool × Fin 5) (Fin N))
    (hraw : PartialOptimum.Feasible G (CurrentBudget.demands G 3)
        (fun v => ((CurrentCriticalProgram.raw G 3 P v).val : ℝ) / D) ∧
      PartialOptimum.objective (CurrentCriticalProgram.weights G 3)
        (fun v => ((CurrentCriticalProgram.raw G 3 P v).val : ℝ) / D) ≤
          (1 + (2 / 205 : ℝ)) *
            PartialOptimum.number G (CurrentBudget.demands G 3) (CurrentCriticalProgram.weights G 3)) :
    dominates G (CurrentCriticalProgram.output G 3 D P) ∧
      ((CurrentCriticalProgram.output G 3 D P).card : ℝ) ≤ 4 * fractionalNumber G := by
  let x := fun v => ((CurrentCriticalProgram.numerators G 3 D P v).val : ℝ) / D
  have he : x = CurrentBudget.restrict G 3
      (PartialOptimum.cap (fun v => ((CurrentCriticalProgram.raw G 3 P v).val : ℝ) / D)) :=
    CurrentCriticalProgram.project_value G 3 D hD (CurrentCriticalProgram.raw G 3 P)
  have hs := CurrentCriticalProgram.cap_restrict_spec G 3 _ hraw.1 (2 / 205) hraw.2
  rw [← he] at hs
  have hc : ∀ v ∈ CurrentBudget.candidates G 3, x v ≤ 1 := fun v _ => hs.2.1 v
  have ho := CurrentThresholdProgram.output_eq G 3 D (D + 1) hD (3 / 2) (by norm_num)
    (CurrentCriticalProgram.numerators G 3 D P) hs.1 hc
  have hb := CurrentGirthOutput.rounded_six G x hs.1 hc hplanar hgirth hs.2.2
  have hout := (CurrentCriticalProgram.output_eq_threshold G 3 D P).trans ho
  rw [hout]
  exact hb

end Semantics

set_option maxHeartbeats 1500000 in
theorem parameters_four :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar →
        (∀ (v : V) (c : G.Walk v v), c.IsCycle → 4 ≤ c.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 5 q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        dominates G (CurrentCriticalKT0.output G ports C 4 D P) ∧
          ((CurrentCriticalKT0.output G ports C 4 D P).card : ℝ) ≤ 5 * fractionalNumber G ∧
          (CurrentCriticalKT0.program C 4 D P).rounds = CurrentCriticalKT0.roundBound A r k T M ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (CurrentCriticalKT0.program C 4 D P).maxBits ≤
              CurrentCriticalKT0.messageConstant 4 A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
    GeneralFractionalBroadcast.parameters 3 (by norm_num) 5 (1 / 100) (by norm_num)
  refine ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hplanar hgirth ports b C
  let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 5 q M hQ
  let D := PartialFractionalProgram.denominator Δ k Q T s q
  have hD : 0 < D := PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq
  have hr := hrun G (PlanarDensity.minor_density G hplanar) C (CurrentBudget.demands G 4)
    (fun v => (CurrentZoneProgram.expected G 4 v).cost) (CurrentZoneProgram.cost_positive G 4)
  dsimp only at hr ⊢
  simp only [Program.runEncoded_eq_run] at hr
  have hgood := correct_four G hplanar hgirth D hD P hr
  rw [CurrentCriticalKT0.output_eq G ports C]
  refine ⟨hgood.1, hgood.2, CurrentCriticalKT0.solver_rounds C 4 A L Δ r k t Q T s q M hQ, ?_⟩
  intro n c hids
  exact CurrentCriticalKT0.logarithmic_bits C 4 A L Δ r k t Q T s q M hQ n c hids

set_option maxHeartbeats 1500000 in
theorem parameters_six :
    ∃ A L Δ r k t Q T s q M : ℕ, ∃ hQ : 0 < Q, 0 < q ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar →
        (∀ (v : V) (c : G.Walk v v), c.IsCycle → 6 ≤ c.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
        let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 4 q M hQ
        let D := PartialFractionalProgram.denominator Δ k Q T s q
        dominates G (CurrentCriticalKT0.output G ports C 3 D P) ∧
          ((CurrentCriticalKT0.output G ports C 3 D P).card : ℝ) ≤ 4 * fractionalNumber G ∧
          (CurrentCriticalKT0.program C 3 D P).rounds = CurrentCriticalKT0.roundBound A r k T M ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (CurrentCriticalKT0.program C 3 D P).maxBits ≤
              CurrentCriticalKT0.messageConstant 3 A L Δ r k Q T s q M c * Nat.clog 2 (n + 2) := by
  obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hrun⟩ :=
    GeneralFractionalBroadcast.parameters 3 (by norm_num) 4 (2 / 205) (by norm_num)
  refine ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, ?_⟩
  intro V _ _ G _ hplanar hgirth ports b C
  let P := GeneralFractionalBroadcast.program C A L Δ r k t Q T s 4 q M hQ
  let D := PartialFractionalProgram.denominator Δ k Q T s q
  have hD : 0 < D := PartialFractionalProgram.denominator_pos Δ k Q T s q hQ hq
  have hr := hrun G (PlanarDensity.minor_density G hplanar) C (CurrentBudget.demands G 3)
    (fun v => (CurrentZoneProgram.expected G 3 v).cost) (CurrentZoneProgram.cost_positive G 3)
  dsimp only at hr ⊢
  simp only [Program.runEncoded_eq_run] at hr
  have hgood := correct_six G hplanar hgirth D hD P hr
  rw [CurrentCriticalKT0.output_eq G ports C]
  refine ⟨hgood.1, hgood.2, CurrentCriticalKT0.solver_rounds C 3 A L Δ r k t Q T s q M hQ, ?_⟩
  intro n c hids
  exact CurrentCriticalKT0.logarithmic_bits C 3 A L Δ r k t Q T s q M hQ n c hids

end Paper.CurrentGirthProgram

#print axioms Paper.CurrentGirthProgram.correct_four
#print axioms Paper.CurrentGirthProgram.correct_six
#print axioms Paper.CurrentGirthProgram.parameters_four
#print axioms Paper.CurrentGirthProgram.parameters_six
