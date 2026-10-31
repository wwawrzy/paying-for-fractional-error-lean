import Paper.Solver.Density.CappedExecution
import Paper.Solver.Density.CappedLocalHalt

/-! Reachable uncapped packets decode strictly below the cap. Consequently,
a finished vertex keeps its entire compact state and every future encoded
value packet, not merely its decoded rational value. Cache simulation and
physical silence are separate implementation obligations. -/

namespace Paper.Density.CappedFrozenPackets

open BroadcastModel
open CappedCounterState (State decode)
open scoped BigOperators

def Canonical (cap : ℚ) (m : ℕ) (s : State) : Prop :=
  s.capped = false → decode cap m s < cap

theorem initial_canonical (cap : ℚ) (m L : ℕ) :
    Canonical cap m (CappedCounterState.initial cap L) := by
  intro hc
  have hn : ¬ cap ≤ 1 / (L : ℚ) := of_decide_eq_false hc
  have hlt := lt_of_not_ge hn
  rw [CappedCounterState.initial_decode, min_eq_right hlt.le]
  exact hlt

theorem step_canonical (cap : ℚ) (m : ℕ) (blocked : Bool) (s : State)
    (hs : Canonical cap m s) : Canonical cap m (CappedCounterState.step cap m blocked s) := by
  unfold CappedCounterState.step
  split_ifs with hf hn
  · exact hs
  · intro h
    cases h
  · intro hc
    have hc' : s.capped = false := hc
    have he : decode cap m { s with exponent := s.exponent + 1 } =
        CappedCounterState.scale m * decode cap m s := by
      simp only [decode, hc', Bool.false_eq_true, ite_false, pow_succ]
      ring
    rw [he]
    exact lt_of_not_ge hn

theorem capped_of_decode_eq (cap : ℚ) (m : ℕ) (s : State)
    (hs : Canonical cap m s) (he : decode cap m s = cap) : s.capped = true := by
  cases hc : s.capped with
  | true => rfl
  | false => exact False.elim ((ne_of_lt (hs hc)) he)

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem transition_canonical (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V)
    (hs : Canonical cap m (s v)) :
    Canonical cap m (CappedEncodedRounds.transition G cap m rho s v) := by
  rw [CappedEncodedRounds.transition_eq]
  exact step_canonical cap m _ (s v) hs

theorem run_canonical (cap : ℚ) (m : ℕ) (rho : ℚ) (n : ℕ) (v : V) :
    Canonical cap m (CappedExecution.run G cap m rho n v) := by
  induction n with
  | zero => rw [CappedExecution.run, CappedExecution.initial_eq]; exact initial_canonical cap m _
  | succ n ih => exact transition_canonical G cap m rho _ v ih

/-- Canonical packets distinguish a cap reached by multiplication from an
uncapped value: decoded equality with the cap implies the stored cap bit. -/
theorem transition_fixed (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V)
    (hs : Canonical cap m (s v))
    (hf : CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
      (fun u => (decode cap m (s u) : ℝ)) v) :
    CappedEncodedRounds.transition G cap m rho s v = s v := by
  rw [CappedEncodedRounds.transition_eq]
  let y := fun u => decode cap m (s u)
  let tight := eval G (CappedRationalRounds.tightRound rho) y
  change CappedCounterState.step cap m
    (decide ((tight v).2 = true ∨ ∃ u : G.neighborFinset v, (tight u).2 = true)) (s v) = s v
  rcases hf with hb | he
  · have ht := (CappedRationalRounds.freeze_test G rho y v).mpr hb
    have ht' : (tight v).2 = true ∨ ∃ u : G.neighborFinset v, (tight u).2 = true := ht
    have hd : decide ((tight v).2 = true ∨
        ∃ u : G.neighborFinset v, (tight u).2 = true) = true := decide_eq_true ht'
    simp only [CappedCounterState.step, hd, Bool.true_or, ite_true]
  · change (decode cap m (s v) : ℝ) = (cap : ℝ) at he
    have heq : decode cap m (s v) = cap := Rat.cast_inj.mp he
    have hc := capped_of_decode_eq cap m (s v) hs heq
    simp [CappedCounterState.step, hc]

/-- Persistence is transferred from the proved real packing dynamics to
the actual finite-string execution. All numerical hypotheses are explicit. -/
theorem finished_persistent (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1)
    {n t : ℕ} (hnt : n ≤ t) (v : V)
    (hf : CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
      (fun u => (decode cap m (CappedExecution.run G cap m rho n u) : ℝ)) v) :
    CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
      (fun u => (decode cap m (CappedExecution.run G cap m rho t u) : ℝ)) v := by
  have hc : (0 : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hcap
  have hmR : (1 : ℝ) ≤ (CappedCounterState.scale m : ℝ) := by
    exact_mod_cast CappedCounterState.scale_ge_one hm
  have hr : (CappedCounterState.scale m : ℝ) * (rho : ℝ) ≤ 1 := by exact_mod_cast hrho
  have hi : ∀ u, 0 ≤ CappedInitialization.initial G (cap : ℝ) u := by
    intro u
    unfold CappedInitialization.initial
    positivity
  rw [CappedExecution.run_cast G cap hm hcap rho n] at hf
  rw [CappedExecution.run_cast G cap hm hcap rho t]
  exact CappedLocalHalt.finished_persistent G hc hmR hr
    (CappedInitialization.initial G (cap : ℝ)) hi
    (CappedInitialization.initial_le_cap G _) (CappedInitialization.initial_packing G _)
    hnt v hf

theorem state_stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hf : CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
      (fun u => (decode cap m (CappedExecution.run G cap m rho n u) : ℝ)) v) :
    CappedExecution.run G cap m rho (n + k) v = CappedExecution.run G cap m rho n v := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht := finished_persistent G cap hm hcap rho hrho (Nat.le_add_right n k) v hf
    have he := transition_fixed G cap m rho (CappedExecution.run G cap m rho (n + k)) v
      (run_canonical G cap m rho (n + k) v) ht
    change CappedEncodedRounds.transition G cap m rho
      (CappedExecution.run G cap m rho (n + k)) v = _
    exact he.trans ih

/-- Once the closed row is finished, its actual outgoing tightness bit is
constant. A successful two-hop probe supplies this closed-row premise. -/
theorem tight_flag_stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hf : ∀ u ∈ SevenFoundation.closed G v,
      CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
        (fun w => (decode cap m (CappedExecution.run G cap m rho n w) : ℝ)) u) :
    (eval G (CappedPacketRounds.tightRound cap m rho)
      (CappedExecution.run G cap m rho (n + k)) v).2 =
    (eval G (CappedPacketRounds.tightRound cap m rho)
      (CappedExecution.run G cap m rho n) v).2 := by
  have hmass : (∑ u ∈ SevenFoundation.closed G v,
      decode cap m (CappedExecution.run G cap m rho (n + k) u)) =
      ∑ u ∈ SevenFoundation.closed G v, decode cap m (CappedExecution.run G cap m rho n u) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [state_stable G cap hm hcap rho hrho n k u (hf u hu)]
  change decide (rho ≤ decode cap m (CappedExecution.run G cap m rho (n + k) v) +
      ∑ u : G.neighborFinset v, decode cap m (CappedExecution.run G cap m rho (n + k) u)) =
    decide (rho ≤ decode cap m (CappedExecution.run G cap m rho n v) +
      ∑ u : G.neighborFinset v, decode cap m (CappedExecution.run G cap m rho n u))
  apply Bool.decide_congr
  rw [CappedRationalRounds.row_closed G
      (fun u => decode cap m (CappedExecution.run G cap m rho (n + k) u)) v,
    CappedRationalRounds.row_closed G
      (fun u => decode cap m (CappedExecution.run G cap m rho n u)) v, hmass]

/-- The exact finite string sent by a finished vertex is reusable forever. -/
theorem packet_stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hf : CappedLocalHalt.finished G (cap : ℝ) (rho : ℝ)
      (fun u => (decode cap m (CappedExecution.run G cap m rho n u) : ℝ)) v) :
    (CappedEncodedRounds.tightRound cap m rho).send v (G.neighborFinset v)
        (CappedExecution.run G cap m rho (n + k) v) =
      (CappedEncodedRounds.tightRound cap m rho).send v (G.neighborFinset v)
        (CappedExecution.run G cap m rho n v) := by
  rw [state_stable G cap hm hcap rho hrho n k v hf]

end Paper.Density.CappedFrozenPackets

#print axioms Paper.Density.CappedFrozenPackets.initial_canonical
#print axioms Paper.Density.CappedFrozenPackets.step_canonical
#print axioms Paper.Density.CappedFrozenPackets.run_canonical
#print axioms Paper.Density.CappedFrozenPackets.transition_fixed
#print axioms Paper.Density.CappedFrozenPackets.finished_persistent
#print axioms Paper.Density.CappedFrozenPackets.packet_stable
#print axioms Paper.Density.CappedFrozenPackets.tight_flag_stable
