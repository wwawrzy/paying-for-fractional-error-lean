import Paper.Solver.Density.CappedFrozenPackets
import Paper.Solver.Density.CappedHaltRounds

/-! A sender's permanent six-message phase template after its near bit is
true. The graph-dependent functions below describe messages in an executed
phase for analysis; they are not graph-dependent network instructions.
Replaying these fields in an actual silent execution is a separate proof. -/

namespace Paper.Density.CappedFrozenMessages

open BroadcastModel SevenFoundation
open CappedCounterState (State decode)

structure Template where
  packet : List Bool
  tight : Bool
  finished : Bool
  near : Bool

/-- The same state packet and tightness bit occur in probe and update. -/
def Template.messages (t : Template) : List (List Bool) :=
  [t.packet, [t.tight], [t.finished], [t.near], t.packet, [t.tight]]

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Analysis-only extraction of a phase template from a fixed state vector. -/
def template (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) : Template :=
  ⟨(CappedEncodedRounds.tightRound cap m rho).send v (G.neighborFinset v) (s v),
    (eval G (CappedPacketRounds.tightRound cap m rho) s v).2,
    (CappedHaltRounds.statuses G cap m rho s v).finished,
    (CappedHaltRounds.nearStatuses G cap m rho s v).near⟩

/-- The actual encoded senders in order: the four probe broadcasts, then
the two update broadcasts on the state retained by the probe. -/
def phaseMessages (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) : List (List Bool) :=
  let t := eval G (CappedHaltRounds.tightRound cap m rho) s
  let f := eval G (CappedHaltRounds.statusRound cap m) t
  let a := eval G CappedHaltRounds.nearRound f
  let retained := fun u => (CappedHaltRounds.probe G cap m rho s u).state
  let u := eval G (CappedEncodedRounds.tightRound cap m rho) retained
  [(CappedHaltRounds.tightRound cap m rho).send v (G.neighborFinset v) (s v),
    (CappedHaltRounds.statusRound cap m).send v (G.neighborFinset v) (t v),
    CappedHaltRounds.nearRound.send v (G.neighborFinset v) (f v),
    CappedHaltRounds.doneRound.send v (G.neighborFinset v) (a v),
    (CappedEncodedRounds.tightRound cap m rho).send v (G.neighborFinset v) (retained v),
    (CappedEncodedRounds.freezeRound cap m).send v (G.neighborFinset v) (u v)]

theorem phaseMessages_eq (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V) :
    phaseMessages G cap m rho s v = (template G cap m rho s v).messages := by
  have ht : eval G (CappedHaltRounds.tightRound cap m rho) s =
      eval G (CappedPacketRounds.tightRound cap m rho) s :=
    PrefixBroadcast.eval_eq G CappedStateCode.code _ s
  have hf : eval G (CappedHaltRounds.statusRound cap m)
      (eval G (CappedHaltRounds.tightRound cap m rho) s) =
      CappedHaltRounds.statuses G cap m rho s := by
    unfold CappedHaltRounds.statusRound
    rw [PrefixBroadcast.eval_eq, ht]
    rfl
  have ha : eval G CappedHaltRounds.nearRound
      (eval G (CappedHaltRounds.statusRound cap m)
        (eval G (CappedHaltRounds.tightRound cap m rho) s)) =
      CappedHaltRounds.nearStatuses G cap m rho s := by
    unfold CappedHaltRounds.nearRound
    rw [PrefixBroadcast.eval_eq, hf]
    rfl
  have hu : eval G (CappedEncodedRounds.tightRound cap m rho) s =
      eval G (CappedPacketRounds.tightRound cap m rho) s :=
    PrefixBroadcast.eval_eq G CappedStateCode.code _ s
  unfold phaseMessages
  dsimp only
  rw [ha, hf, ht]
  simp only [CappedHaltRounds.probe_state, hu]
  rfl

theorem near_persistent (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hn : (CappedHaltRounds.nearStatuses G cap m rho (CappedExecution.run G cap m rho n) v).near = true) :
    (CappedHaltRounds.nearStatuses G cap m rho (CappedExecution.run G cap m rho (n + k)) v).near = true := by
  apply (CappedHaltRounds.near_iff G cap m rho _ v).mpr
  have hf := (CappedHaltRounds.near_iff G cap m rho _ v).mp hn
  intro u hu
  exact CappedFrozenPackets.finished_persistent G cap hm hcap rho hrho
    (Nat.le_add_right n k) u (hf u hu)

/-- A true near bit makes every field of the sender's future phase template
permanent, before requiring that the sender itself has a done certificate. -/
theorem template_stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hn : (CappedHaltRounds.nearStatuses G cap m rho (CappedExecution.run G cap m rho n) v).near = true) :
    template G cap m rho (CappedExecution.run G cap m rho (n + k)) v =
      template G cap m rho (CappedExecution.run G cap m rho n) v := by
  have hf := (CappedHaltRounds.near_iff G cap m rho _ v).mp hn
  have hv := hf v (self_mem_closed G v)
  have hfinished : (CappedHaltRounds.statuses G cap m rho
      (CappedExecution.run G cap m rho n) v).finished = true :=
    (CappedHaltRounds.statuses_finished G cap m rho _ v).mpr hv
  have hfuture : (CappedHaltRounds.statuses G cap m rho
      (CappedExecution.run G cap m rho (n + k)) v).finished = true :=
    (CappedHaltRounds.statuses_finished G cap m rho _ v).mpr
      (CappedFrozenPackets.finished_persistent G cap hm hcap rho hrho
        (Nat.le_add_right n k) v hv)
  have hnear := near_persistent G cap hm hcap rho hrho n k v hn
  change Template.mk _ _ _ _ = Template.mk _ _ _ _
  congr 1
  · exact CappedFrozenPackets.packet_stable G cap hm hcap rho hrho n k v hv
  · exact CappedFrozenPackets.tight_flag_stable G cap hm hcap rho hrho n k v hf
  · exact hfuture.trans hfinished.symm
  · exact hnear.trans hn.symm

/-- Exact equality of all six actual encoded messages, enabling a later
receiver-cache refinement without replacing any network instruction. -/
theorem phaseMessages_stable (cap : ℚ) {m : ℕ} (hm : 0 < m) (hcap : 0 ≤ cap)
    (rho : ℚ) (hrho : CappedCounterState.scale m * rho ≤ 1) (n k : ℕ) (v : V)
    (hn : (CappedHaltRounds.nearStatuses G cap m rho (CappedExecution.run G cap m rho n) v).near = true) :
    phaseMessages G cap m rho (CappedExecution.run G cap m rho (n + k)) v =
      phaseMessages G cap m rho (CappedExecution.run G cap m rho n) v := by
  rw [phaseMessages_eq, phaseMessages_eq, template_stable G cap hm hcap rho hrho n k v hn]

/-- The fourth actual message announces that the permanent template is ready. -/
theorem near_notification (cap : ℚ) (m : ℕ) (rho : ℚ) (s : V → State) (v : V)
    (hn : (CappedHaltRounds.nearStatuses G cap m rho s v).near = true) :
    (phaseMessages G cap m rho s v)[3]? = some [true] := by
  rw [phaseMessages_eq]
  simp only [Template.messages, template, List.getElem?_cons_succ,
    List.getElem?_cons_zero, hn]

end Paper.Density.CappedFrozenMessages

#print axioms Paper.Density.CappedFrozenMessages.phaseMessages_eq
#print axioms Paper.Density.CappedFrozenMessages.near_persistent
#print axioms Paper.Density.CappedFrozenMessages.template_stable
#print axioms Paper.Density.CappedFrozenMessages.phaseMessages_stable
#print axioms Paper.Density.CappedFrozenMessages.near_notification
