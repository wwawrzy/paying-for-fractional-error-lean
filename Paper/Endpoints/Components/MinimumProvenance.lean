import Paper.Preliminaries.MaskedFlooding
import Paper.Preliminaries.PayloadFlood

/-! Source-distance provenance for the existing executable flooding rounds.
The graph `I` is the logical incidence graph on which these rounds are evaluated.
This module does not assert a simulation on a different physical graph. -/
namespace Paper.ComponentAcceptance
open BroadcastModel MaskedMinimum
variable {V : Type} [LinearOrder V] [Fintype V]
variable (I : SimpleGraph V) [DecidableRel I.Adj]

/-- A stored minimum comes from an active source at most `n` logical edges away. -/
theorem minimum_source_walk (A : V → Bool) (n : ℕ) {v u : V}
    (h : (MaskedFlooding.state I A n v).value = some u) :
    ∃ p : I.Walk v u, p.length ≤ n ∧ ∀ z ∈ p.support, A z = true := by
  induction n generalizing v u with
  | zero =>
    change (if A v then some v else none) = some u at h
    cases ha : A v with
    | false => simp [ha] at h
    | true =>
      simp only [ha, ↓reduceIte, Option.some.injEq] at h
      subst u
      exact ⟨.nil, le_rfl, by simpa using ha⟩
  | succ n ih =>
    cases ha : A v with
    | false => rw [MaskedFlooding.inactive I A (n + 1) ha] at h; contradiction
    | true =>
      rw [MaskedFlooding.update_active I A n ha] at h
      apply pool_origin _ _ _
        (fun u => ∃ p : I.Walk v u, p.length ≤ n + 1 ∧
          ∀ z ∈ p.support, A z = true) ?_ ?_ (minimum_mem h)
      · intro u hu
        obtain ⟨p, hp, hpa⟩ := ih hu
        exact ⟨p, by omega, hpa⟩
      · intro w u hu
        obtain ⟨p, hp, hpa⟩ := ih hu
        refine ⟨.cons ((I.mem_neighborFinset v w).mp w.property) p, ?_, ?_⟩
        · simp only [SimpleGraph.Walk.length_cons]; omega
        · intro z hz
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact ha
          · exact hpa z hz

/-- Exact minimum characterization, including a witness at the claimed radius. -/
theorem minimum_characterization (A : V → Bool) (n : ℕ) {v : V}
    (hv : A v = true) :
    ∃ u, (MaskedFlooding.state I A n v).value = some u ∧
      (∃ p : I.Walk v u, p.length ≤ n ∧ ∀ z ∈ p.support, A z = true) ∧
      ∀ w (p : I.Walk v w), p.length ≤ n →
        (∀ z ∈ p.support, A z = true) → u ≤ w := by
  obtain ⟨u, hu, _⟩ := MaskedFlooding.le_initial I A n hv
  refine ⟨u, hu, minimum_source_walk I A n hu, ?_⟩
  intro w p hp hpa
  obtain ⟨m, hm, hmw⟩ := MaskedFlooding.le_of_walk I A p hpa n hp
  have heq : m = u := Option.some.inj (hm.symm.trans hu)
  simpa [heq] using hmw

/-- Payload flooding cannot invent a packet or move it faster than one logical edge
per round. All vertices participate; the initial payloads remain arbitrary. -/
theorem payload_source_walk {X : Type} (S : V → PayloadFlood.State X)
    (ha : ∀ v, (S v).1 = true) (n : ℕ) {v : V} {x : X}
    (h : (PayloadFlood.state I S n v).2 = some x) :
    ∃ (w : V) (p : I.Walk v w), p.length ≤ n ∧ (S w).2 = some x := by
  induction n generalizing v with
  | zero => exact ⟨v, .nil, le_rfl, h⟩
  | succ n ih =>
    change (if (PayloadFlood.state I S n v).1 then
      match (PayloadFlood.state I S n v).2 with
      | some a => some a
      | none => BroadcastChoice.choose (I.neighborFinset v)
          (fun w => if (PayloadFlood.state I S n w).1 then
            (PayloadFlood.state I S n w).2 else none)
      else none) = some x at h
    rw [PayloadFlood.active, ha] at h
    simp only [↓reduceIte] at h
    cases hv : (PayloadFlood.state I S n v).2 with
    | some a =>
      simp only [hv, Option.some.injEq] at h
      subst a
      obtain ⟨w, p, hp, hs⟩ := ih hv
      exact ⟨w, p, by omega, hs⟩
    | none =>
      rw [hv] at h
      obtain ⟨w, hw⟩ := BroadcastChoice.origin _ _ h
      rw [PayloadFlood.active, ha] at hw
      simp only [↓reduceIte] at hw
      obtain ⟨u, p, hp, hs⟩ := ih hw
      refine ⟨u, .cons ((I.mem_neighborFinset v w).mp w.property) p, ?_, hs⟩
      simp only [SimpleGraph.Walk.length_cons]; omega

end Paper.ComponentAcceptance

#print axioms Paper.ComponentAcceptance.minimum_source_walk
#print axioms Paper.ComponentAcceptance.minimum_characterization
#print axioms Paper.ComponentAcceptance.payload_source_walk
