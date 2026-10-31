import Paper.Solver.Density.RationalRuntime
import Paper.Solver.Density.UnitDomination

/-! The actual two-broadcast runtime conserves primal coverage exactly.
Dual fulfilled counters are the closed-neighborhood sums of the accumulated
primal grid numerators, including the locally simulated diagonal incidence. -/
namespace Paper.Density.RationalBalance
open BroadcastModel RationalRuntime SevenFoundation
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def row (f : V → ℕ) (v : V) : ℕ := f v + ∑ u : G.neighborFinset v, f u

def Balanced {m K : ℕ} (s : V → State m K) : Prop :=
  ∀ v, (s v).fulfilled = row G (fun u => (s u).primal) v

theorem row_closed (f : V → ℕ) (v : V) : row G f v = ∑ u ∈ closed G v, f u := by
  rw [UnitDomination.closed_eq_insert, Finset.sum_insert (by simp)]
  exact congrArg (fun z => f v + z) (Finset.sum_coe_sort (G.neighborFinset v) f)

theorem initial_balanced (m K : ℕ) : Balanced G (fun _ => initial m K) := by
  intro v
  simp [initial, row]

theorem inner_balanced (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K)
    (hs : Balanced G s) : Balanced G ((inner m K ep ed).run G s) := by
  let t := eval G (primalRound m K ep ed) s
  have hp (u : V) : (t u).primal = (s u).primal + (t u).increment.value.val := rfl
  intro v
  change (s v).fulfilled + ((t v).increment.value.val +
      ∑ u : G.neighborFinset v, (t u).increment.value.val) =
    (t v).primal + ∑ u : G.neighborFinset v, (t u).primal
  rw [hs v]
  simp only [row, hp, Finset.sum_add_distrib]
  omega

theorem clean_primal {m K : ℕ} (s : State m K) : (clean s).primal = s.primal := by
  unfold clean
  split_ifs <;> rfl

theorem clean_fulfilled {m K : ℕ} (s : State m K) : (clean s).fulfilled = s.fulfilled := by
  unfold clean
  split_ifs <;> rfl

theorem clean_weight_lt {m K : ℕ} (s : State m K) :
    (clean s).weight < denominator m K := by
  have hD : 0 < denominator m K := by unfold denominator; positivity
  unfold clean
  split_ifs with hw hf
  · exact hD
  · exact Nat.mod_lt _ hD
  · exact Nat.lt_of_not_ge hw

theorem clean_balanced {m K : ℕ} (s : V → State m K) (hs : Balanced G s) :
    Balanced G (fun v => clean (s v)) := by
  intro v
  simp only [clean_fulfilled, row, clean_primal]
  exact hs v

theorem scan_balanced (m K : ℕ) (ep : ℤ) (j : ℕ) (s : V → State m K)
    (hs : Balanced G s) : Balanced G ((scan m K ep j).run G s) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih => exact ih _ (inner_balanced G m K ep j s hs)

theorem phase_balanced (m K : ℕ) (ep : ℤ) (s : V → State m K)
    (hs : Balanced G s) : Balanced G ((phase m K ep).run G s) := by
  apply clean_balanced
  apply scan_balanced
  exact hs

theorem iterate_balanced {m K : ℕ} (P : Program V (State m K) (State m K))
    (hP : ∀ s, Balanced G s → Balanced G (P.run G s)) (j : ℕ)
    (s : V → State m K) (hs : Balanced G s) : Balanced G ((P.iterate j).run G s) := by
  induction j with
  | zero => exact hs
  | succ j ih => exact hP _ ih

theorem outer_balanced (m K j : ℕ) (s : V → State m K) (hs : Balanced G s) :
    Balanced G ((outer m K j).run G s) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih =>
    apply ih
    exact iterate_balanced G _ (phase_balanced G m K _) _ s hs

/-- This equality refers to the literal final runtime state, not a supplied
coverage observer or an auxiliary task score. -/
theorem actual_fulfilled (m K : ℕ) (v : V) :
    let s := (outer (V := V) m K (K + target m K)).run G (fun _ => initial m K)
    (s v).fulfilled = ∑ u ∈ closed G v, (s u).primal := by
  dsimp only
  exact (outer_balanced G m K (K + target m K) _ (initial_balanced G m K) v).trans
    (row_closed G _ v)

end Paper.Density.RationalBalance

#print axioms Paper.Density.RationalBalance.inner_balanced
#print axioms Paper.Density.RationalBalance.clean_weight_lt
#print axioms Paper.Density.RationalBalance.actual_fulfilled
