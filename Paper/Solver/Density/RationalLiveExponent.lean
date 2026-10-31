import Paper.Solver.Density.RationalCounters

/-! A live row's exponent remains strictly below the target throughout the
literal outer loop. Thus a live requirement has a positive public lower bound. -/
namespace Paper.Density.RationalLiveExponent
open BroadcastModel RationalRuntime RationalCounters

def LiveBound {m K : ℕ} (s : State m K) : Prop :=
  s.stopped = false → s.exponent.value.val < target m K

def Valid {m K : ℕ} (s : State m K) : Prop := Consistent s ∧ LiveBound s

theorem initial_valid {m : ℕ} (hm : 1 ≤ m) (K : ℕ) : Valid (initial m K) := by
  refine ⟨initial_consistent m K, ?_⟩
  intro _
  change (CappedCount.cap (target m K) 0).value.val < target m K
  simp only [CappedCount.cap, Nat.zero_min]
  unfold target
  exact Nat.mul_pos (by omega) (by omega)

theorem count_strict {m K : ℕ} (s : State m K)
    (hacc : s.fulfilled = s.exponent.value.val * denominator m K + s.weight)
    (hf : s.fulfilled < target m K * denominator m K) :
    s.exponent.value.val + s.weight / denominator m K < target m K := by
  have hmul : (s.exponent.value.val + s.weight / denominator m K) * denominator m K ≤
      s.fulfilled := by
    rw [Nat.add_mul, hacc]
    exact Nat.add_le_add_left (Nat.div_mul_le_self _ _) _
  by_contra hn
  have hbig := Nat.mul_le_mul_right (denominator m K) (Nat.le_of_not_gt hn)
  omega

theorem clean_live {m K : ℕ} (s : State m K) (hc : Consistent s) (hs : LiveBound s) :
    LiveBound (clean s) := by
  unfold clean
  split_ifs with hw hf
  · intro h
    contradiction
  · intro h
    have hstrict := count_strict s (hc.2 h) (Nat.lt_of_not_ge hf)
    change min (s.exponent.value.val + s.weight / denominator m K) (target m K) < target m K
    rw [min_eq_left hstrict.le]
    exact hstrict
  · exact hs

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem inner_live (m K : ℕ) (ep : ℤ) (ed : ℕ) (s : V → State m K)
    (hs : ∀ v, LiveBound (s v)) : ∀ v, LiveBound ((inner m K ep ed).run G s v) := by
  intro v
  exact hs v

theorem scan_live (m K : ℕ) (ep : ℤ) (j : ℕ) (s : V → State m K)
    (hs : ∀ v, LiveBound (s v)) : ∀ v, LiveBound ((scan m K ep j).run G s v) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih => exact ih _ (inner_live G m K ep j s hs)

theorem phase_live (m K : ℕ) (ep : ℤ) (s : V → State m K)
    (hc : ∀ v, Consistent (s v)) (hs : ∀ v, LiveBound (s v)) :
    ∀ v, LiveBound ((phase m K ep).run G s v) := by
  let a : V → State m K := fun u => {(s u) with active := !(s u).stopped}
  have hac : ∀ v, Consistent (a v) := hc
  have has : ∀ v, LiveBound (a v) := hs
  intro v
  exact clean_live _ (scan_consistent G m K ep K a hac v) (scan_live G m K ep K a has v)

theorem phase_valid (m K : ℕ) (ep : ℤ) (s : V → State m K)
    (hs : ∀ v, Valid (s v)) : ∀ v, Valid ((phase m K ep).run G s v) := by
  intro v
  exact ⟨phase_consistent G m K ep s (fun u => (hs u).1) v,
    phase_live G m K ep s (fun u => (hs u).1) (fun u => (hs u).2) v⟩

theorem iterate_valid {m K : ℕ} (P : Program V (State m K) (State m K))
    (hP : ∀ s, (∀ v, Valid (s v)) → ∀ v, Valid (P.run G s v))
    (j : ℕ) (s : V → State m K) (hs : ∀ v, Valid (s v)) :
    ∀ v, Valid ((P.iterate j).run G s v) := by
  induction j with
  | zero => exact hs
  | succ j ih => exact hP _ ih

theorem outer_valid (m K j : ℕ) (s : V → State m K) (hs : ∀ v, Valid (s v)) :
    ∀ v, Valid ((outer m K j).run G s v) := by
  induction j generalizing s with
  | zero => exact hs
  | succ j ih =>
    apply ih
    exact iterate_valid G _ (phase_valid G m K _) _ s hs

theorem actual_live {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (v : V) :
    LiveBound ((outer (V := V) m K (K + target m K)).run G (fun _ => initial m K) v) :=
  (outer_valid G m K (K + target m K) _ (fun _ => initial_valid hm K) v).2

end Paper.Density.RationalLiveExponent

#print axioms Paper.Density.RationalLiveExponent.count_strict
#print axioms Paper.Density.RationalLiveExponent.clean_live
#print axioms Paper.Density.RationalLiveExponent.actual_live
