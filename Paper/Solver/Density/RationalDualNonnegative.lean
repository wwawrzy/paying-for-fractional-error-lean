import Paper.Solver.Density.RationalDualLedger

/-! Nonnegativity of the constructed dual vector follows from every actual
allocation and cleanup payment, without an input dual-feasibility contract. -/
namespace Paper.Density.RationalDualNonnegative
open RationalRuntime RationalDualLedger
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Nonnegative {m K : ℕ} (L : Ledger (V := V) m K) : Prop :=
  (∀ v, 0 ≤ L.pending v) ∧ ∀ v, 0 ≤ L.paid v

theorem scan_nonnegative {m K : ℕ} (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K)
    (hL : Nonnegative L) : Nonnegative (accountScan G ep j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (inner_nonnegative G ep j L hL.1 hL.2)

theorem phase_nonnegative {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (L : Ledger (V := V) m K)
    (hL : Nonnegative L) : Nonnegative (accountPhase G ep L) := by
  let R : Ledger (V := V) m K :=
    { L with state := fun v => { L.state v with active := !(L.state v).stopped } }
  have hr : Nonnegative R := hL
  have hs := scan_nonnegative G ep K R hr
  exact clean_nonnegative hm ep _ hs.1 hs.2

theorem block_nonnegative {m K : ℕ} (hm : 1 ≤ m) (ep : ℤ) (j : ℕ) (L : Ledger (V := V) m K)
    (hL : Nonnegative L) : Nonnegative (accountBlock G ep j L) := by
  induction j with
  | zero => exact hL
  | succ j ih => exact phase_nonnegative G hm ep _ ih

theorem outer_nonnegative {m K : ℕ} (hm : 1 ≤ m) (j : ℕ) (L : Ledger (V := V) m K)
    (hL : Nonnegative L) : Nonnegative (accountOuter G j L) := by
  induction j generalizing L with
  | zero => exact hL
  | succ j ih => exact ih _ (block_nonnegative G hm _ (2 * m) L hL)

theorem actual_nonnegative {m K : ℕ} (hm : 1 ≤ m) : Nonnegative (actualLedger G m K) := by
  have hi : Nonnegative (initialLedger (V := V) m K) := by
    simp [Nonnegative, initialLedger]
  exact outer_nonnegative G hm (K + target m K) (initialLedger m K) hi

theorem actual_paid_nonnegative {m K : ℕ} (hm : 1 ≤ m) (v : V) :
    0 ≤ (actualLedger G m K).paid v := (actual_nonnegative G hm).2 v

end Paper.Density.RationalDualNonnegative

#print axioms Paper.Density.RationalDualNonnegative.actual_nonnegative
#print axioms Paper.Density.RationalDualNonnegative.actual_paid_nonnegative
