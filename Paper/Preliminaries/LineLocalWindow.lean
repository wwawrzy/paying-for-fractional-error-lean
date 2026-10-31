import Paper.Preliminaries.LineLocal
import Paper.Optimality.LowerBounds.PathPowerRamsey

namespace Paper.LineLocalWindow
open LineLocal

/-- The finite path is present exactly at coordinates 0,...,n-1. -/
def labels {n : ℕ} (ids : Fin n → ℕ) (x : ℤ) : Option ℕ :=
  if h : 0 ≤ x ∧ x < n then some (ids ⟨x.toNat, by omega⟩) else none

/-- A virtual finite window used only to define the local decision rule. -/
def canonical {r : ℕ} (w : Fin (2*r+1) → ℕ) (x : ℤ) : Option ℕ :=
  if h : -(r : ℤ) ≤ x ∧ x ≤ r then some (w ⟨(x+r).toNat, by omega⟩) else none

def rule {t : ℕ} (P : Program t Unit Bool) (r : ℕ) : PathPowerRamsey.Rule r :=
  fun w => P.run (canonical w) (fun _ => ()) 0

def output {n t : ℕ} (P : Program t Unit Bool) (ids : Fin n → ℕ) (v : Fin n) : Bool :=
  P.run (labels ids) (fun _ => ()) v.val

theorem agrees {n t : ℕ} (P : Program t Unit Bool) (r : ℕ) (hPr : P.radius ≤ r) (ids : Fin n → ℕ) :
    PathPowerRamsey.Agrees (rule P r) ids (output P ids) := by
  intro v hl hr
  apply run_locality P
  · intro d hdL hdR
    have hdL' : -(r : ℤ) ≤ d := by omega
    have hdR' : d ≤ r := by omega
    dsimp only [labels, canonical]
    rw [dif_pos (by omega), dif_pos (by omega)]
    apply congrArg some
    unfold PathPowerRamsey.window
    congr 1
    apply Fin.ext
    dsimp only
    omega
  · intro d _ _
    rfl

/-- The execution's communication is on actual edges of the path power;
the middle slot is the local self message. -/
theorem neighbor_iff {n t : ℕ} (u v : Fin n) :
    (PathPowerTreewidth.graph n t).Adj u v ↔
      u ≠ v ∧ ∃ p : Ports t, (v.val : ℤ) = u.val + delta p := by
  constructor
  · intro h
    refine ⟨h.1, ⟨⟨(v.val : ℤ) - u.val + t |>.toNat, by have h' := h.2; omega⟩, ?_⟩⟩
    dsimp [delta]
    have h' := h.2
    omega
  · rintro ⟨hne, p, hp⟩
    have hb := delta_bounds p
    exact ⟨hne, by omega, by omega⟩

end Paper.LineLocalWindow
