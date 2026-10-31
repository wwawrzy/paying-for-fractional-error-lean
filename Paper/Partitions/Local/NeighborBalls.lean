import Mathlib.Data.Finset.Union
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Nat.Basic

/-! Computable finite dependency balls for an arbitrary local neighbor
function. No graph, vertex Fintype, symmetry or global enumeration needed. -/
namespace Paper.NeighborBalls
variable {V : Type} [DecidableEq V]

def ball (N : V → Finset V) (v : V) : ℕ → Finset V
  | 0 => {v}
  | r + 1 => insert v ((N v).biUnion (fun u => ball N u r))

theorem mem_zero (N : V → Finset V) (v u : V) : u ∈ ball N v 0 ↔ u = v := Finset.mem_singleton

theorem mem_succ (N : V → Finset V) (v u : V) (r : ℕ) :
    u ∈ ball N v (r + 1) ↔ u = v ∨ ∃ w ∈ N v, u ∈ ball N w r := by
  simp only [ball, Finset.mem_insert, Finset.mem_biUnion]

theorem self_mem (N : V → Finset V) (v : V) (r : ℕ) : v ∈ ball N v r := by
  cases r with
  | zero => exact Finset.mem_singleton_self _
  | succ r => exact Finset.mem_insert_self _ _

theorem step_subset (N : V → Finset V) (v : V) (r : ℕ) : ball N v r ⊆ ball N v (r + 1) := by
  induction r generalizing v with
  | zero =>
    intro u hu
    have he := (mem_zero N v u).mp hu
    subst u
    exact self_mem N v 1
  | succ r ih =>
    intro u hu
    rcases (mem_succ N v u r).mp hu with he | ⟨w, hw, hu⟩
    · exact (mem_succ N v u (r + 1)).mpr (Or.inl he)
    · exact (mem_succ N v u (r + 1)).mpr (Or.inr ⟨w, hw, ih w hu⟩)

theorem monotone (N : V → Finset V) (v : V) : Monotone (ball N v) :=
  monotone_nat_of_le_succ (fun r => step_subset N v r)

theorem neighbor_mem (N : V → Finset V) (v u : V) (hu : u ∈ N v) : u ∈ ball N v 1 :=
  (mem_succ N v u 0).mpr (Or.inr ⟨u, hu, self_mem N u 0⟩)

theorem subball (N : V → Finset V) (r s : ℕ) (v u : V) (hu : u ∈ ball N v r) :
    ball N u s ⊆ ball N v (r + s) := by
  induction r generalizing v u with
  | zero =>
    have he := (mem_zero N v u).mp hu
    subst u
    simpa only [Nat.zero_add] using (Finset.Subset.refl (ball N v s))
  | succ r ih =>
    rcases (mem_succ N v u r).mp hu with he | ⟨w, hw, hu⟩
    · subst u
      exact monotone N v (by omega : s ≤ r + 1 + s)
    · intro x hx
      have hh := (mem_succ N v x (r + s)).mpr (Or.inr ⟨w, hw, ih w u hu hx⟩)
      have hn : r + s + 1 = r + 1 + s := by omega
      simpa only [hn] using hh
end Paper.NeighborBalls
