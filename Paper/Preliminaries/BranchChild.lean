import Paper.Solver.LocalSearch.SearchSpec

/-! Physical semantics of the private input supplied to an actual child
call. Shared candidate IDs are required only on active task vertices;
inactive zero demands stay zero for any padded-slot contents. -/
namespace Paper.BranchChild
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem metadata {B q : ℕ} (j : ℕ) (s : V → BranchLoop.State V B q) (v : V) :
    (BranchLoop.childState G j s v).active = (s v).input.active ∧
      (BranchLoop.childState G j s v).cost = (s v).input.cost := by
  dsimp only [BranchLoop.childState, BranchLoop.childInput]
  cases h : (s v).info.candidates[j]? <;> exact ⟨rfl, rfl⟩

theorem value_le {B q : ℕ} (j : ℕ) (s : V → BranchLoop.State V B q) (v : V) :
    (BranchLoop.childState G j s v).value.val ≤ (s v).input.value.val := by
  dsimp only [BranchLoop.childState, BranchLoop.childInput]
  cases h : (s v).info.candidates[j]? with
  | none => exact le_rfl
  | some t => exact Nat.sub_le _ _

theorem values_some {B q : ℕ} (H : Finset V) (j : ℕ) (s : V → BranchLoop.State V B q)
    (b : V → Fin (q + 1)) (hb : ∀ u, (s u).input.value = b u)
    (hz : ∀ u, u ∉ H → (b u).val = 0)
    (hi : ∀ u v, u ∈ H → v ∈ H → (s u).info = (s v).info)
    (v : V) (hv : v ∈ H) (t : CostTag.Tag V B) (ht : (s v).info.candidates[j]? = some t) :
    ∀ r, (BranchLoop.childState G j s r).value = SearchResidual.values G (SolutionWord.id t) b r := by
  intro r
  by_cases hr : r ∈ H
  · have hh : (s r).info = (s v).info := hi r v hr hv
    have he : BranchLoop.childState G j s r =
        (SearchResidual.program t).run G (fun u => (s u).input) r := by
      dsimp only [BranchLoop.childState, BranchLoop.childInput]
      rw [hh, ht]
      rfl
    rw [he]
    exact SearchResidual.run_values G t (fun u => (s u).input) b hb r
  · apply Fin.ext
    have hle := value_le G j s r
    rw [hb r] at hle
    have hb0 := hz r hr
    have hred := SearchResidual.zero_outside G (SolutionWord.id t) b H hz r hr
    rw [hred]
    omega

theorem choice_some {B q : ℕ}
    (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → BranchLoop.State V B q) (v : V) (t : CostTag.Tag V B)
    (ht : (s v).info.candidates[j]? = some t) :
    BranchLoop.choice G P j s v = (P.run G (BranchLoop.childState G j s) v).map (List.cons t) := by
  simp only [BranchLoop.choice, BranchLoop.proposal, ht, Option.bind_some]

theorem choice_none {B q : ℕ}
    (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → BranchLoop.State V B q) (v : V)
    (ht : (s v).info.candidates[j]? = none) : BranchLoop.choice G P j s v = none := by
  simp only [BranchLoop.choice, BranchLoop.proposal, ht, Option.bind_none]
end Paper.BranchChild
