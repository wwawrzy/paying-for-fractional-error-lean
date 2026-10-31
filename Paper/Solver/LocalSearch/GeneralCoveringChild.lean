import Paper.Solver.LocalSearch.GeneralCoveringParent

/-! Physical semantics of the private input supplied to an actual child
call. Shared candidate IDs are required only on active task vertices;
inactive zero demands stay zero for any padded-slot contents. -/
namespace Paper.GeneralCoveringChild
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem metadata {B q : ℕ} (j : ℕ) (s : V → GeneralCoveringLoop.State V B q) (v : V) :
    (GeneralCoveringLoop.childState G j s v).base.active = (s v).input.base.active ∧
      (GeneralCoveringLoop.childState G j s v).base.cost = (s v).input.base.cost ∧
      (GeneralCoveringLoop.childState G j s v).candidates = (s v).input.candidates ∧
      (GeneralCoveringLoop.childState G j s v).targets = (s v).input.targets := by
  dsimp only [GeneralCoveringLoop.childState, GeneralCoveringLoop.childInput]
  cases h : (s v).info.candidates[j]? <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem value_le {B q : ℕ} (j : ℕ) (s : V → GeneralCoveringLoop.State V B q) (v : V) :
    (GeneralCoveringLoop.childState G j s v).base.value.val ≤ (s v).input.base.value.val := by
  dsimp only [GeneralCoveringLoop.childState, GeneralCoveringLoop.childInput]
  cases h : (s v).info.candidates[j]? with
  | none => exact le_rfl
  | some t => exact Nat.sub_le _ _

theorem values_some (cover : V → Finset V) {B q : ℕ} (H : Finset V) (j : ℕ) (s : V → GeneralCoveringLoop.State V B q)
    (b : V → Fin (q + 1)) (hb : ∀ u, (s u).input.base.value = b u)
    (hC : ∀ u, (s u).input.candidates = cover u)
    (hz : ∀ u, u ∉ H → (b u).val = 0)
    (hi : ∀ u v, u ∈ H → v ∈ H → (s u).info = (s v).info)
    (v : V) (hv : v ∈ H) (t : CostTag.Tag V B) (ht : (s v).info.candidates[j]? = some t) :
    ∀ r, (GeneralCoveringLoop.childState G j s r).base.value = GeneralCoveringResidual.values cover (SolutionWord.id t) b r := by
  intro r
  by_cases hr : r ∈ H
  · have hh : (s r).info = (s v).info := hi r v hr hv
    have he : GeneralCoveringLoop.childState G j s r =
        (GeneralCoveringResidual.program (SolutionWord.id t)).run G (fun u => (s u).input) r := by
      dsimp only [GeneralCoveringLoop.childState, GeneralCoveringLoop.childInput]
      rw [hh, ht]
      rfl
    rw [he]
    exact GeneralCoveringResidual.run_values G cover (SolutionWord.id t) (fun u => (s u).input) b hC hb r
  · apply Fin.ext
    have hle := value_le G j s r
    rw [hb r] at hle
    have hb0 := hz r hr
    have hred := GeneralCoveringResidual.zero_outside cover (SolutionWord.id t) b H hz r hr
    rw [hred]
    omega

theorem choice_some {B q : ℕ}
    (P : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → GeneralCoveringLoop.State V B q) (v : V) (t : CostTag.Tag V B)
    (ht : (s v).info.candidates[j]? = some t) :
    GeneralCoveringLoop.choice G P j s v = (P.run G (GeneralCoveringLoop.childState G j s) v).map (List.cons t) := by
  simp only [GeneralCoveringLoop.choice, GeneralCoveringLoop.proposal, ht, Option.bind_some]

theorem choice_none {B q : ℕ}
    (P : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (j : ℕ) (s : V → GeneralCoveringLoop.State V B q) (v : V)
    (ht : (s v).info.candidates[j]? = none) : GeneralCoveringLoop.choice G P j s v = none := by
  simp only [GeneralCoveringLoop.choice, GeneralCoveringLoop.proposal, ht, Option.bind_none]
end Paper.GeneralCoveringChild
