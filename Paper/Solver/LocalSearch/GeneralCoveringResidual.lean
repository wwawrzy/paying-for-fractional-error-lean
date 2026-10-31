import Paper.Solver.LocalSearch.SearchResidual

/-! Residual updates for arbitrary local covering incidences. Candidate lists
are private local input, not messages. The physical heavy lists from the
existing search remain complete for this more restrictive covering relation. -/
namespace Paper.GeneralCoveringResidual
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [DecidableEq V]

structure Input (V : Type) (B q : ℕ) where
  base : TerminalProtocol.Input V B q
  /-- Demand-side incidence list C(r), supplied privately. -/
  candidates : Finset V
  /-- Candidate-side incidence list, known at the other endpoint of each edge. -/
  targets : Finset V

def localUpdate {B q : ℕ} (u : V) (s : Input V B q) : Input V B q :=
  ⟨⟨s.base.active, s.base.cost,
    ⟨s.base.value.val - if u ∈ s.candidates then 1 else 0,
      lt_of_le_of_lt (Nat.sub_le _ _) s.base.value.isLt⟩⟩, s.candidates, s.targets⟩

def program {B q : ℕ} (u : V) : Program V (Input V B q) (Input V B q) :=
  .local fun _ _ s => localUpdate u s

def values (C : V → Finset V) {q : ℕ} (u : V)
    (b : V → Fin (q + 1)) (r : V) : Fin (q + 1) :=
  ⟨(b r).val - if u ∈ C r then 1 else 0,
    lt_of_le_of_lt (Nat.sub_le _ _) (b r).isLt⟩

variable [Fintype V]

theorem run_values (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : V → Finset V) {B q : ℕ} (u : V) (s : V → Input V B q)
    (b : V → Fin (q + 1)) (hC : ∀ r, (s r).candidates = C r)
    (hb : ∀ r, (s r).base.value = b r) :
    ∀ r, ((program u).run G s r).base.value = values C u b r := by
  intro r
  apply Fin.ext
  change (s r).base.value.val - (if u ∈ (s r).candidates then 1 else 0) = _
  rw [hC r, hb r]
  rfl

theorem metadata (G : SimpleGraph V) [DecidableRel G.Adj]
    {B q : ℕ} (u : V) (s : V → Input V B q) (r : V) :
    ((program u).run G s r).base.active = (s r).base.active ∧
    ((program u).run G s r).base.cost = (s r).base.cost ∧
    ((program u).run G s r).candidates = (s r).candidates := ⟨rfl, rfl, rfl⟩

theorem covers_addOne_iff (C : V → Finset V) (b : V → ℕ) (u : V) (p : V → ℕ) :
    (∀ r, b r ≤ ∑ v ∈ C r, ExactSearch.addOne u p v) ↔
      ∀ r, b r - (if u ∈ C r then 1 else 0) ≤ ∑ v ∈ C r, p v := by
  simp_rw [ExactSearch.sum_addOne, Nat.sub_le_iff_le_add]

theorem erase_feasible (C : V → Finset V) {q : ℕ} (u : V)
    (b : V → Fin (q + 1)) (m : ℕ) (p : V → ℕ)
    (hsize : ∑ r, p r ≤ m + 1)
    (hcover : ∀ r, (b r).val ≤ ∑ v ∈ C r, p v) (hu : 0 < p u) :
    (∑ r, ExactSearch.eraseOne u p r) ≤ m ∧
      ∀ r, (values C u b r).val ≤ ∑ v ∈ C r, ExactSearch.eraseOne u p v := by
  have heq := ExactSearch.add_erase u p hu
  have hs := ExactSearch.sum_addOne (Finset.univ : Finset V) u (ExactSearch.eraseOne u p)
  rw [heq] at hs
  simp only [Finset.mem_univ, if_true] at hs
  refine ⟨by omega, ?_⟩
  exact (covers_addOne_iff C (fun r => (b r).val) u (ExactSearch.eraseOne u p)).mp
    (by rw [heq]; exact hcover)

theorem covers_cons (C : V → Finset V) {B q : ℕ}
    (t : CostTag.Tag V B) (w : SolutionWord.Word V B) (b : V → Fin (q + 1))
    (hcover : ∀ r, (values C (SolutionWord.id t) b r).val ≤
      ∑ v ∈ C r, SolutionWord.copies w v) :
    ∀ r, (b r).val ≤ ∑ v ∈ C r, SolutionWord.copies (t :: w) v := by
  have he : SolutionWord.copies (t :: w) =
      ExactSearch.addOne (SolutionWord.id t) (SolutionWord.copies w) := by
    funext r
    simp only [SolutionWord.copies_cons, ExactSearch.addOne, Nat.add_comm]
  rw [he]
  exact (covers_addOne_iff C (fun r => (b r).val) (SolutionWord.id t)
    (SolutionWord.copies w)).mpr hcover

/-- Every bounded completion for the restricted incidences still hits the
existing physical heavy list. No new graph counting theorem is required. -/
theorem completion_hits_heavy (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : V → Finset V) (A : Finset V) (hA : A.Nonempty)
    (hlocal : ∀ r ∈ A, C r ⊆ closed G r) (m : ℕ) (hm : 1 ≤ m)
    (p : V → ℕ) (hsize : ∑ v, p v ≤ m)
    (hcover : ∀ r ∈ A, 1 ≤ ∑ v ∈ C r, p v) :
    ∃ v ∈ LocalSearchBounds.heavy G A m, 0 < p v := by
  apply LocalSearchBounds.completion_hits_heavy G A hA m hm p hsize
  intro r hr
  exact (hcover r hr).trans (Finset.sum_le_sum_of_subset (hlocal r hr))

theorem zero_outside (C : V → Finset V) {q : ℕ} (u : V)
    (b : V → Fin (q + 1)) (H : Finset V) (hb : ∀ r, r ∉ H → (b r).val = 0) :
    ∀ r, r ∉ H → (values C u b r).val = 0 := by
  intro r hr
  simp [values, hb r hr]

theorem rounds {B q : ℕ} (u : V) : (program (B := B) (q := q) u).rounds = 0 := rfl

theorem maxBits {B q : ℕ} (u : V) : (program (B := B) (q := q) u).maxBits = 0 := rfl

end Paper.GeneralCoveringResidual

#print axioms Paper.GeneralCoveringResidual.erase_feasible
#print axioms Paper.GeneralCoveringResidual.completion_hits_heavy
