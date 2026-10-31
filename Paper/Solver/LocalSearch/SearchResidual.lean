import Paper.Solver.LocalSearch.SearchZero
import Paper.Solver.LocalSearch.ExactSearch

/-! Real local residual update for one selected candidate. It reads only
own ID/N and own demand; the graph appears only in evaluation/correctness. -/
namespace Paper.SearchResidual
open BroadcastModel
variable {V : Type} [DecidableEq V]

def localUpdate {B q : ℕ} (r : V) (N : Finset V) (u : V) (s : TerminalProtocol.Input V B q) :
    TerminalProtocol.Input V B q :=
  ⟨s.active, s.cost, ⟨s.value.val - if u = r ∨ u ∈ N then 1 else 0,
    lt_of_le_of_lt (Nat.sub_le _ _) s.value.isLt⟩⟩

def program {B q : ℕ} (t : CostTag.Tag V B) :
    Program V (TerminalProtocol.Input V B q) (TerminalProtocol.Input V B q) :=
  .local fun r N s => localUpdate r N (SolutionWord.id t) s

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def values {q : ℕ} (u : V) (b : V → Fin (q + 1)) (r : V) : Fin (q + 1) :=
  ⟨(b r).val - if u ∈ SevenFoundation.closed G r then 1 else 0,
    lt_of_le_of_lt (Nat.sub_le _ _) (b r).isLt⟩

theorem run_value {B q : ℕ} (t : CostTag.Tag V B) (s : V → TerminalProtocol.Input V B q) (r : V) :
    ((program t).run G s r).value.val = (s r).value.val -
      if SolutionWord.id t ∈ SevenFoundation.closed G r then 1 else 0 := by
  simp [program, Program.run, localUpdate, SevenFoundation.mem_closed, SimpleGraph.mem_neighborFinset]

theorem metadata {B q : ℕ} (t : CostTag.Tag V B) (s : V → TerminalProtocol.Input V B q) (r : V) :
    ((program t).run G s r).active = (s r).active ∧
      ((program t).run G s r).cost = (s r).cost := ⟨rfl, rfl⟩

theorem run_values {B q : ℕ} (t : CostTag.Tag V B) (s : V → TerminalProtocol.Input V B q)
    (b : V → Fin (q + 1)) (hb : ∀ r, (s r).value = b r) :
    ∀ r, ((program t).run G s r).value = values G (SolutionWord.id t) b r := by
  intro r
  apply Fin.ext
  rw [run_value, hb r]
  rfl

theorem zero_outside {q : ℕ} (u : V) (b : V → Fin (q + 1)) (H : Finset V)
    (hb : ∀ r, r ∉ H → (b r).val = 0) :
    ∀ r, r ∉ H → (values G u b r).val = 0 := by
  intro r hr
  simp [values, hb r hr]

theorem erase_feasible {q : ℕ} (u : V) (b : V → Fin (q + 1)) (m : ℕ) (p : V → ℕ)
    (hsize : ∑ r, p r ≤ m + 1)
    (hcover : ∀ r, (b r).val ≤ ∑ v ∈ SevenFoundation.closed G r, p v) (hu : 0 < p u) :
    (∑ r, IntegralTable.erase p u r) ≤ m ∧
      ∀ r, (values G u b r).val ≤ ∑ v ∈ SevenFoundation.closed G r, IntegralTable.erase p u v :=
  ExactSearch.valid_eraseOne G (fun r => (b r).val) u m p ⟨hsize, hcover⟩ hu

theorem covers_cons {B q : ℕ} (t : CostTag.Tag V B) (w : SolutionWord.Word V B)
    (b : V → Fin (q + 1))
    (hcover : ∀ r, (values G (SolutionWord.id t) b r).val ≤
      ∑ v ∈ SevenFoundation.closed G r, SolutionWord.copies w v) :
    ∀ r, (b r).val ≤ ∑ v ∈ SevenFoundation.closed G r, SolutionWord.copies (t :: w) v := by
  have he : SolutionWord.copies (t :: w) = ExactSearch.addOne (SolutionWord.id t) (SolutionWord.copies w) := by
    funext r
    simp only [SolutionWord.copies_cons, ExactSearch.addOne, Nat.add_comm]
  rw [he]
  exact (ExactSearch.covers_addOne_iff G (fun r => (b r).val) (SolutionWord.id t) (SolutionWord.copies w)).mpr hcover

theorem consistent_cons {B : ℕ} (c : V → Fin (B + 1)) (t : CostTag.Tag V B) (w : SolutionWord.Word V B)
    (ht : (ofLex t).1 = c (SolutionWord.id t)) (hw : SolutionWord.Consistent c w) :
    SolutionWord.Consistent c (t :: w) := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact ht
  · exact hw a ha

theorem cons_cost_bound {B : ℕ} (c : V → Fin (B + 1)) (t : CostTag.Tag V B) (w : SolutionWord.Word V B)
    (ht : (ofLex t).1 = c (SolutionWord.id t)) (p : V → ℕ) (hp : 0 < p (SolutionWord.id t))
    (hw : SolutionWord.cost w ≤ IntegralTable.cost (fun v => (c v).val) (IntegralTable.erase p (SolutionWord.id t))) :
    SolutionWord.cost (t :: w) ≤ IntegralTable.cost (fun v => (c v).val) p := by
  have hprice : SolutionWord.tagPrice t = (c (SolutionWord.id t)).val := congrArg Fin.val ht
  have hc := IntegralTable.cost_restore (fun v => (c v).val) p (SolutionWord.id t) hp
  rw [SolutionWord.cost_cons]
  dsimp only at hc
  rw [← hprice] at hc
  omega

theorem rounds {B q : ℕ} (t : CostTag.Tag V B) : (program (q := q) t).rounds = 0 := rfl

theorem maxBits {B q : ℕ} (t : CostTag.Tag V B) : (program (q := q) t).maxBits = 0 := rfl
end Paper.SearchResidual
