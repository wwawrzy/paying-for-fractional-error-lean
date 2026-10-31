import Paper.Solver.LocalSearch.RecursiveSearch

/-! Semantic specification for actual bounded search programs. These are
proof contracts, not runtime inputs; concrete base/terminal/control programs
discharge them in the recursive correctness theorem. -/
namespace Paper.SearchSpec
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Valid (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) : Prop :=
  w.length ≤ m ∧ (∀ t ∈ w, SolutionWord.id t ∈ H) ∧ SolutionWord.Consistent c w ∧
    ∀ r, (b r).val ≤ ∑ u ∈ SevenFoundation.closed G r, SolutionWord.copies w u

structure Spec {B q : ℕ}
    (P : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (H : Finset V) (c : V → Fin (B + 1)) (b : V → Fin (q + 1)) (m : ℕ)
    (s : V → TerminalProtocol.Input V B q) : Prop where
  sound : ∀ v ∈ H, ∀ w, P.run G s v = some w → Valid G H c b m w
  complete : ∀ p : V → ℕ, (∑ u, p u) ≤ m → (∀ u, u ∉ H → p u = 0) →
    (∀ r, (b r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) →
      ∀ v ∈ H, ∃ w, P.run G s v = some w ∧ SolutionWord.cost w ≤ IntegralTable.cost (fun u => (c u).val) p
  uniform : ∀ v w, v ∈ H → w ∈ H → P.run G s v = P.run G s w

theorem valid_cons (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (t : CostTag.Tag V B) (w : SolutionWord.Word V B)
    (htH : SolutionWord.id t ∈ H) (htc : (ofLex t).1 = c (SolutionWord.id t))
    (hw : Valid G H c (SearchResidual.values G (SolutionWord.id t) b) m w) :
    Valid G H c b (m + 1) (t :: w) := by
  refine ⟨by simpa only [List.length_cons] using Nat.add_le_add_right hw.1 1,
    ?_, SearchResidual.consistent_cons c t w htc hw.2.2.1,
    SearchResidual.covers_cons G t w b hw.2.2.2⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact htH
  · exact hw.2.1 a ha

theorem erase_support (H : Finset V) (p : V → ℕ) (u : V) (hp : ∀ v, v ∉ H → p v = 0) :
    ∀ v, v ∉ H → IntegralTable.erase p u v = 0 := by
  intro v hv
  simp [IntegralTable.erase, hp v hv]

theorem copies_bound (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) (hw : Valid G H c b m w) :
    (∑ v, SolutionWord.copies w v) ≤ m := by
  rw [SolutionWord.total_size]
  exact hw.1

theorem copies_support (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) (hw : Valid G H c b m w) :
    ∀ v, v ∉ H → SolutionWord.copies w v = 0 := by
  intro v hv
  apply TableInterpretation.support (SolutionWord.entries w) H ?_ hv
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  exact hw.2.1 t ht

theorem exact_cost (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) (hw : Valid G H c b m w) :
    IntegralTable.cost (fun v => (c v).val) (SolutionWord.copies w) = SolutionWord.cost w :=
  SolutionWord.cost_eq c w hw.2.2.1
end Paper.SearchSpec
