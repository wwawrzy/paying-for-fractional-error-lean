import Paper.Solver.LocalSearch.GeneralCoveringResidual

/-! Semantic specification for actual bounded search programs. These are
proof contracts, not runtime inputs; concrete base/terminal/control programs
discharge them in the recursive correctness theorem. -/
namespace Paper.GeneralCoveringSpec
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (cover : V → Finset V)

def Valid (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) : Prop :=
  w.length ≤ m ∧ (∀ t ∈ w, SolutionWord.id t ∈ H) ∧ SolutionWord.Consistent c w ∧
    ∀ r, (b r).val ≤ ∑ u ∈ cover r, SolutionWord.copies w u

structure Spec (G : SimpleGraph V) [DecidableRel G.Adj] {B q : ℕ}
    (P : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (H : Finset V) (c : V → Fin (B + 1)) (b : V → Fin (q + 1)) (m : ℕ)
    (s : V → GeneralCoveringResidual.Input V B q) : Prop where
  sound : ∀ v ∈ H, ∀ w, P.run G s v = some w → Valid cover H c b m w
  complete : ∀ p : V → ℕ, (∑ u, p u) ≤ m → (∀ u, u ∉ H → p u = 0) →
    (∀ r, (b r).val ≤ ∑ u ∈ cover r, p u) →
      ∀ v ∈ H, ∃ w, P.run G s v = some w ∧ SolutionWord.cost w ≤ IntegralTable.cost (fun u => (c u).val) p
  uniform : ∀ v w, v ∈ H → w ∈ H → P.run G s v = P.run G s w

theorem valid_cons (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (t : CostTag.Tag V B) (w : SolutionWord.Word V B)
    (htH : SolutionWord.id t ∈ H) (htc : (ofLex t).1 = c (SolutionWord.id t))
    (hw : Valid cover H c (GeneralCoveringResidual.values cover (SolutionWord.id t) b) m w) :
    Valid cover H c b (m + 1) (t :: w) := by
  refine ⟨by simpa only [List.length_cons] using Nat.add_le_add_right hw.1 1,
    ?_, SearchResidual.consistent_cons c t w htc hw.2.2.1,
    GeneralCoveringResidual.covers_cons cover t w b hw.2.2.2⟩
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact htH
  · exact hw.2.1 a ha

omit cover in
theorem erase_support (H : Finset V) (p : V → ℕ) (u : V) (hp : ∀ v, v ∉ H → p v = 0) :
    ∀ v, v ∉ H → IntegralTable.erase p u v = 0 := by
  intro v hv
  simp [IntegralTable.erase, hp v hv]

theorem copies_bound (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) (hw : Valid cover H c b m w) :
    (∑ v, SolutionWord.copies w v) ≤ m := by
  rw [SolutionWord.total_size]
  exact hw.1

theorem copies_support (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) (hw : Valid cover H c b m w) :
    ∀ v, v ∉ H → SolutionWord.copies w v = 0 := by
  intro v hv
  apply TableInterpretation.support (SolutionWord.entries w) H ?_ hv
  intro e he
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp he
  exact hw.2.1 t ht

theorem exact_cost (H : Finset V) {B q : ℕ} (c : V → Fin (B + 1)) (b : V → Fin (q + 1))
    (m : ℕ) (w : SolutionWord.Word V B) (hw : Valid cover H c b m w) :
    IntegralTable.cost (fun v => (c v).val) (SolutionWord.copies w) = SolutionWord.cost w :=
  SolutionWord.cost_eq c w hw.2.2.1
/-- Positive costs exclude candidates covering no positive row from every
returned optimum, even when physical heavy lists contain such candidates. -/
theorem used_is_admissible (G : SimpleGraph V) [DecidableRel G.Adj] {B q : ℕ}
    (P : Program V (GeneralCoveringResidual.Input V B q) (Option (SolutionWord.Word V B)))
    (H : Finset V) (c : V → Fin (B + 1)) (b : V → Fin (q + 1)) (m : ℕ)
    (s : V → GeneralCoveringResidual.Input V B q) (h : Spec cover G P H c b m s)
    (hc : ∀ u, 0 < (c u).val) (v : V) (hv : v ∈ H) (w : SolutionWord.Word V B)
    (hw : P.run G s v = some w) (u : V) (hu : 0 < SolutionWord.copies w u) :
    ∃ r, 0 < (b r).val ∧ u ∈ cover r := by
  by_contra hn
  have hn' : ∀ r, 0 < (b r).val → u ∉ cover r := by
    intro r hr hur
    exact hn ⟨r, hr, hur⟩
  let p := SolutionWord.copies w
  let e := IntegralTable.erase p u
  have hvalid := h.sound v hv w hw
  have hsize : (∑ r, e r) ≤ m := by
    apply (Finset.sum_le_sum (fun r _ => IntegralTable.erase_le p u r)).trans
    exact copies_bound cover H c b m w hvalid
  have hsup : ∀ r, r ∉ H → e r = 0 :=
    erase_support H p u (copies_support cover H c b m w hvalid)
  have hcover : ∀ r, (b r).val ≤ ∑ z ∈ cover r, e z := by
    intro r
    by_cases hr : 0 < (b r).val
    · have hs := ExactSearch.sum_addOne (cover r) u (ExactSearch.eraseOne u p)
      rw [ExactSearch.add_erase u p hu, if_neg (hn' r hr), Nat.add_zero] at hs
      exact (hvalid.2.2.2 r).trans_eq hs
    · have hz : (b r).val = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  obtain ⟨w', hw', hcost⟩ := h.complete e hsize hsup hcover v hv
  have heq : w' = w := Option.some.inj (hw'.symm.trans hw)
  subst w'
  have hrestore := IntegralTable.cost_restore (fun z => (c z).val) p u hu
  have hprice := exact_cost cover H c b m w hvalid
  have hpositive := hc u
  dsimp only [e, p] at hcost
  dsimp only [p] at hrestore
  rw [hprice] at hrestore
  omega

end Paper.GeneralCoveringSpec

#print axioms Paper.GeneralCoveringSpec.valid_cons

#print axioms Paper.GeneralCoveringSpec.used_is_admissible
