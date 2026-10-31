import Paper.Preliminaries.TerminalAlphabet
import Paper.Preliminaries.ActiveMaskRepresentatives

/-! The concrete table returned by the broadcast program is well formed,
has bounded size, and contains a row/cost replacement for every actual
physical candidate. No representative table is an input assumption. -/
namespace Paper.ActiveActualTable
open BroadcastModel TabularSearch
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem alphabet_correct (K : ActiveTask.Context G) {b : ℕ} (C : BitCode V b)
    (B T : ℕ) (l : List V) (cost : V → Fin (B + 1)) (s : V → MaskQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v) (hl : ∀ v ∈ K.vertices, (s v).demands = l) :
    ∀ v ∈ K.vertices, ((TerminalAlphabet.program C K.diameter B T).run G s v).2 =
      TerminalAlphabet.alphabet (MaskRepresentatives.patterns T) ((MaskRepresentatives.patterns T).map
        (ActiveMaskRepresentatives.answer G K B T l cost)) := by
  intro v hv
  exact congrArg (TerminalAlphabet.alphabet (MaskRepresentatives.patterns T))
    (ActiveMaskRepresentatives.all_correct G K B T l cost C s ha hc hl v hv)

def table {b : ℕ} (C : BitCode V b) (roundBound B T : ℕ) (s : V → MaskQuery.Input V B) (v : V) :=
  ((TerminalAlphabet.program C roundBound B T).run G s v).2

variable (K : ActiveTask.Context G) (B T : ℕ) (l : List V) (cost : V → Fin (B + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → MaskQuery.Input V B)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v)
variable (hl : ∀ v ∈ K.vertices, (s v).demands = l)
include ha hc hl

theorem wellformed (v : V) (hv : v ∈ K.vertices)
    (e : Entry V T) (he : e ∈ table G C K.diameter B T s v) :
    e.id ∈ K.vertices ∧
      e.row = LocalDemandMask.mask T l e.id (G.neighborFinset e.id) ∧ e.price = (cost e.id).val := by
  dsimp only [table] at he
  rw [alphabet_correct G K C B T l cost s ha hc hl v hv] at he
  obtain ⟨z, _, t, ht, hentry⟩ := (TerminalAlphabet.mem_alphabet_map _ _ e).mp he
  subst e
  have hm : MaskedMinimum.minimum
      ((MaskQuery.fiber G (K.vertices) T l z).image (CostTag.tag cost)) = some t := ht
  obtain ⟨hmem, hcost, _⟩ := CostTag.least_cost cost
    (MaskQuery.fiber G (K.vertices) T l z) hm
  exact ⟨(Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2.symm,
    congrArg Fin.val hcost⟩

theorem length_le (v : V) (hv : v ∈ K.vertices) :
    (table G C K.diameter B T s v).length ≤ 2 ^ T := by
  dsimp only [table]
  rw [alphabet_correct G K C B T l cost s ha hc hl v hv]
  exact (TerminalAlphabet.length_map_le _ _).trans_eq (MaskRepresentatives.patterns_length T)

theorem representative (v : V) (hv : v ∈ K.vertices)
    (w : V) (hw : w ∈ K.vertices) :
    ∃ e ∈ table G C K.diameter B T s v,
      e.row = LocalDemandMask.mask T l w (G.neighborFinset w) ∧ e.price ≤ (cost w).val := by
  let z := LocalDemandMask.mask T l w (G.neighborFinset w)
  have hwf : w ∈ MaskQuery.fiber G (K.vertices) T l z :=
    Finset.mem_filter.mpr ⟨hw, rfl⟩
  have him : CostTag.tag cost w ∈
      (MaskQuery.fiber G (K.vertices) T l z).image (CostTag.tag cost) :=
    Finset.mem_image.mpr ⟨w, hwf, rfl⟩
  obtain ⟨t, ht, hle⟩ := MaskedMinimum.minimum_le him
  refine ⟨TerminalAlphabet.ofTag z t, ?_, rfl, Prod.Lex.monotone_fst _ _ hle⟩
  dsimp only [table]
  rw [alphabet_correct G K C B T l cost s ha hc hl v hv]
  exact (TerminalAlphabet.mem_alphabet_map _ _ _).mpr
    ⟨z, MaskRepresentatives.patterns_complete T z, t, ht, rfl⟩
end Paper.ActiveActualTable
