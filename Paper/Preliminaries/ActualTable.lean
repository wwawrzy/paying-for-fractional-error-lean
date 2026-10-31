import Paper.Preliminaries.TerminalAlphabet

/-! The concrete table returned by the broadcast program is well formed,
has bounded size, and contains a row/cost replacement for every actual
physical candidate. No representative table is an input assumption. -/
namespace Paper.ActualTable
open BroadcastModel TabularSearch
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def table {b : ℕ} (C : BitCode V b) (roundBound B T : ℕ) (s : V → MaskQuery.Input V B) (v : V) :=
  ((TerminalAlphabet.program C roundBound B T).run G s v).2

variable (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
variable (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
variable (k : ℕ) (hsize : I.card ≤ k) (B T : ℕ) (l : List V) (cost : V → Fin (B + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → MaskQuery.Input V B)
variable (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
variable (hc : ∀ v, (s v).cost = cost v)
variable (hl : ∀ v ∈ PhysicalTasks.vertices G D R L Q I, (s v).demands = l)
include hI hsize ha hc hl

theorem wellformed (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (e : Entry V T) (he : e ∈ table G C (4 * k) B T s v) :
    e.id ∈ PhysicalTasks.vertices G D R L Q I ∧
      e.row = LocalDemandMask.mask T l e.id (G.neighborFinset e.id) ∧ e.price = (cost e.id).val := by
  dsimp only [table] at he
  rw [TerminalAlphabet.physical_alphabet G C D R L Q I hI k hsize B T l cost s ha hc hl v hv] at he
  obtain ⟨z, _, t, ht, hentry⟩ := (TerminalAlphabet.mem_alphabet_map _ _ e).mp he
  subst e
  have hm : MaskedMinimum.minimum
      ((MaskQuery.fiber G (PhysicalTasks.vertices G D R L Q I) T l z).image (CostTag.tag cost)) = some t := ht
  obtain ⟨hmem, hcost, _⟩ := CostTag.least_cost cost
    (MaskQuery.fiber G (PhysicalTasks.vertices G D R L Q I) T l z) hm
  exact ⟨(Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2.symm,
    congrArg Fin.val hcost⟩

theorem length_le (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) :
    (table G C (4 * k) B T s v).length ≤ 2 ^ T := by
  dsimp only [table]
  rw [TerminalAlphabet.physical_alphabet G C D R L Q I hI k hsize B T l cost s ha hc hl v hv]
  exact (TerminalAlphabet.length_map_le _ _).trans_eq (MaskRepresentatives.patterns_length T)

theorem representative (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (w : V) (hw : w ∈ PhysicalTasks.vertices G D R L Q I) :
    ∃ e ∈ table G C (4 * k) B T s v,
      e.row = LocalDemandMask.mask T l w (G.neighborFinset w) ∧ e.price ≤ (cost w).val := by
  let z := LocalDemandMask.mask T l w (G.neighborFinset w)
  have hwf : w ∈ MaskQuery.fiber G (PhysicalTasks.vertices G D R L Q I) T l z :=
    Finset.mem_filter.mpr ⟨hw, rfl⟩
  have him : CostTag.tag cost w ∈
      (MaskQuery.fiber G (PhysicalTasks.vertices G D R L Q I) T l z).image (CostTag.tag cost) :=
    Finset.mem_image.mpr ⟨w, hwf, rfl⟩
  obtain ⟨t, ht, hle⟩ := MaskedMinimum.minimum_le him
  refine ⟨TerminalAlphabet.ofTag z t, ?_, rfl, Prod.Lex.monotone_fst _ _ hle⟩
  dsimp only [table]
  rw [TerminalAlphabet.physical_alphabet G C D R L Q I hI k hsize B T l cost s ha hc hl v hv]
  exact (TerminalAlphabet.mem_alphabet_map _ _ _).mpr
    ⟨z, MaskRepresentatives.patterns_complete T z, t, ht, rfl⟩
end Paper.ActualTable
