import Paper.Preliminaries.TerminalAlphabet
import Paper.Solver.LocalSearch.GeneralCoveringRepresentativesCorrect

/-! The concrete table returned by the broadcast program is well formed,
has bounded size, and contains a row/cost replacement for every actual
physical candidate. No representative table is an input assumption. -/
namespace Paper.GeneralCoveringTable
open BroadcastModel TabularSearch
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def alphabetProgram {b : ℕ} (C : BitCode V b) (D B T : ℕ) :=
  Program.seq (GeneralCoveringRepresentatives.all C D B T)
    (.local fun _ _ s => (s.1, TerminalAlphabet.alphabet
      (GeneralCoveringRepresentatives.patterns T) s.2))

theorem rounds {b : ℕ} (C : BitCode V b) (D B T : ℕ) : (alphabetProgram C D B T).rounds = 2 ^ T * (4 * D + 1) := by
  simp only [alphabetProgram, GeneralCoveringRepresentatives.all,
    GeneralCoveringRepresentatives.start, Program.rounds,
    GeneralCoveringRepresentatives.rounds, GeneralCoveringRepresentatives.patterns_length,
    Nat.zero_add, Nat.add_zero]

theorem maxBits {b : ℕ} (C : BitCode V b) (D B T : ℕ) :
    (alphabetProgram C D B T).maxBits ≤ max (2 * b + B + 3) (D + 2) := by
  simp only [alphabetProgram, GeneralCoveringRepresentatives.all,
    GeneralCoveringRepresentatives.start, Program.maxBits, Nat.zero_max, Nat.max_zero]
  exact GeneralCoveringRepresentatives.maxBits C D B T _

theorem alphabet_correct (K : ActiveTask.Context G) {b : ℕ} (C : BitCode V b)
    (B T : ℕ) (l : List V) (targets : V → Finset V) (cost : V → Fin (B + 1)) (s : V → GeneralCoveringQuery.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = cost v) (hl : ∀ v ∈ K.vertices, (s v).demands = l)
    (htarget : ∀ v ∈ K.vertices, (s v).targets = targets v) :
    ∀ v ∈ K.vertices, ((alphabetProgram C K.diameter B T).run G s v).2 =
      TerminalAlphabet.alphabet (GeneralCoveringRepresentatives.patterns T) ((GeneralCoveringRepresentatives.patterns T).map
        (GeneralCoveringRepresentativesCorrect.answer G K B T l targets cost)) := by
  intro v hv
  exact congrArg (TerminalAlphabet.alphabet (GeneralCoveringRepresentatives.patterns T))
    (GeneralCoveringRepresentativesCorrect.all_correct G K B T l targets cost C s ha hc hl htarget v hv)

def table {b : ℕ} (C : BitCode V b) (roundBound B T : ℕ) (s : V → GeneralCoveringQuery.Input V B) (v : V) :=
  ((alphabetProgram C roundBound B T).run G s v).2

variable (K : ActiveTask.Context G) (B T : ℕ) (l : List V) (targets : V → Finset V) (cost : V → Fin (B + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → GeneralCoveringQuery.Input V B)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v)
variable (hl : ∀ v ∈ K.vertices, (s v).demands = l)
variable (htarget : ∀ v ∈ K.vertices, (s v).targets = targets v)
include ha hc hl htarget

theorem wellformed (v : V) (hv : v ∈ K.vertices)
    (e : Entry V T) (he : e ∈ table G C K.diameter B T s v) :
    e.id ∈ K.vertices ∧
      e.row = GeneralCoveringMask.mask T l (targets e.id) ∧ e.price = (cost e.id).val := by
  dsimp only [table] at he
  rw [alphabet_correct G K C B T l targets cost s ha hc hl htarget v hv] at he
  obtain ⟨z, _, t, ht, hentry⟩ := (TerminalAlphabet.mem_alphabet_map _ _ e).mp he
  subst e
  have hm : MaskedMinimum.minimum
      ((GeneralCoveringQuery.fiber K.vertices T l targets z).image (CostTag.tag cost)) = some t := ht
  obtain ⟨hmem, hcost, _⟩ := CostTag.least_cost cost
    (GeneralCoveringQuery.fiber K.vertices T l targets z) hm
  exact ⟨(Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2.symm,
    congrArg Fin.val hcost⟩

theorem length_le (v : V) (hv : v ∈ K.vertices) :
    (table G C K.diameter B T s v).length ≤ 2 ^ T := by
  dsimp only [table]
  rw [alphabet_correct G K C B T l targets cost s ha hc hl htarget v hv]
  exact (TerminalAlphabet.length_map_le _ _).trans_eq (GeneralCoveringRepresentatives.patterns_length T)

theorem representative (v : V) (hv : v ∈ K.vertices)
    (w : V) (hw : w ∈ K.vertices) :
    ∃ e ∈ table G C K.diameter B T s v,
      e.row = GeneralCoveringMask.mask T l (targets w) ∧ e.price ≤ (cost w).val := by
  let z := GeneralCoveringMask.mask T l (targets w)
  have hwf : w ∈ GeneralCoveringQuery.fiber K.vertices T l targets z :=
    Finset.mem_filter.mpr ⟨hw, rfl⟩
  have him : CostTag.tag cost w ∈
      (GeneralCoveringQuery.fiber K.vertices T l targets z).image (CostTag.tag cost) :=
    Finset.mem_image.mpr ⟨w, hwf, rfl⟩
  obtain ⟨t, ht, hle⟩ := MaskedMinimum.minimum_le him
  refine ⟨TerminalAlphabet.ofTag z t, ?_, rfl, Prod.Lex.monotone_fst _ _ hle⟩
  dsimp only [table]
  rw [alphabet_correct G K C B T l targets cost s ha hc hl htarget v hv]
  exact (TerminalAlphabet.mem_alphabet_map _ _ _).mpr
    ⟨z, GeneralCoveringRepresentatives.patterns_complete T z, t, ht, rfl⟩
end Paper.GeneralCoveringTable

#print axioms Paper.GeneralCoveringTable.wellformed
#print axioms Paper.GeneralCoveringTable.representative
