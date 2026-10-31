import Paper.Solver.LocalSearch.GeneralCoveringTerminalDataCorrect
import Paper.Solver.LocalSearch.GeneralCoveringSpec
import Paper.Preliminaries.ActiveTerminalProtocol

/-! Small-demand terminal from private directed incidences. The demand IDs,
residual values and cost/ID representatives are collected by actual programs. -/
namespace Paper.GeneralCoveringTerminal
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringResidual.Input

def prepare (B q : ℕ) : Program V (Input V B q)
    ((Bool × Bool) × Input V B q) :=
  .local fun _ _ s => (TerminalProtocol.selectionInput s.base, s)

def dataInput {B q : ℕ} (chosen : SelectProtocol.State V) (s : Input V B q) :
    GeneralCoveringTerminalData.Input V B q :=
  ⟨s.base.active, s.base.cost, s.base.value, chosen.chosen, s.targets⟩

def prepareData (B q : ℕ) : Program V (SelectProtocol.State V × Input V B q)
    (GeneralCoveringTerminalData.Input V B q) := .local fun _ _ s => dataInput s.1 s.2

def entriesProgram {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :=
  Program.seq (prepare B q) (.seq
    (ProgramMemory.carry (SelectProtocol.program C D T)) (.seq (prepareData B q)
      (GeneralCoveringTerminalData.program C D B q T m)))

def program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :=
  Program.seq (entriesProgram C D B q T m)
    (.local fun _ _ ans => ans.map (SolutionWord.fromEntries B))

variable [Fintype V]

theorem rounds {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) : (program C D B q T m).rounds = (T + 2 ^ T + 1) * (4 * D + 1) := by
  simp only [program, entriesProgram, prepare, prepareData, Program.rounds, ProgramMemory.rounds,
    SelectCorrect.rounds, GeneralCoveringTerminalData.rounds]
  ring

theorem maxBits {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) : (program C D B q T m).maxBits ≤
    max (b + T * (q + 1) + 1) (max (2 * b + B + 3) (D + 2)) := by
  have hs := SelectCorrect.maxBits C D T
  have ht := GeneralCoveringTerminalData.maxBits C D B q T m
  simp only [program, entriesProgram, prepare, prepareData, Program.maxBits,
    ProgramMemory.maxBits, Nat.zero_max, Nat.max_zero]
  apply max_le _ ht
  apply hs.trans
  apply max_le
  · exact (by omega : 2 * b + 2 ≤ 2 * b + B + 3) |>.trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (le_max_right _ _).trans (le_max_right _ _)
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def dataState {b : ℕ} (C : BitCode V b) (D B q T : ℕ) (s : V → Input V B q) (v : V) :=
  dataInput ((SelectProtocol.program C D T).run G
    (fun u => TerminalProtocol.selectionInput (s u).base) v) (s v)

theorem run_entries {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) (s : V → Input V B q) :
    (entriesProgram C D B q T m).run G s =
      (GeneralCoveringTerminalData.program C D B q T m).run G (dataState G C D B q T s) := by
  change (GeneralCoveringTerminalData.program C D B q T m).run G
    ((prepareData B q).run G ((ProgramMemory.carry (SelectProtocol.program C D T)).run G
      (fun v => (TerminalProtocol.selectionInput (s v).base, s v)))) = _
  rw [ProgramMemory.run]
  rfl

theorem run_program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) (s : V → Input V B q) (v : V) :
    (program C D B q T m).run G s v =
      ((entriesProgram C D B q T m).run G s v).map (SolutionWord.fromEntries B) := rfl

variable (K : ActiveTask.Context G) (B q T : ℕ) (cover targets : V → Finset V)
variable (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → Input V B q)
variable (ha : ∀ v, (s v).base.active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).base.cost = cost v) (hb : ∀ v, (s v).base.value = multiplicity v)
variable (htarget : ∀ v ∈ K.vertices, (s v).targets = targets v)
include ha hc hb htarget

theorem chosen (v : V) (hv : v ∈ K.vertices) :
    (dataState G C K.diameter B q T s v).demands =
      TerminalProtocolCorrect.demandList K.vertices multiplicity T :=
  ActiveTerminalProtocol.chosen G K B q T cost multiplicity C
    (fun u => (s u).base) ha hc hb v hv

theorem data_run (m : ℕ) (v : V) (hv : v ∈ K.vertices) :
    (entriesProgram C K.diameter B q T m).run G s v = TabularSearch.choose
      (GeneralCoveringTable.table G C K.diameter B T
        (fun u => GeneralCoveringTerminalData.maskInput (dataState G C K.diameter B q T s u)) v) m
      (DemandValues.values T (TerminalProtocolCorrect.demandList K.vertices multiplicity T) multiplicity) := by
  rw [run_entries]
  exact GeneralCoveringTerminalDataCorrect.run_correct G K B q T
    (TerminalProtocolCorrect.demandList K.vertices multiplicity T) targets cost multiplicity C
    (dataState G C K.diameter B q T s) ha hc hb
    (chosen G K B q T targets cost multiplicity C s ha hc hb htarget)
    (fun r hr => TerminalProtocolCorrect.list_inside _ multiplicity T hr) htarget m v hv

theorem entry_meta (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (w : List (TabularSearch.Entry V T))
    (hw : (entriesProgram C K.diameter B q T m).run G s v = some w) :
    ∀ e ∈ w, e.id ∈ K.vertices ∧ e.price = (cost e.id).val := by
  rw [data_run G K B q T targets cost multiplicity C s ha hc hb htarget m v hv] at hw
  have hmem := (TabularSearch.choose_sound _ m _ hw).2.1
  intro e he
  have hh := GeneralCoveringTable.wellformed G K B T
    (TerminalProtocolCorrect.demandList K.vertices multiplicity T) targets cost C
    (fun u => GeneralCoveringTerminalData.maskInput (dataState G C K.diameter B q T s u))
    ha hc (chosen G K B q T targets cost multiplicity C s ha hc hb htarget) htarget v hv e (hmem e he)
  exact ⟨hh.1, hh.2.2⟩

include hinc in
theorem sound (hsmall : (TerminalProtocolCorrect.demands K.vertices multiplicity).card ≤ T)
    (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ K.vertices) (w : SolutionWord.Word V B)
    (hw : (program C K.diameter B q T m).run G s v = some w) :
    GeneralCoveringSpec.Valid cover K.vertices cost multiplicity m w := by
  rw [run_program] at hw
  cases hr : (entriesProgram C K.diameter B q T m).run G s v with
  | none => simp [hr] at hw
  | some x =>
    simp only [hr, Option.map_some, Option.some.injEq] at hw
    subst w
    have hentry := hr
    rw [run_entries] at hr
    have hs := GeneralCoveringTerminalDataCorrect.sound G K B q T
      (TerminalProtocolCorrect.demandList K.vertices multiplicity T) cover targets hinc cost multiplicity C
      (dataState G C K.diameter B q T s) ha hc hb
      (chosen G K B q T targets cost multiplicity C s ha hc hb htarget)
      (fun r hr => TerminalProtocolCorrect.list_inside _ multiplicity T hr) htarget
      (MinimumList.run_length _ T)
      (fun r hr => TerminalProtocolCorrect.zero_outside _ multiplicity T hsmall hz hr) m v hv x hr
    have hm := entry_meta G K B q T targets cost multiplicity C s ha hc hb htarget m v hv x hentry
    refine ⟨?_, ?_, SolutionWord.consistent_fromEntries cost x (fun e he => (hm e he).2), ?_⟩
    · rw [SolutionWord.length_fromEntries, ← TableInterpretation.total_size]
      exact hs.1
    · intro t ht
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      exact (hm e he).1
    · simpa only [SolutionWord.copies_fromEntries] using hs.2.2.1

include hinc in
theorem complete (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ K.vertices → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ cover r, p u) :
    ∃ w, (program C K.diameter B q T m).run G s v = some w ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  have hx := GeneralCoveringTerminalDataCorrect.complete G K B q T
    (TerminalProtocolCorrect.demandList K.vertices multiplicity T) cover targets hinc cost multiplicity C
    (dataState G C K.diameter B q T s) ha hc hb
    (chosen G K B q T targets cost multiplicity C s ha hc hb htarget)
    (fun r hr => TerminalProtocolCorrect.list_inside _ multiplicity T hr) htarget m v hv p hsizep hsupport hcover
  rw [← run_entries G C K.diameter B q T m s] at hx
  obtain ⟨x, hx, hcost⟩ := hx
  have hm := entry_meta G K B q T targets cost multiplicity C s ha hc hb htarget m v hv x hx
  have hbound : ∀ e ∈ x, e.price ≤ B := by
    intro e he
    rw [(hm e he).2]
    have := (cost e.id).isLt
    omega
  refine ⟨SolutionWord.fromEntries B x, ?_, ?_⟩
  · rw [run_program, hx]
    rfl
  · rw [SolutionWord.cost_fromEntries B x hbound]
    exact hcost

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ K.vertices) (hw : w ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = (program C K.diameter B q T m).run G s w := by
  simp only [run_program, run_entries]
  apply congrArg (Option.map (SolutionWord.fromEntries B))
  exact GeneralCoveringTerminalDataCorrect.uniform G K B q T
    (TerminalProtocolCorrect.demandList K.vertices multiplicity T) targets cost multiplicity C
    (dataState G C K.diameter B q T s) ha hc hb
    (chosen G K B q T targets cost multiplicity C s ha hc hb htarget)
    (fun r hr => TerminalProtocolCorrect.list_inside _ multiplicity T hr) htarget m v w hv hw

end Paper.GeneralCoveringTerminal

#print axioms Paper.GeneralCoveringTerminal.sound
#print axioms Paper.GeneralCoveringTerminal.complete
#print axioms Paper.GeneralCoveringTerminal.rounds
#print axioms Paper.GeneralCoveringTerminal.maxBits
