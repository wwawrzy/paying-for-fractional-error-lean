import Paper.Preliminaries.SolutionWord
import Paper.Preliminaries.TerminalProtocolCorrect
import Paper.Preliminaries.TerminalProtocolBudget

/-! The actual terminal returns a common bounded-cost/ID word type suitable
for recursive search at every budget, with physical validity and optimality. -/
namespace Paper.TerminalWord
open BroadcastModel
variable {V : Type} [LinearOrder V]

def program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) :=
  Program.seq (TerminalProtocol.program C D B q T m)
    (.local fun _ _ ans => ans.map (SolutionWord.fromEntries B))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {b : ℕ} (C : BitCode V b) (D B q T m : ℕ) (s : V → TerminalProtocol.Input V B q) (v : V) :
    (program C D B q T m).run G s v =
      ((TerminalProtocol.program C D B q T m).run G s v).map (SolutionWord.fromEntries B) := rfl

variable (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
variable (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
variable (k : ℕ) (hsize : I.card ≤ k) (B q T : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
include hI hsize ha hc hb

theorem entry_meta (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (w : List (TabularSearch.Entry V T))
    (hw : (TerminalProtocol.program C (4 * k) B q T m).run G s v = some w) :
    ∀ e ∈ w, e.id ∈ PhysicalTasks.vertices G D R L Q I ∧ e.price = (cost e.id).val := by
  let l := TerminalProtocolCorrect.demandList (PhysicalTasks.vertices G D R L Q I) multiplicity T
  let ds := TerminalProtocol.dataState G C (4 * k) B q T s
  have hl : ∀ u ∈ PhysicalTasks.vertices G D R L Q I, (ds u).demands = l :=
    TerminalProtocolCorrect.chosen G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb
  have hlist : ∀ r ∈ l, r ∈ PhysicalTasks.vertices G D R L Q I :=
    fun r hr => TerminalProtocolCorrect.list_inside _ multiplicity T hr
  rw [TerminalProtocol.run_program] at hw
  rw [TerminalDataCorrect.run_correct G D R L Q I hI k hsize B q T l cost multiplicity C ds
    ha hc hb hl hlist m v hv] at hw
  have hmem := (TabularSearch.choose_sound _ m _ hw).2.1
  intro e he
  have hh := ActualTable.wellformed G D R L Q I hI k hsize B T l cost C
    (fun u => TerminalData.maskInput (ds u)) ha hc hl v hv e (hmem e he)
  exact ⟨hh.1, hh.2.2⟩

theorem sound (hsmall : (TerminalProtocolCorrect.demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card ≤ T)
    (hz : ∀ r, r ∉ PhysicalTasks.vertices G D R L Q I → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) (w : SolutionWord.Word V B)
    (hw : (program C (4 * k) B q T m).run G s v = some w) :
    w.length ≤ m ∧ (∀ t ∈ w, SolutionWord.id t ∈ PhysicalTasks.vertices G D R L Q I) ∧
      SolutionWord.Consistent cost w ∧
      ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, SolutionWord.copies w u := by
  rw [run_program] at hw
  cases hr : (TerminalProtocol.program C (4 * k) B q T m).run G s v with
  | none => simp [hr] at hw
  | some x =>
    simp only [hr, Option.map_some, Option.some.injEq] at hw
    subst w
    have hs := TerminalProtocolCorrect.sound G D R L Q I hI k hsize B q T cost multiplicity C s
      ha hc hb hsmall hz m v hv x hr
    have hm := entry_meta G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb m v hv x hr
    refine ⟨?_, ?_, SolutionWord.consistent_fromEntries cost x (fun e he => (hm e he).2), ?_⟩
    · rw [SolutionWord.length_fromEntries, ← TableInterpretation.total_size]
      exact hs.1
    · intro t ht
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      exact (hm e he).1
    · simpa only [SolutionWord.copies_fromEntries] using hs.2.2.1

theorem complete (m : ℕ) (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ PhysicalTasks.vertices G D R L Q I → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (program C (4 * k) B q T m).run G s v = some w ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  obtain ⟨x, hx, hcost⟩ := TerminalProtocolCorrect.complete G D R L Q I hI k hsize B q T
    cost multiplicity C s ha hc hb m v hv p hsizep hsupport hcover
  have hm := entry_meta G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb m v hv x hx
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

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (hw : w ∈ PhysicalTasks.vertices G D R L Q I) :
    (program C (4 * k) B q T m).run G s v = (program C (4 * k) B q T m).run G s w := by
  rw [run_program, run_program,
    TerminalProtocolCorrect.uniform G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb m v w hv hw]

omit hI hsize ha hc hb

theorem rounds (D B q T m : ℕ) : (program C D B q T m).rounds = (T + 2 ^ T + 1) * (4 * D + 1) := by
  simp only [program, Program.rounds, TerminalProtocol.rounds, Nat.add_zero]

theorem maxBits (D B q T m : ℕ) : (program C D B q T m).maxBits ≤
    max (b + T * (q + 1) + 1) (max (2 * b + B + 3) (D + 2)) :=
  max_le (TerminalProtocol.maxBits C D B q T m) (Nat.zero_le _)
end Paper.TerminalWord
