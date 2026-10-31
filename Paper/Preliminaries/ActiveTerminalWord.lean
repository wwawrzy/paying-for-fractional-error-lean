import Paper.Preliminaries.TerminalWord
import Paper.Preliminaries.ActiveTerminalProtocol

/-! Common bounded solution word for the generic actual active task terminal. -/
namespace Paper.ActiveTerminalWord
open BroadcastModel TerminalWord
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (K : ActiveTask.Context G) (B q T : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
variable (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
include ha hc hb

theorem entry_meta (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (w : List (TabularSearch.Entry V T))
    (hw : (TerminalProtocol.program C K.diameter B q T m).run G s v = some w) :
    ∀ e ∈ w, e.id ∈ K.vertices ∧ e.price = (cost e.id).val := by
  let l := TerminalProtocolCorrect.demandList (K.vertices) multiplicity T
  let ds := TerminalProtocol.dataState G C K.diameter B q T s
  have hl : ∀ u ∈ K.vertices, (ds u).demands = l :=
    ActiveTerminalProtocol.chosen G K B q T cost multiplicity C s ha hc hb
  have hlist : ∀ r ∈ l, r ∈ K.vertices :=
    fun r hr => TerminalProtocolCorrect.list_inside _ multiplicity T hr
  rw [TerminalProtocol.run_program] at hw
  rw [ActiveTerminalData.run_correct G K B q T l cost multiplicity C ds
    ha hc hb hl hlist m v hv] at hw
  have hmem := (TabularSearch.choose_sound _ m _ hw).2.1
  intro e he
  have hh := ActiveActualTable.wellformed G K B T l cost C
    (fun u => TerminalData.maskInput (ds u)) ha hc hl v hv e (hmem e he)
  exact ⟨hh.1, hh.2.2⟩

theorem sound (hsmall : (TerminalProtocolCorrect.demands (K.vertices) multiplicity).card ≤ T)
    (hz : ∀ r, r ∉ K.vertices → (multiplicity r).val = 0)
    (m : ℕ) (v : V) (hv : v ∈ K.vertices) (w : SolutionWord.Word V B)
    (hw : (program C K.diameter B q T m).run G s v = some w) :
    w.length ≤ m ∧ (∀ t ∈ w, SolutionWord.id t ∈ K.vertices) ∧
      SolutionWord.Consistent cost w ∧
      ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, SolutionWord.copies w u := by
  rw [run_program] at hw
  cases hr : (TerminalProtocol.program C K.diameter B q T m).run G s v with
  | none => simp [hr] at hw
  | some x =>
    simp only [hr, Option.map_some, Option.some.injEq] at hw
    subst w
    have hs := ActiveTerminalProtocol.sound G K B q T cost multiplicity C s
      ha hc hb hsmall hz m v hv x hr
    have hm := entry_meta G K B q T cost multiplicity C s ha hc hb m v hv x hr
    refine ⟨?_, ?_, SolutionWord.consistent_fromEntries cost x (fun e he => (hm e he).2), ?_⟩
    · rw [SolutionWord.length_fromEntries, ← TableInterpretation.total_size]
      exact hs.1
    · intro t ht
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
      exact (hm e he).1
    · simpa only [SolutionWord.copies_fromEntries] using hs.2.2.1

theorem complete (m : ℕ) (v : V) (hv : v ∈ K.vertices)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ m)
    (hsupport : ∀ u, u ∉ K.vertices → p u = 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (program C K.diameter B q T m).run G s v = some w ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  obtain ⟨x, hx, hcost⟩ := ActiveTerminalProtocol.complete G K B q T
    cost multiplicity C s ha hc hb m v hv p hsizep hsupport hcover
  have hm := entry_meta G K B q T cost multiplicity C s ha hc hb m v hv x hx
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

theorem uniform (m : ℕ) (v w : V) (hv : v ∈ K.vertices)
    (hw : w ∈ K.vertices) :
    (program C K.diameter B q T m).run G s v = (program C K.diameter B q T m).run G s w := by
  rw [run_program, run_program,
    ActiveTerminalProtocol.uniform G K B q T cost multiplicity C s ha hc hb m v w hv hw]

end Paper.ActiveTerminalWord
