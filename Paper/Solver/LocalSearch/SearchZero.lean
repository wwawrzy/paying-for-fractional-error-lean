import Paper.Solver.LocalSearch.SearchCount

/-! Physical validity and completeness of the actually executed zero-budget
search case. A positive residual demand is rejected by exact task count. -/
namespace Paper.SearchZero
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]

theorem all_zero (H : Finset V) {q : ℕ} (multiplicity : V → Fin (q + 1))
    (hz : ∀ r, r ∉ H → (multiplicity r).val = 0)
    (hcard : (TerminalProtocolCorrect.demands H multiplicity).card = 0) :
    ∀ r, (multiplicity r).val = 0 := by
  have he : TerminalProtocolCorrect.demands H multiplicity = ∅ := Finset.card_eq_zero.mp hcard
  intro r
  by_cases hr : r ∈ H
  · apply Nat.eq_zero_of_not_pos
    intro hp
    have hm : r ∈ TerminalProtocolCorrect.demands H multiplicity := Finset.mem_filter.mpr ⟨hr, hp⟩
    rw [he] at hm
    simp at hm
  · exact hz r hr

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
variable (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
variable (k : ℕ) (hsize : I.card ≤ k) (B q : ℕ)
variable (cost : V → Fin (B + 1)) (multiplicity : V → Fin (q + 1))
variable {b : ℕ} (C : BitCode V b) (s : V → TerminalProtocol.Input V B q)
variable (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
variable (hb : ∀ v, (s v).value = multiplicity v)
include hI hsize ha hb

theorem result_iff (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) (w : SolutionWord.Word V B)
    (hw : (SearchCount.zero C (4 * k) B q).run G s v = some w) :
    w = [] ∧ (TerminalProtocolCorrect.demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card = 0 := by
  rw [SearchCount.zero_correct G D R L Q I hI k hsize B q multiplicity C s ha hb v hv] at hw
  split_ifs at hw with he
  · exact ⟨(Option.some.inj hw).symm, he⟩

theorem sound (hz : ∀ r, r ∉ PhysicalTasks.vertices G D R L Q I → (multiplicity r).val = 0)
    (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I) (w : SolutionWord.Word V B)
    (hw : (SearchCount.zero C (4 * k) B q).run G s v = some w) :
    w.length ≤ 0 ∧ (∀ t ∈ w, SolutionWord.id t ∈ PhysicalTasks.vertices G D R L Q I) ∧
      SolutionWord.Consistent cost w ∧
      ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, SolutionWord.copies w u := by
  obtain ⟨rfl, hcard⟩ := result_iff G D R L Q I hI k hsize B q multiplicity C s ha hb v hv w hw
  have hzero := all_zero (PhysicalTasks.vertices G D R L Q I) multiplicity hz hcard
  refine ⟨by simp, by simp, by simp [SolutionWord.Consistent], ?_⟩
  intro r
  rw [hzero r]
  exact Nat.zero_le _

theorem complete (v : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (p : V → ℕ) (hsizep : ∑ u, p u ≤ 0)
    (hcover : ∀ r, (multiplicity r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) :
    ∃ w, (SearchCount.zero C (4 * k) B q).run G s v = some w ∧
      SolutionWord.cost w ≤ IntegralTable.cost (fun u => (cost u).val) p := by
  have hp0 : ∀ u, p u = 0 := by
    intro u
    have hh : p u ≤ ∑ r, p r :=
      Finset.single_le_sum (fun r _ => Nat.zero_le (p r)) (Finset.mem_univ u)
    omega
  have hb0 : ∀ r, (multiplicity r).val = 0 := by
    intro r
    have hh := hcover r
    simpa only [hp0, Finset.sum_const_zero, Nat.le_zero_eq] using hh
  have hcard : (TerminalProtocolCorrect.demands (PhysicalTasks.vertices G D R L Q I) multiplicity).card = 0 := by
    simp [TerminalProtocolCorrect.demands, hb0]
  refine ⟨[], ?_, Nat.zero_le _⟩
  rw [SearchCount.zero_correct G D R L Q I hI k hsize B q multiplicity C s ha hb v hv, if_pos hcard]

theorem uniform (v w : V) (hv : v ∈ PhysicalTasks.vertices G D R L Q I)
    (hw : w ∈ PhysicalTasks.vertices G D R L Q I) :
    (SearchCount.zero C (4 * k) B q).run G s v = (SearchCount.zero C (4 * k) B q).run G s w := by
  rw [SearchCount.zero_correct G D R L Q I hI k hsize B q multiplicity C s ha hb v hv,
    SearchCount.zero_correct G D R L Q I hI k hsize B q multiplicity C s ha hb w hw]

omit hI hsize ha hb

theorem rounds (D B q : ℕ) : (SearchCount.zero C D B q).rounds = 4 * D + 1 := by
  simp only [SearchCount.zero, Program.rounds, SearchCount.rounds, Nat.add_zero]

theorem maxBits (D B q : ℕ) : (SearchCount.zero C D B q).maxBits ≤ max (3 * b + 3) (D + 2) :=
  max_le (SearchCount.maxBits C D B q) (Nat.zero_le _)
end Paper.SearchZero
