import Paper.Solver.LocalSearch.SearchParentCorrect

/-! Full budget induction for the literal RecursiveSearch.program.
Physical task connectivity supplies the genuine count/list/value protocols;
induced density supplies only the heavy-list completeness theorem.
No correctness/solution/list oracle remains in the final statement. -/
namespace Paper.RecursiveSearchCorrect
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (a : ℕ) (ha' : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G (a : ℝ)) (B q : ℕ)
    (cost : V → Fin (B + 1)) {bits : ℕ} (C : BitCode V bits)
    (m : ℕ) (multiplicity : V → Fin (q + 1)) (s : V → TerminalProtocol.Input V B q)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v).cost = cost v) (hb : ∀ v, (s v).value = multiplicity v)
    (hz : ∀ r, r ∉ PhysicalTasks.vertices G D R L Q I → (multiplicity r).val = 0) :
    SearchSpec.Spec G (RecursiveSearch.program C (4 * k) a B q m)
      (PhysicalTasks.vertices G D R L Q I) cost multiplicity m s := by
  induction m generalizing multiplicity s with
  | zero =>
    constructor
    · exact SearchZero.sound G D R L Q I hI k hsize B q cost multiplicity C s ha hb hz
    · intro p hp _ hpc v hv
      exact SearchZero.complete G D R L Q I hI k hsize B q cost multiplicity C s ha hb v hv p hp hpc
    · exact SearchZero.uniform G D R L Q I hI k hsize B q multiplicity C s ha hb
  | succ m ih =>
    let H := PhysicalTasks.vertices G D R L Q I
    let A := TerminalProtocolCorrect.demands H multiplicity
    let T := RecursiveSearch.threshold a (m + 1)
    let K := RecursiveSearch.branches a (m + 1)
    let leaf := TerminalWord.program C (4 * k) B q T (m + 1)
    let control := SearchControl.program C (4 * k) a B q (m + 1)
    let child := RecursiveSearch.program C (4 * k) a B q m
    change SearchSpec.Spec G (BranchParent.program leaf control child K) H cost multiplicity (m + 1) s
    refine SearchParentCorrect.correct G H cost multiplicity s ha hc hb hz leaf control child ih
      K (T ≤ A.card) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro hn
      have hsmall : A.card ≤ T := (lt_of_not_ge hn).le
      constructor
      · exact TerminalWord.sound G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb hsmall hz (m + 1)
      · intro p hp hps hpc v hv
        exact TerminalWord.complete G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb
          (m + 1) v hv p hp hps hpc
      · exact TerminalWord.uniform G D R L Q I hI k hsize B q T cost multiplicity C s ha hc hb (m + 1)
    · intro v hv
      change ((SearchControl.program C (4 * k) a B q (m + 1)).run G s v).large = _
      rw [SearchControlCorrect.result G D R L Q I hI k hsize a B q (m + 1) cost multiplicity C s ha hc hb v hv]
      rfl
    · exact SearchControlCorrect.uniform G D R L Q I hI k hsize a B q (m + 1) cost multiplicity C s ha hc hb
    · exact SearchControlCorrect.support G D R L Q I hI k hsize a B q (m + 1) cost multiplicity C s ha hc hb
    · exact SearchControlCorrect.consistent G D R L Q I hI k hsize a B q (m + 1) cost multiplicity C s ha hc hb
    · exact SearchControlCorrect.candidates_length G D R L Q I hI k hsize a B q (m + 1) cost multiplicity C s ha hc hb
    · intro hlarge p hp hps hpc v hv
      have hT : 0 < T := by dsimp [T, RecursiveSearch.threshold]; positivity
      have hA : A.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hT hlarge)
      have hcover : ∀ r ∈ A, 1 ≤ ∑ u ∈ SevenFoundation.closed G r, p u := by
        intro r hr
        have hh := (Finset.mem_filter.mp hr).2
        exact (by omega : 1 ≤ (multiplicity r).val).trans (hpc r)
      obtain ⟨u, hu, hpos⟩ := LocalSearchBounds.completion_hits_heavy G A hA (m + 1) (by omega) p hp hcover
      have huH : u ∈ H := by
        by_contra hn
        have hh := hps u hn
        omega
      refine ⟨CostTag.tag cost u, ?_, hpos⟩
      exact SearchControlCorrect.contains_heavy G D R L Q I hI k hsize a B q (m + 1) cost multiplicity C s
        ha hc hb ha' (by omega) hden hlarge v hv u huH hu
end Paper.RecursiveSearchCorrect
