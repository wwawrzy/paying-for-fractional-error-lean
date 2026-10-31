import Paper.Partitions.Local.FinitePartition

/-! Root part labels without choosing a part: union of exactly the output
parts containing the root. This has a direct finite stage recursion. -/
namespace Paper.FinitePartLabels
variable {V : Type} [LinearOrder V]

def label (N : V → Finset V) (k t : ℕ) {Q : ℕ} (S : Finset V) :
    (n : ℕ) → FiniteIteration.Seeds (Finset V → Fin Q) n → V → Finset V
  | 0, _, v => if v ∈ S then {v} else ∅
  | n + 1, ω, v =>
    FinitePriorityRule.part (FiniteEligibility.family N S k t) ω.1 v ∪
      label N k t (FinitePriorityRule.next N S k t ω.1) n ω.2 v

theorem parts (N : V → Finset V) (k t : ℕ) {Q : ℕ} (S : Finset V) (n : ℕ)
    (ω : FiniteIteration.Seeds (Finset V → Fin Q) n) (v : V) :
    label N k t S n ω v = (FinitePartition.parts N k t S n ω).biUnion (fun U => if v ∈ U then U else ∅) := by
  induction n generalizing S with
  | zero =>
    by_cases hv : v ∈ S
    · ext u
      simp only [label, if_pos hv, FinitePartition.parts, Finset.mem_singleton, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro hu
        subst u
        exact ⟨{v}, ⟨v, hv, rfl⟩, by simp⟩
      · rintro ⟨U, ⟨w, hw, rfl⟩, hu⟩
        split_ifs at hu with h
        · have hvw : v = w := Finset.mem_singleton.mp h
          exact (Finset.mem_singleton.mp hu).trans hvw.symm
        · exact False.elim (Finset.notMem_empty u hu)
    · ext u
      simp only [label, if_neg hv, FinitePartition.parts, Finset.notMem_empty, false_iff,
        Finset.mem_biUnion, Finset.mem_image]
      rintro ⟨U, ⟨w, hw, rfl⟩, hu⟩
      split_ifs at hu with h
      · have he : v = w := Finset.mem_singleton.mp h
        exact hv (he ▸ hw)
      · exact Finset.notMem_empty u hu
  | succ n ih =>
    rw [label, FinitePartition.parts, Finset.union_biUnion, ← ih]
    rfl
end Paper.FinitePartLabels
