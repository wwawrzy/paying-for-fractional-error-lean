import Paper.RedBlue.Rounding

/-! Feasibility of the actual numerical red-blue rounding program. -/
namespace Paper.RedBlue
open BroadcastModel SevenFoundation CoveringThresholdInput
attribute [local instance 10] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rounding_covers {b M : ℕ} (ids : BitCode V b)
    (R B : Finset V) (c : V → Fin (M + 1)) (n : V → ℕ) (t q : ℕ)
    (hne : ∀ r ∈ R, (rows G R B r).Nonempty) :
    ∀ r ∈ R, ∃ v ∈ CoveringThresholdCost.output G ids t q
      (roundingInput G R B c n), v ∈ B ∧ G.Adj r v := by
  intro r hr
  obtain ⟨v, hv, hs⟩ := CoveringThresholdInput.output_covers G ids t q
    (roundingInput G R B c n) (fun r _ => rows_local G R B r)
    (fun r hr => hne r (by simpa [roundingInput] using hr))
    r (by simpa [roundingInput] using hr)
  obtain ⟨_, ha, hb⟩ := (mem_rows G R B r v).mp hv
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, hb, ha⟩

theorem rounding_subset_blue {b M : ℕ} (ids : BitCode V b)
    (R B : Finset V) (c : V → Fin (M + 1)) (n : V → ℕ) (t q : ℕ)
    (hq : 0 < q) (hne : ∀ r ∈ R, (rows G R B r).Nonempty)
    (hsupport : ∀ v ∉ B, n v = 0) :
    CoveringThresholdCost.output G ids t q (roundingInput G R B c n) ⊆ B := by
  intro v hv
  rw [CoveringThresholdCost.output, CoveringThresholdInput.output_image G ids t q
    (roundingInput G R B c n) (fun r _ => rows_local G R B r)
    (fun r hr => hne r (by simpa [roundingInput] using hr))] at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · by_contra hb
    have hs := (Finset.mem_filter.mp hv).2
    change q ≤ t * n v at hs
    rw [hsupport v hb, Nat.mul_zero] at hs
    omega
  · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    have hd := (Finset.mem_filter.mp hr).2.1
    have hrR : r ∈ R := by simpa [prepare, roundingInput] using hd
    have hc := (CoveringRoundingCost.chosen_spec
      (fun v => prepare t q (roundingInput G R B c n v)) r (hne r hrR)).2.1
    exact ((mem_rows G R B r _).mp hc).2.2

end Paper.RedBlue
#print axioms Paper.RedBlue.rounding_covers
#print axioms Paper.RedBlue.rounding_subset_blue
