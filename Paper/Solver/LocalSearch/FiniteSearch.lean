import Paper.Preliminaries.MaskCompression

/-! Finite terminal enumeration for the exact local certificate search. -/
namespace Paper.FiniteSearch
attribute [local instance] Classical.propDecidable
open SevenFoundation
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def active (b : V → ℕ) : Finset V := Finset.univ.filter (fun r => 0 < b r)

def covers (b p : V → ℕ) : Prop := ∀ r, b r ≤ ∑ v ∈ closed G r, p v

def valid (m : ℕ) (b p : V → ℕ) : Prop := (∑ v, p v) ≤ m ∧ covers G b p

noncomputable def integerCost (c : V → ℝ) (p : V → ℕ) : ℝ := ∑ v, c v * (p v : ℝ)

noncomputable def embed (S : Finset V) (m : ℕ) (f : S → Fin (m + 1)) (v : V) : ℕ :=
  if h : v ∈ S then (f ⟨v, h⟩).val else 0

noncomputable def assignments (S : Finset V) (m : ℕ) : Finset (V → ℕ) :=
  Finset.univ.image (embed S m)

theorem assignments_card_le (S : Finset V) (m : ℕ) :
    (assignments S m).card ≤ (m + 1) ^ S.card := by
  have h := Finset.card_image_le (f := embed S m) (s := Finset.univ)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using h

theorem mem_assignments (S : Finset V) (m : ℕ) (p : V → ℕ)
    (hsize : ∑ v, p v ≤ m) (hsupport : ∀ v ∉ S, p v = 0) : p ∈ assignments S m := by
  classical
  have hp : ∀ v, p v < m + 1 := by
    intro v
    have h := (Finset.single_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) =>
      Nat.zero_le (p u)) (Finset.mem_univ v)).trans hsize
    omega
  let f : S → Fin (m + 1) := fun v => ⟨p v.val, hp v.val⟩
  apply Finset.mem_image.mpr
  refine ⟨f, Finset.mem_univ _, ?_⟩
  funext v
  by_cases hv : v ∈ S
  · simp only [embed, dif_pos hv]
    rfl
  · simp only [embed, dif_neg hv, hsupport v hv]

noncomputable def terminal (b : V → ℕ) (m : ℕ) (c : V → ℝ) : Finset (V → ℕ) :=
  (assignments (MaskCompression.representatives G (active b) c) m).filter (valid G m b)

theorem terminal_sound (b : V → ℕ) (m : ℕ) (c : V → ℝ) {p : V → ℕ}
    (hp : p ∈ terminal G b m c) : valid G m b p := (Finset.mem_filter.mp hp).2

/-- Every feasible completion has an enumerated replacement of no greater cost.
All coordinates, support, coverage and copy counts are actual finite objects. -/
theorem terminal_complete (b : V → ℕ) (m : ℕ) (c : V → ℝ) (p : V → ℕ)
    (hp : valid G m b p) : ∃ p' ∈ terminal G b m c, integerCost c p' ≤ integerCost c p := by
  classical
  let A := active b
  let f := MaskCompression.canonical G A c
  let p' := MaskCompression.push f p
  have hsize : (∑ v, p' v) ≤ m := by
    rw [MaskCompression.push_sum]
    exact hp.1
  have hcover : covers G b p' := by
    intro r
    by_cases hr : r ∈ A
    · rw [MaskCompression.compressed_coverage G A c p hr]
      exact hp.2 r
    · have hb : b r = 0 := by
        have hn : ¬ 0 < b r := fun h => hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        omega
      rw [hb]
      exact Nat.zero_le _
  refine ⟨p', Finset.mem_filter.mpr ⟨?_, hsize, hcover⟩, ?_⟩
  · exact mem_assignments _ m p' hsize (fun v hv => MaskCompression.compressed_support G A c p hv)
  · exact MaskCompression.compressed_cost_le G A c p
end Paper.FiniteSearch
