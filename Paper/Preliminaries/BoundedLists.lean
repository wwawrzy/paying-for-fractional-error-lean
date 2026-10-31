import Paper.Certificates.Counting.CoreHitting
import Paper.Preliminaries.ListPhase

/-! Actual recursive bounded-list cover and its cost. The structural hypothesis
is radius-one density of each derived incidence graph; the clique-blowup
transfer from the physical input graph remains a separate dependency. -/
namespace Paper.BoundedLists
attribute [local instance] Classical.propDecidable Classical.decEq
open CoreHierarchy CoreIncidence
variable {V : Type*} [Fintype V] [LinearOrder V]

noncomputable def densityHierarchy (H : Finset (Finset V)) (a : ℕ) : ℕ → Prop
  | 0 => True
  | j + 1 => DepthOne.Bound (graph H) (a : ℝ) ∧ densityHierarchy (cores H (2 * a)) a j

noncomputable def cover (H : Finset (Finset V)) (q : ℕ) : ℕ → Finset V
  | 0 => ∅
  | j + 1 => ListPhase.phase H (cover (cores H q) q j)

noncomputable def factor (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => (j + 1) * factor q j + SunflowerLists.delta (j + 1) q

theorem core_comparison (H : Finset (Finset V)) (O : Finset V) (j a : ℕ) (ha : 1 ≤ a)
    (hrank : ∀ s ∈ H, s.card ≤ j + 1) (hO : ∀ s ∈ H, (s ∩ O).Nonempty)
    (hden : DepthOne.Bound (graph H) (a : ℝ)) :
    ∃ D : Finset V, (∀ C ∈ cores H (2 * a), (C ∩ D).Nonempty) ∧
      D.card ≤ (j + 1) * O.card := by
  have hq : 2 ≤ 2 * a := by omega
  have hap : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hqa : (a : ℝ) < (2 * a : ℕ) := by push_cast; linarith
  obtain ⟨D, hD, hcost⟩ := CoreHitting.exists_core_cover H O (j + 1) (2 * a) hq hrank hO hden hqa
  have heq : 1 + (((j + 1 - 1 : ℕ) : ℝ) * a) / (((2 * a : ℕ) : ℝ) - a) = (j + 1 : ℕ) := by
    simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  rw [heq] at hcost
  exact ⟨D, hD, by exact_mod_cast hcost⟩

set_option maxHeartbeats 2000000 in
/-- Every phase is an actual set construction. Cost is proved from the core
minor theorem and the no-missed-core sunflower count. -/
theorem cover_spec (H : Finset (Finset V)) (a : ℕ) (ha : 1 ≤ a) (j : ℕ)
    (hrank : ∀ s ∈ H, s.card ≤ j) (hnon : ∀ s ∈ H, s.Nonempty)
    (hden : densityHierarchy H a j) (O : Finset V) (hO : ∀ s ∈ H, (s ∩ O).Nonempty) :
    (∀ s ∈ H, (s ∩ cover H (2 * a) j).Nonempty) ∧
      (cover H (2 * a) j).card ≤ factor (2 * a) j * O.card := by
  classical
  induction j generalizing H O with
  | zero =>
    refine ⟨?_, by simp only [cover, Finset.card_empty, factor, zero_mul, le_refl]⟩
    intro s hs
    have hp := Finset.card_pos.mpr (hnon s hs)
    have hz := hrank s hs
    omega
  | succ j ih =>
    have hq : 2 ≤ 2 * a := by omega
    obtain ⟨O', hO', hOcard⟩ := core_comparison H O j a ha hrank hO hden.1
    have hrank' : ∀ C ∈ cores H (2 * a), C.card ≤ j := by
      intro C hC
      have h := core_rank_le H (2 * a) hq (j + 1) hrank C hC
      simpa only [Nat.add_sub_cancel] using h
    have hn' : ∀ C ∈ cores H (2 * a), C.Nonempty :=
      fun C hC => ((mem_cores H (2 * a) C).mp hC).1
    obtain ⟨hpre, hprecost⟩ := ih (cores H (2 * a)) hrank' hn' hden.2 O' hO'
    refine ⟨ListPhase.phase_covers H _ hnon, ?_⟩
    have hphase := ListPhase.phase_cost H (cover (cores H (2 * a)) (2 * a) j)
      O (j + 1) (2 * a) hq hrank hpre hO
    have hscale := Nat.mul_le_mul_left (factor (2 * a) j) hOcard
    calc
      _ ≤ _ := hphase
      _ ≤ factor (2 * a) j * ((j + 1) * O.card) + SunflowerLists.delta (j + 1) (2 * a) * O.card :=
        Nat.add_le_add_right (hprecost.trans hscale) _
      _ = factor (2 * a) (j + 1) * O.card := by rw [factor]; ring
end Paper.BoundedLists
