import Paper.Initialization.Pruning.InitializerRun
import Paper.Initialization.Pruning.InitializerResidual

/-! The residual estimate for the actual iterative initialization algorithm.
No forest, successful-region certificate or pass-disjointness is an input. -/
namespace Paper.ActualInitialization
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass InitializerRun
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def candidateThreshold (d T : ℕ) : ℕ := d + 4 * T * d
def listThreshold (d T : ℕ) : ℕ := d + 4 * T * T * d

theorem past_eq_fin (b h f T : ℕ) (R₀ : Finset V) :
    (Finset.univ.biUnion (fun i : Fin T => selection G b h f R₀ i.val)) = past G b h f R₀ T := by
  ext v
  simp only [past, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨⟨i, hi⟩, hv⟩

set_option maxHeartbeats 2000000 in
theorem residual_bound (b d T : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V) :
    (state G b (candidateThreshold d T) (listThreshold d T) R₀ T).card ≤
      4 * (past G b (candidateThreshold d T) (listThreshold d T) R₀ T).card := by
  classical
  let h := candidateThreshold d T
  let f := listThreshold d T
  let R : Fin (T + 1) → Finset V := fun i => state G b h f R₀ i.val
  let C : Fin T → Finset V := fun i => candidates G h (R i.castSucc)
  have hf : ∀ i v, v ∈ R i.succ → d + (T + T) * d * (2 * T) ≤ ((G.neighborFinset v) ∩ C i).card := by
    intro i v hv
    have hv' : v ∈ residual G b h f (R i.castSucc) := hv
    have hh := surviving_neighbors G b h f (R i.castSucc) hv'
    have he : d + (T + T) * d * (2 * T) = f := by dsimp [f, listThreshold]; ring
    simpa only [he] using hh
  have hh : ∀ i v, v ∈ C i → d + (T + T) * d * 2 ≤ ((G.neighborFinset v) ∩ R i.castSucc).card := by
    intro i v hv
    have hc := candidate_neighbors G h (R i.castSucc) hv
    have he : d + (T + T) * d * 2 = h := by dsimp [h, candidateThreshold]; ring
    simpa only [he] using hc
  obtain ⟨M⟩ := InitialForest.exists_model G hT hd (MinorDensity.induced_bound G hden) hda R C hf hh
  let X := state G b h f R₀ T
  have hX : ∀ i : Fin T, X ⊆ R i.succ := by
    intro i
    exact InitializerRun.antitone G b h f R₀ (show i.val + 1 ≤ T by omega)
  let S : Fin T → Finset V := fun i => selection G b h f R₀ i.val
  have hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    exact selections_disjoint G b h f hb R₀ (fun he => hij (Fin.ext he))
  have hr : ∀ i, R i.castSucc \ R i.succ ⊆ covered G (S i) := by
    intro i
    exact removed_covered G b h f R₀ i.val
  have hc := InitializerResidual.residual_bound G hT (by omega) ha hTa hden M X hX S hdis hr
  rw [past_eq_fin G b h f T R₀] at hc
  exact hc

theorem output_bound (b d T : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V) :
    let S := past G b (candidateThreshold d T) (listThreshold d T) R₀ T
    let X := state G b (candidateThreshold d T) (listThreshold d T) R₀ T
    R₀ ⊆ covered G (S ∪ X) ∧ (S ∪ X).card ≤ 5 * S.card := by
  dsimp only
  refine ⟨output_covers G _ _ _ _ _, ?_⟩
  have hr := residual_bound G b d T hb hd hT ha hda hTa hden R₀
  have hu := Finset.card_union_le
    (past G b (candidateThreshold d T) (listThreshold d T) R₀ T)
    (state G b (candidateThreshold d T) (listThreshold d T) R₀ T)
  omega
end Paper.ActualInitialization
