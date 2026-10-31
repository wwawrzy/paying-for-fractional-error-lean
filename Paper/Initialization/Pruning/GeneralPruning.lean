import Paper.Initialization.Pruning.InitializerResidual
import Paper.Certificates.Counting.HumanDependencies
import Paper.Initialization.Pruning.ActualInitialization

/-! Exact source residual coefficient, and pruning on arbitrary positive
d-degenerate graphs with an independent all-minor density parameter. -/
namespace Paper.GeneralPruning
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sharp_residual_bound {T μ : ℕ} (hT : 1 ≤ T) (hμ : 1 ≤ μ)
    {a : ℝ} (ha : 0 ≤ a) (hTa : 2 * a ≤ T) (hden : MinorDensity.Bound G a)
    {R : Fin (T + 1) → Finset V} {C : Fin T → Finset V}
    (M : InitialForest.Model G T (2 * T) μ R C)
    (X : Finset V) (hX : ∀ i : Fin T, X ⊆ R i.succ)
    (S : Fin T → Finset V) (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hremoved : ∀ i, R i.castSucc \ R i.succ ⊆ covered G (S i)) :
    (X.card : ℝ) ≤ (2*(T : ℝ)/((T : ℝ)-a)) * (Finset.univ.biUnion S).card := by
  classical
  obtain ⟨Q, hQX, hQcard, hsuccess⟩ := SuccessfulRegions.many_successful G hT M hμ X hX
  let own := ForestRegions.owner M.parent M.rank M.decrease X
  obtain ⟨P, hPQ, hPcard, havoid⟩ := InitializerResidual.discard_intersecting own Q (Finset.univ.biUnion S)
  have htouch : ∀ x ∈ P, ∀ i, ∃ v, own v = some x ∧ v ∈ covered G (S i) := by
    intro x hx i
    obtain ⟨v, hv, ho⟩ := hsuccess x (hPQ hx) i
    exact ⟨v, ho, hremoved i hv⟩
  have hcount := RegionMinor.count G M.parent M.rank M.decrease hden X P
    (Finset.univ.biUnion S) (hPQ.trans hQX) M.subgraph havoid T
    (fun _ hx => InitializerResidual.touched_count G own S hdis P havoid htouch hx)
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hdiff : 0 < (T : ℝ)-a := by linarith
  have hQ' : (X.card : ℝ) ≤ 2*Q.card := by exact_mod_cast hQcard
  have hP' : (Q.card : ℝ) ≤ P.card + (Finset.univ.biUnion S).card := by exact_mod_cast hPcard
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdiff).mpr
  have hh := mul_le_mul_of_nonneg_right (hQ'.trans (mul_le_mul_of_nonneg_left hP' (by norm_num))) hdiff.le
  nlinarith [hcount]

theorem pass_bound {T d : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d)
    (hdeg : G.IsKDegenerate d) {a : ℝ} (ha : 0 ≤ a) (hTa : 2*a ≤ T)
    (hden : MinorDensity.Bound G a)
    (R : Fin (T+1) → Finset V) (C S : Fin T → Finset V)
    (hf : ∀ i v, v ∈ R i.succ → d+4*T*T*d ≤ ((G.neighborFinset v) ∩ C i).card)
    (hh : ∀ i v, v ∈ C i → d+4*T*d ≤ ((G.neighborFinset v) ∩ R i.castSucc).card)
    (X : Finset V) (hX : ∀ i : Fin T, X ⊆ R i.succ)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hremoved : ∀ i, R i.castSucc \ R i.succ ⊆ covered G (S i)) :
    (X.card : ℝ) ≤ (2*(T : ℝ)/((T : ℝ)-a)) * (Finset.univ.biUnion S).card ∧
      X.card ≤ 4 * (Finset.univ.biUnion S).card := by
  have hf' : ∀ i v, v ∈ R i.succ →
      d+(T+T)*d*(2*T) ≤ ((G.neighborFinset v) ∩ C i).card := by
    intro i v hv
    convert hf i v hv using 1 <;> ring
  have hh' : ∀ i v, v ∈ C i →
      d+(T+T)*d*2 ≤ ((G.neighborFinset v) ∩ R i.castSucc).card := by
    intro i v hv
    convert hh i v hv using 1 <;> ring
  obtain ⟨M⟩ := HumanDependencies.simultaneous_forest G hT hd hdeg R C hf' hh'
  exact ⟨sharp_residual_bound G hT (by omega) ha hTa hden M X hX S hdis hremoved,
    InitializerResidual.residual_bound G hT (by omega) ha hTa hden M X hX S hdis hremoved⟩

section Actual
open InitializerPass InitializerRun ActualInitialization

theorem actual_residual (b d T : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    {a : ℝ} (ha : 0 ≤ a) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (hdeg : G.IsKDegenerate d) (R₀ : Finset V) :
    ((state G b (candidateThreshold d T) (listThreshold d T) R₀ T).card : ℝ) ≤
      (2*(T : ℝ)/((T : ℝ)-a)) * (past G b (candidateThreshold d T) (listThreshold d T) R₀ T).card := by
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
  obtain ⟨M⟩ := HumanDependencies.simultaneous_forest G hT hd hdeg R C hf hh
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
  have hc := sharp_residual_bound G hT (by omega) ha hTa hden M X hX S hdis hr
  rw [past_eq_fin G b h f T R₀] at hc
  exact hc

end Actual

end Paper.GeneralPruning
