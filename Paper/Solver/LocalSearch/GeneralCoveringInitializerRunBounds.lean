import Paper.Solver.LocalSearch.GeneralCoveringInitializerRun
import Paper.Initialization.Pruning.InitializerResidual

/-! Bounds for the actual arbitrary-covering initializer. The simultaneous
forest is constructed from physical minor density and the proved physical
degree witnesses of the actual passes. The integral competitor and costs
occur only in this analysis; the private-input program is unchanged. -/
namespace Paper.GeneralCoveringInitializerRunBounds
open BroadcastModel SevenFoundation GeneralCoveringInitializerRun
open scoped BigOperators

/-- A public numeric coefficient, independent of the graph and private data. -/
noncomputable def constant (b h f T : ℕ) : ℕ :=
  5 * T * h * (BoundedLists.factor (2 * b) f + 1)

variable {V : Type} [Fintype V] [LinearOrder V]

theorem mem_past (C : V → Finset V) (b h f : ℕ) (R₀ : Finset V) (T : ℕ) (v : V) :
    v ∈ past C b h f R₀ T ↔ ∃ i < T, v ∈ selection C b h f R₀ i := by
  induction T with
  | zero => simp [past]
  | succ T ih =>
    change (v ∈ past C b h f R₀ T ∪ selection C b h f R₀ T) ↔ _
    rw [Finset.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨T, Nat.lt_succ_self T, hv⟩
    · rintro ⟨i, hi, hv⟩
      by_cases hiT : i < T
      · exact Or.inl ⟨i, hiT, hv⟩
      · have he : i = T := by omega
        subst i
        exact Or.inr hv

theorem past_eq_fin (C : V → Finset V) (b h f T : ℕ) (R₀ : Finset V) :
    (Finset.univ.biUnion (fun i : Fin T => selection C b h f R₀ i.val)) =
      past C b h f R₀ T := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_past]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, i.isLt, hi⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨⟨i, hi⟩, hv⟩

theorem selected_cost_le (C : V → Finset V) (b h f T B : ℕ) (hb : 1 ≤ b)
    (R₀ : Finset V) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R₀, c v ≤ B) :
    (∑ v ∈ selected C b h f R₀ T, c v) ≤ (B : ℝ) * (selected C b h f R₀ T).card := by
  calc
    _ ≤ ∑ _v ∈ selected C b h f R₀ T, (B : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact hc v (selected_admissible C b h f hb R₀ T hv)
    _ = _ := by simp [mul_comm]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The actual residual is bounded using constructed physical forest data.
No residual bound, orientation, degeneracy certificate or forest is assumed. -/
theorem residual_bound (C : V → Finset V) (b h f d T : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (hrows : ∀ r ∈ R₀, (C r).Nonempty) :
    (state C b h f R₀ T).card ≤ 4 * (past C b h f R₀ T).card := by
  let R : Fin (T + 1) → Finset V := fun i => state C b h f R₀ i.val
  let E : Fin T → Finset V := fun i =>
    GeneralCoveringInitializerPassLists.eligible C h (R i.castSucc)
  let S : Fin T → Finset V := fun i => selection C b h f R₀ i.val
  have hl : ∀ i : Fin T, ∀ r ∈ R i.castSucc, C r ⊆ closed G r := by
    intro i r hr
    exact hlocal r (state_subset_initial C b h f R₀ i.val hr)
  have hn : ∀ i : Fin T, ∀ r ∈ R i.castSucc, (C r).Nonempty := by
    intro i r hr
    exact hrows r (state_subset_initial C b h f R₀ i.val hr)
  have hf' : ∀ i v, v ∈ R i.succ →
      d + (T + T) * d * (2 * T) ≤ ((G.neighborFinset v) ∩ E i).card := by
    intro i v hv
    have hv' : v ∈ GeneralCoveringInitializerPass.residual C b h f (R i.castSucc) := hv
    have hc := GeneralCoveringInitializerPass.surviving_neighbors G C b h f
      (R i.castSucc) (hl i) (hn i) hv'
    have ht : d + (T + T) * d * (2 * T) ≤ f := by
      calc
        _ = d + 4 * T * T * d := by ring
        _ ≤ f := hf
    exact ht.trans hc
  have hh' : ∀ i v, v ∈ E i →
      d + (T + T) * d * 2 ≤ ((G.neighborFinset v) ∩ R i.castSucc).card := by
    intro i v hv
    have hc := GeneralCoveringInitializerPass.candidate_neighbors G C h (R i.castSucc) (hl i) hv
    have ht : d + (T + T) * d * 2 ≤ h := by
      calc
        _ = d + 4 * T * d := by ring
        _ ≤ h := hh
    exact ht.trans hc
  obtain ⟨M⟩ := InitialForest.exists_model G (κ := 2 * T) (μ := 2) hT hd
    (MinorDensity.induced_bound G hden) hda R E hf' hh'
  let X := state C b h f R₀ T
  have hX : ∀ i : Fin T, X ⊆ R i.succ := by
    intro i
    exact GeneralCoveringInitializerRun.antitone C b h f R₀ (show i.val + 1 ≤ T by omega)
  have hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j) := by
    intro i j hij
    exact selections_disjoint C b h f hb R₀ (fun he => hij (Fin.ext he))
  have hremoved : ∀ i, R i.castSucc \ R i.succ ⊆ covered G (S i) := by
    intro i
    exact GeneralCoveringInitializerPass.removed_physically_covered G C b h f (R i.castSucc) (hl i)
  have hc := InitializerResidual.residual_bound G hT (by omega) ha hTa hden M X hX S hdis hremoved
  change (state C b h f R₀ T).card ≤
    4 * (Finset.univ.biUnion (fun i : Fin T => selection C b h f R₀ i.val)).card at hc
  rw [past_eq_fin C b h f T R₀] at hc
  exact hc

/-- Terminal requests contribute at most one new candidate per true survivor. -/
theorem selected_past_bound (C : V → Finset V) (b h f d T : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a) (R₀ : Finset V)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (hrows : ∀ r ∈ R₀, (C r).Nonempty) :
    (selected C b h f R₀ T).card ≤ 5 * (past C b h f R₀ T).card := by
  have hr := residual_bound G C b h f d T hb hd hT hh hf ha hda hTa hden R₀ hlocal hrows
  have hreq := GeneralCoveringRequests.requested_card C (state C b h f R₀ T)
  have hu := Finset.card_union_le (past C b h f R₀ T)
    (GeneralCoveringRequests.requested C (state C b h f R₀ T))
  change (selected C b h f R₀ T).card ≤ _ at hu
  omega

/-- Sum the proved cost of the literal passes against one integral C-cover.
Every hierarchy is derived by Pass.pass_cost from the same physical density. -/
theorem past_cost (C : V → Finset V) (b h f T : ℕ) (hb : 1 ≤ b) (hh : 1 ≤ h)
    (R₀ O : Finset V) (hO : GeneralCoveringInitializerPass.Covers C R₀ O)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) {a : ℝ} (ha : 0 ≤ a)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b) :
    (past C b h f R₀ T).card ≤ T * h * (BoundedLists.factor (2 * b) f + 1) * O.card := by
  rw [← past_eq_fin C b h f T R₀]
  calc
    _ ≤ ∑ i : Fin T, (selection C b h f R₀ i.val).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin T, h * (BoundedLists.factor (2 * b) f + 1) * O.card := by
      apply Finset.sum_le_sum
      intro i _
      have hR := state_subset_initial C b h f R₀ i.val
      exact GeneralCoveringInitializerPass.pass_cost G C b h f hb hh
        (state C b h f R₀ i.val) O (fun r hr => hO r (hR hr))
        (fun r hr => hlocal r (hR hr)) ha hden hba
    _ = _ := by simp [mul_assoc]

theorem selected_card (C : V → Finset V) (b h f d T : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R₀ O : Finset V) (hO : GeneralCoveringInitializerPass.Covers C R₀ O)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) :
    (selected C b h f R₀ T).card ≤ constant b h f T * O.card := by
  have hrows : ∀ r ∈ R₀, (C r).Nonempty := by
    intro r hr
    obtain ⟨v, _, hv⟩ := hO r hr
    exact ⟨v, hv⟩
  have hs := selected_past_bound G C b h f d T hb hd hT hh hf ha hda hTa hden R₀ hlocal hrows
  have hp := past_cost G C b h f T hb (by omega) R₀ O hO hlocal ha hden hba
  calc
    _ ≤ 5 * (past C b h f R₀ T).card := hs
    _ ≤ 5 * (T * h * (BoundedLists.factor (2 * b) f + 1) * O.card) := Nat.mul_le_mul_left 5 hp
    _ = _ := by unfold constant; ring

/-- Bounded positive costs on admissible vertices give a weighted benchmark
against every admissible integral C-cover. No optimum is input to the program. -/
theorem weighted_bound (C : V → Finset V) (b h f d T B : ℕ)
    (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R₀ O : Finset V) (hO : GeneralCoveringInitializerPass.Covers C R₀ O)
    (hOad : O ⊆ CoveringSupport.admissible C R₀)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R₀, 1 ≤ c v ∧ c v ≤ B) :
    (∑ v ∈ selected C b h f R₀ T, c v) ≤
      (B : ℝ) * (constant b h f T : ℝ) * (∑ v ∈ O, c v) := by
  have hcard := selected_card G C b h f d T hb hd hT hh hf ha hda hTa hden hba R₀ O hO hlocal
  have hOc : (O.card : ℝ) ≤ ∑ v ∈ O, c v := by
    calc
      _ = ∑ _v ∈ O, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => (hc v (hOad hv)).1)
  have hnon : (0 : ℝ) ≤ (B : ℝ) * (constant b h f T : ℝ) :=
    mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg _)
  calc
    _ ≤ (B : ℝ) * (selected C b h f R₀ T).card :=
      selected_cost_le C b h f T B hb R₀ c (fun v hv => (hc v hv).2)
    _ ≤ (B : ℝ) * ((constant b h f T : ℝ) * (O.card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (Nat.cast_nonneg B)
    _ = (B : ℝ) * (constant b h f T : ℝ) * (O.card : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hOc hnon

/-- Bounds and feasibility of the existing private-input program. All numeric
hypotheses are uniform; only the physical minor bound depends on the graph. -/
theorem spec {bits : ℕ} (ids : BitCode V bits) (C targets : V → Finset V)
    (b h f d T B : ℕ) (hb : 1 ≤ b) (hd : 1 ≤ d) (hT : 1 ≤ T)
    (hh : d + 4 * T * d ≤ h) (hf : d + 4 * T * T * d ≤ f)
    {a : ℝ} (ha : 0 ≤ a) (hda : 2 * a ≤ d) (hTa : 2 * a ≤ T)
    (hden : MinorDensity.Bound G a)
    (hba : a * ((2 ^ f + 1 : ℕ) : ℝ) ^ 4 + (2 ^ f + 1 : ℕ) ≤ b)
    (R₀ O : Finset V) (hO : GeneralCoveringInitializerPass.Covers C R₀ O)
    (hOad : O ⊆ CoveringSupport.admissible C R₀)
    (hlocal : ∀ r ∈ R₀, C r ⊆ closed G r)
    (hinc : ∀ v r, r ∈ targets v ↔ v ∈ C r) (c : V → ℝ)
    (hc : ∀ v ∈ CoveringSupport.admissible C R₀, 1 ≤ c v ∧ c v ≤ B)
    (s : V → Input V) (hR : ∀ r, (s r).residual = decide (r ∈ R₀))
    (hC : ∀ r, (s r).candidates = C r) (hTargets : ∀ v, (s v).targets = targets v) :
    GeneralCoveringInitializerPass.Covers C R₀ (output G ids b h f T s) ∧
      output G ids b h f T s ⊆ CoveringSupport.admissible C R₀ ∧
      (output G ids b h f T s).card ≤ constant b h f T * O.card ∧
      (∑ v ∈ output G ids b h f T s, c v) ≤
        (B : ℝ) * (constant b h f T : ℝ) * (∑ v ∈ O, c v) := by
  have hrows : ∀ r ∈ R₀, (C r).Nonempty := by
    intro r hr
    obtain ⟨v, _, hv⟩ := hO r hr
    exact ⟨v, hv⟩
  rw [output_eq G ids C targets b h f T hb R₀ hinc hlocal hrows s hR hC hTargets]
  exact ⟨selected_covers C b h f R₀ T hrows, selected_admissible C b h f hb R₀ T,
    selected_card G C b h f d T hb hd hT hh hf ha hda hTa hden hba R₀ O hO hlocal,
    weighted_bound G C b h f d T B hb hd hT hh hf ha hda hTa hden hba R₀ O hO hOad hlocal c hc⟩

end Paper.GeneralCoveringInitializerRunBounds

#print axioms Paper.GeneralCoveringInitializerRunBounds.past_eq_fin
#print axioms Paper.GeneralCoveringInitializerRunBounds.selected_cost_le
#print axioms Paper.GeneralCoveringInitializerRunBounds.residual_bound
#print axioms Paper.GeneralCoveringInitializerRunBounds.selected_past_bound
#print axioms Paper.GeneralCoveringInitializerRunBounds.past_cost
#print axioms Paper.GeneralCoveringInitializerRunBounds.selected_card
#print axioms Paper.GeneralCoveringInitializerRunBounds.weighted_bound
#print axioms Paper.GeneralCoveringInitializerRunBounds.spec
