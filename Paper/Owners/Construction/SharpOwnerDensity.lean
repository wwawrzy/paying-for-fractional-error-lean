import Paper.Owners.Construction.SharpOwnerSurvival
import Paper.Owners.Construction.OwnerGraphCount

namespace Paper.SharpOwnerDensity
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerExperiment OwnerEdgeCylinder SharpOwnerExperiment FiniteMeanIncidence
open scoped BigOperators
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type} [Fintype A] [DecidableEq A]

theorem mask_lift (I : Finset V) (L : ℕ) (hL : 1 ≤ L) (ω : Outcomes (V := V) L) :
    OwnerMask.mask I hL (lift I L hL ω) = lift I L hL ω := by
  funext z
  cases z with
  | inl d =>
    by_cases hd : d ∈ I
    · simp only [OwnerMask.mask, if_pos hd]
    · simp [OwnerMask.mask, lift, hd]
  | inr v => rfl

theorem count (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (J : SimpleGraph A)
    [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e) (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, J.Adj x y →
      (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    (J.edgeFinset.card : ℝ) ≤ 2*a*L*Fintype.card A := by
  classical
  let I := Finset.univ.image e
  have hIsub : I ⊆ D := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact heD y
  have hIc : I.card = Fintype.card A := by
    simp only [I, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  letI : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  let Ω := Outcomes (V := V) L
  let P : J.Dart → Ω → Prop := fun d ω => Survives G D R L (lift I L hL ω) (e d.fst) (e d.snd)
  have hlow (d : J.Dart) : Fintype.card Ω ≤ (4*L)*(Finset.univ.filter (P d)).card := by
    exact SharpOwnerSurvival.count G D R I L hL
      (Finset.mem_image.mpr ⟨d.fst, Finset.mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨d.snd, Finset.mem_univ _, rfl⟩) (hedge _ _ d.adj)
  have hhigh (ω : Ω) : ((Finset.univ.filter (fun d => P d ω)).card : ℝ) ≤
      2*a*(I.filter (fun d => ω.1 d = 0)).card := by
    have hc := OwnerGraphCount.alive_card G D R I L hL J e hinj (lift I L hL ω)
    dsimp only [OwnerGraphCount.alive] at hc
    rw [mask_lift] at hc
    have hc' : ((Finset.univ.filter (fun d => P d ω)).card : ℝ) ≤
        2*((OwnerExperiment.graph G D R L (lift I L hL ω)).edgeFinset.card : ℝ) := by
      exact_mod_cast hc
    have hd := hden (sampled D (lift I L hL ω)) (OwnerExperiment.graph G D R L (lift I L hL ω))
      ⟨OwnerSampleMinor.model G D R L (lift I L hL ω)⟩
    rw [Fintype.card_coe] at hd
    have hcards := congrArg Finset.card (sampled_eq D I hIsub L hL ω)
    rw [hcards] at hd
    nlinarith
  have hh := FiniteMeanIncidence.bound P (4*L)
    (fun ω => 2*a*(I.filter (fun d => ω.1 d = 0)).card) hlow hhigh
  have hm := FiniteMeanIncidence.mean_selected L I
  have hm' : 2*(∑ ω : Ω, ((I.filter (fun d => ω.1 d = 0)).card : ℝ)) =
      (I.card : ℝ)*Fintype.card Ω := by exact_mod_cast hm
  have hsumeq : (∑ ω : Ω, ((I.filter (fun d => ω.1 d = 0)).card : ℝ)) =
      (I.card : ℝ)*Fintype.card Ω/2 := by linarith
  have hdarts : (Fintype.card J.Dart : ℝ) = 2*(J.edgeFinset.card : ℝ) := by
    exact_mod_cast SimpleGraph.dart_card_eq_twice_card_edges J
  rw [← Finset.mul_sum, hsumeq, hdarts, hIc] at hh
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hh' : (J.edgeFinset.card : ℝ)*(2*Fintype.card Ω) ≤
      (2*a*L*Fintype.card A)*(2*Fintype.card Ω) := by
    convert hh using 1 <;> push_cast <;> ring
  exact (mul_le_mul_iff_of_pos_right (by positivity : (0 : ℝ) < 2*Fintype.card Ω)).mp hh'

theorem augmented_density (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    Incidence.InducedDensityBound (OwnerInteraction.augmentedGraph G D R L) (2*a*L) := by
  classical
  intro S
  let J := (OwnerInteraction.augmentedGraph G D R L).induce (S : Set D)
  let e : ↥(S : Set D) → V := fun x => x.val.val
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext (Subtype.ext he)
  have heD : ∀ x : (S : Set D), e x ∈ D := fun x => x.val.property
  have hedge : ∀ x y : (S : Set D), J.Adj x y →
      (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩ := fun _ _ h => h
  have hh := count G D R L hL J e hinj heD hedge hden ha
  change (J.edgeFinset.card : ℝ) ≤ _
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh

end Paper.SharpOwnerDensity
