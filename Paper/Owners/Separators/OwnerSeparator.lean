import Paper.Owners.Construction.OwnerPhysicalVertices
import Paper.Owners.Construction.OwnerGraphCount
import Paper.Partitions.Separators.GuardedSeparator
import Paper.Preliminaries.MinorInheritance
import Paper.Partitions.Separators.SeparatorProfile

/-! Actual owner separators follow from physical minor density, constructed
owner-edge walks and the proved weighted separator. No separator oracle. -/
namespace Paper.OwnerSeparator
attribute [local instance] Classical.propDecidable Classical.decEq
open DeletionComponents
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def physicalFactor (a : ℝ) (L : ℕ) : ℝ := 1 + 6 * (a * ((L + 1 : ℕ) : ℝ) ^ 4)
noncomputable def constant (a : ℝ) (h L : ℕ) : ℝ := 2 * (h : ℝ) ^ 2 * L * Real.sqrt (physicalFactor a L)

theorem constant_pos (a : ℝ) (ha : 0 ≤ a) (h L : ℕ) (hh : 1 ≤ h) (hL : 1 ≤ L) :
    0 < constant a h L := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hL' : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hκ : 0 < physicalFactor a L := by unfold physicalFactor; positivity
  have hs := Real.sqrt_pos.mpr hκ
  unfold constant
  positivity

set_option maxHeartbeats 2000000 in
theorem represented (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (K : SimpleGraph A) [DecidableRel K.Adj]
    (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
    (hedge : ∀ a b, K.Adj a b → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    ∃ X : Finset A, (X.card : ℝ) ≤ constant a h L * Real.sqrt (Fintype.card A) ∧
      ∀ C : (deleted K X).ConnectedComponent,
        ((physical K X C).card : ℝ) ≤ (Fintype.card A : ℝ) / 2 := by
  classical
  let W := OwnerPhysicalVertices.vertices G D R L K e heD hedge
  let S := OwnerPhysicalVertices.restricted G D R L K e hinj heD hedge
  have hlabels : ∀ v, (S.labels v).card ≤ L := OwnerPhysicalVertices.restricted_labels G D R L K e hinj heD hedge hL
  have hnat := OwnerPhysicalVertices.card_bound G D R L K e hinj heD hedge
  have hreal : (W.card : ℝ) ≤ Fintype.card A + 6 * (K.edgeFinset.card : ℝ) := by exact_mod_cast hnat
  have hcount := OwnerGraphCount.count G D R L hL K e hinj heD hedge hden ha
  have hsize : (Fintype.card ↥(W : Set V) : ℝ) ≤ physicalFactor a L * Fintype.card A := by
    have hs : (W.card : ℝ) ≤ physicalFactor a L * Fintype.card A := by
      dsimp only [physicalFactor]
      nlinarith
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hs
  have hκ : 0 ≤ physicalFactor a L := by unfold physicalFactor; positivity
  have hs := GuardedSeparator.proportional S L hlabels (MinorInheritance.induced G hden W) ha h hh
    (physicalFactor a L) hκ hsize
  exact hs

theorem represented_profile (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (K : SimpleGraph A) [DecidableRel K.Adj] (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
    (hedge : ∀ a b, K.Adj a b → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    SeparatorProfile.Bound K (constant a h L) := by
  classical
  intro I
  let J := K.induce (I : Set A)
  let e' : ↥(I : Set A) → V := fun x => e x.val
  have hinj' : Function.Injective e' := fun _ _ he => Subtype.ext (hinj he)
  have heD' : ∀ x, e' x ∈ D := fun x => heD x.val
  have hh' := represented G D R L hL J e' hinj' heD' (fun x y h => hedge x.val y.val h) hden ha h hh
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh'

theorem augmented_profile (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    SeparatorProfile.Bound (OwnerInteraction.augmentedGraph G D R L) (constant a h L) := by
  classical
  intro I
  let K := (OwnerInteraction.augmentedGraph G D R L).induce (I : Set D)
  let e : ↥(I : Set D) → V := fun x => x.val.val
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext (Subtype.ext he)
  have heD : ∀ x, e x ∈ D := fun x => x.val.property
  have hh' := represented G D R L hL K e hinj heD (fun _ _ h => h) hden ha h hh
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh'

theorem actual_profile (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (h : ℕ) (hh : 2 * a + 1 < h) :
    SeparatorProfile.Bound (OwnerInteraction.graph G D R L) (constant a h L) := by
  classical
  intro I
  let K := (OwnerInteraction.graph G D R L).induce (I : Set D)
  let e : ↥(I : Set D) → V := fun x => x.val.val
  have hinj : Function.Injective e := fun _ _ he => Subtype.ext (Subtype.ext he)
  have heD : ∀ x, e x ∈ D := fun x => x.val.property
  have hh' := represented G D R L hL K e hinj heD
    (fun _ _ h => OwnerInteraction.graph_le_augmented G D R L h) hden ha h hh
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh'
end Paper.OwnerSeparator
