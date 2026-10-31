import Paper.Owners.Construction.OwnerUndirectedRoutes
import Paper.Owners.Construction.SharpOwnerDensity
import Paper.Partitions.Separators.SharpGuardedSeparator
import Paper.Preliminaries.MinorInheritance
import Paper.Partitions.Separators.SeparatorBalance

/-! Exact owner separator constant with one route per edge,
exact 2aL density and the proved sharp excluded-clique weighted separator. -/
namespace Paper.SharpOwnerSeparator
attribute [local instance] Classical.propDecidable Classical.decEq
open DeletionComponents
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable def physicalFactor (a : ℝ) (L : ℕ) : ℝ := 1+3*(2*a*L)
noncomputable def constant (a : ℝ) (s L : ℕ) : ℝ :=
  (s : ℝ)^(3/2 : ℝ)*L*Real.sqrt (physicalFactor a L)

theorem represented (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (K : SimpleGraph A) [DecidableRel K.Adj]
    (e : A → V) (hinj : Function.Injective e) (heD : ∀ a, e a ∈ D)
    (hedge : ∀ a b, K.Adj a b → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e a, heD a⟩ ⟨e b, heD b⟩)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (s : ℕ) (hs : 2*a+1 < s) :
    ∃ X : Finset A, (X.card : ℝ) ≤ constant a s L*Real.sqrt (Fintype.card A) ∧
      ∀ C : (deleted K X).ConnectedComponent,
        ((physical K X C).card : ℝ) ≤ (Fintype.card A : ℝ)/2 := by
  classical
  let W := OwnerUndirectedRoutes.vertices G D R L K e heD hedge
  let S := OwnerUndirectedRoutes.restricted G D R L K e hinj heD hedge
  have hlabels : ∀ v, (S.labels v).card ≤ L :=
    OwnerUndirectedRoutes.label_bound G D R L K e hinj heD hedge hL
  have hnat := OwnerUndirectedRoutes.card_bound G D R L K e hinj heD hedge
  have hreal : (W.card : ℝ) ≤ Fintype.card A+3*(K.edgeFinset.card : ℝ) := by exact_mod_cast hnat
  have hcount := SharpOwnerDensity.count G D R L hL K e hinj heD hedge hden ha
  have hsize : (Fintype.card ↥(W : Set V) : ℝ) ≤ physicalFactor a L*Fintype.card A := by
    have hh : (W.card : ℝ) ≤ physicalFactor a L*Fintype.card A := by
      dsimp only [physicalFactor]
      nlinarith
    simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh
  have hκ : 0 ≤ physicalFactor a L := by unfold physicalFactor; positivity
  have hs1 : 1 ≤ s := by
    have hp : (1 : ℝ) ≤ s := by linarith
    exact_mod_cast hp
  have hfree := SharpExcludedSeparator.excludes_clique (G.induce (W : Set V)) ha
    (MinorInheritance.induced G hden W) s hs
  exact SharpGuardedSeparator.proportional S L hlabels s hs1 hfree (physicalFactor a L) hκ hsize

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
/-- Exactly the source two-thirds profile with C=s^(3/2)L sqrt(1+3C_L)
and C_L=2aL; the proved intermediate profile is even half-balanced. -/
theorem published_profile (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) (s : ℕ) (hs : 2*a+1 < s) :
    SeparatorBalance.Bound (OwnerInteraction.augmentedGraph G D R L) (constant a s L) (2/3) := by
  intro I
  obtain ⟨X, hX, hbal⟩ := augmented_profile G D R L hL hden ha s hs I
  refine ⟨X, hX, ?_⟩
  intro C
  have hb := hbal C
  have hn : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  linarith

end Paper.SharpOwnerSeparator
