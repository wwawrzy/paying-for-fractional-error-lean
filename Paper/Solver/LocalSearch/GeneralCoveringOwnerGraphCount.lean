import Paper.Solver.LocalSearch.GeneralCoveringOwnerEdgeCylinder
import Paper.Averaging.Tasks.FiniteIncidenceAverage

/-! Finite counting from the actual optional-C-owner experiment. Masked
outcomes are physical minors; each represented edge survives a cylinder
with at most four coordinates. The coefficient a*(L+1)^4 is coarse.
This is proof-side analysis, with no randomized runtime or sharp2aL claim. -/
namespace Paper.GeneralCoveringOwnerGraphCount
open SevenFoundation GeneralCoveringTaskGeometry GeneralCoveringOwnerExperiment
open GeneralCoveringOwnerEdgeCylinder
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance sampledAdj {c : ℕ} (C : V → Finset V) (D R : Finset V)
    (L : ℕ) (ω : V ⊕ V → Fin c) :
    DecidableRel (GeneralCoveringOwnerExperiment.graph G C D R L ω).Adj :=
  fun _ _ => Classical.propDecidable _

noncomputable local instance ownerAdj (C : V → Finset V) (D R : Finset V) (L : ℕ) :
    DecidableRel (ownerGraph G C D R L).Adj := fun _ _ => Classical.propDecidable _

noncomputable local instance survivalDecision {c : ℕ} (C : V → Finset V) (D R : Finset V)
    (L : ℕ) (ω : V ⊕ V → Fin c) (i j : V) :
    Decidable (Survives G C D R L ω i j) := Classical.propDecidable _

theorem sampled_density (C : V → Finset V) (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (ω : V ⊕ V → Fin (L + 1)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    ((GeneralCoveringOwnerExperiment.graph G C D R L (mask I hL ω)).edgeFinset.card : ℝ) ≤
      a * I.card := by
  have hh := hden (sampled D (mask I hL ω))
    (GeneralCoveringOwnerExperiment.graph G C D R L (mask I hL ω))
    ⟨GeneralCoveringOwnerExperiment.model G C D R L _ hlocal⟩
  have hc : Fintype.card (sampled D (mask I hL ω)) ≤ I.card := by
    rw [Fintype.card_coe]
    exact Finset.card_le_card (GeneralCoveringOwnerEdgeCylinder.sampled_subset D I hL ω)
  have hc' : (Fintype.card (sampled D (mask I hL ω)) : ℝ) ≤ I.card := by exact_mod_cast hc
  exact hh.trans (mul_le_mul_of_nonneg_left hc' ha)

/-- The finite cylinder's function enumeration is transported to native
index equality locally; no equality instance is installed. -/
theorem survival_card (C : V → Finset V) (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {i j : D} (hiI : i.val ∈ I) (hjI : j.val ∈ I)
    (hab : (ownerGraph G C D R L).Adj i j) :
    Fintype.card (V ⊕ V → Fin (L + 1)) ≤ (L + 1) ^ 4 *
      ((Finset.univ : Finset (V ⊕ V → Fin (L + 1))).filter
        (fun ω => Survives G C D R L (mask I hL ω) i.val j.val)).card := by
  obtain ⟨F, hF, target, ht⟩ := cylinder_survives G C D R I L hL hiI hjI hab
  have hs : FiniteCylinder.cylinder F target ⊆
      (Finset.univ : Finset (V ⊕ V → Fin (L + 1))).filter
        (fun ω => Survives G C D R L (mask I hL ω) i.val j.val) := by
    intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht ω hω⟩
  have hc := FiniteCylinder.bounded_coordinates F target 4 (by omega) hF
  have heq : (fun x y : V ⊕ V => Classical.propDecidable (x = y)) =
      (inferInstance : DecidableEq (V ⊕ V)) := Subsingleton.elim _ _
  have hc' : Fintype.card (V ⊕ V → Fin (L + 1)) ≤
      (L + 1) ^ 4 * (FiniteCylinder.cylinder F target).card := by
    simpa only [heq] using hc
  exact hc'.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hs))

variable {A : Type} [Fintype A] [DecidableEq A]

noncomputable def alive (C : V → Finset V) (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (J : SimpleGraph A) [DecidableRel J.Adj] (e : A → V)
    (ω : V ⊕ V → Fin (L + 1)) : Finset J.Dart :=
  Finset.univ.filter (fun d => Survives G C D R L (mask I hL ω) (e d.fst) (e d.snd))

theorem alive_card (C : V → Finset V) (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (J : SimpleGraph A) [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e)
    (ω : V ⊕ V → Fin (L + 1)) :
    (alive G C D R I L hL J e ω).card ≤
      2 * (GeneralCoveringOwnerExperiment.graph G C D R L (mask I hL ω)).edgeFinset.card := by
  let K := GeneralCoveringOwnerExperiment.graph G C D R L (mask I hL ω)
  let E := alive G C D R I L hL J e ω
  let f : E → K.Dart := fun d => {
    toProd := (⟨e d.val.fst, (Finset.mem_filter.mp d.property).2.1⟩,
      ⟨e d.val.snd, (Finset.mem_filter.mp d.property).2.2.1⟩)
    adj := ⟨fun he => d.val.adj.ne (hinj (congrArg Subtype.val he)),
      (Finset.mem_filter.mp d.property).2.2.2⟩ }
  have hf : Function.Injective f := by
    intro d g he
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    exact Prod.ext (hinj (congrArg (fun z : K.Dart => z.fst.val) he))
      (hinj (congrArg (fun z : K.Dart => z.snd.val) he))
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, SimpleGraph.dart_card_eq_twice_card_edges] using hc

theorem alive_density (C : V → Finset V) (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (J : SimpleGraph A) [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e)
    (ω : V ⊕ V → Fin (L + 1)) (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    ((alive G C D R I L hL J e ω).card : ℝ) ≤ 2 * a * I.card := by
  have hc := alive_card G C D R I L hL J e hinj ω
  have hc' : ((alive G C D R I L hL J e ω).card : ℝ) ≤
      2 * ((GeneralCoveringOwnerExperiment.graph G C D R L (mask I hL ω)).edgeFinset.card : ℝ) := by
    exact_mod_cast hc
  have hd := sampled_density G C D R I L hL ω hlocal hden ha
  exact hc'.trans (by nlinarith [hd])

theorem dart_bound (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (J : SimpleGraph A) [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e)
    (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, J.Adj x y → (ownerGraph G C D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    (Fintype.card J.Dart : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ 4 * (2 * a * Fintype.card A) := by
  let I := Finset.univ.image e
  have hIc : I.card = Fintype.card A := by
    simp only [I, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let W : Finset (V ⊕ V → Fin (L + 1)) := Finset.univ
  have hW : W.Nonempty := ⟨fun _ => 0, Finset.mem_univ _⟩
  rw [← Nat.cast_pow, ← Finset.card_univ (α := J.Dart)]
  apply FiniteIncidenceAverage.bound Finset.univ W hW
    (fun d ω => Survives G C D R L (mask I hL ω) (e d.fst) (e d.snd))
    ((L + 1) ^ 4) (2 * a * Fintype.card A)
  · intro d _
    have hiI : e d.fst ∈ I := Finset.mem_image.mpr ⟨d.fst, Finset.mem_univ _, rfl⟩
    have hjI : e d.snd ∈ I := Finset.mem_image.mpr ⟨d.snd, Finset.mem_univ _, rfl⟩
    simpa only [W, Finset.card_univ] using
      survival_card G C D R I L hL hiI hjI (hedge _ _ d.adj)
  · intro ω _
    have hh := alive_density G C D R I L hL J e hinj ω hlocal hden ha
    rw [hIc] at hh
    exact hh

theorem count (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (J : SimpleGraph A) [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e)
    (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, J.Adj x y → (ownerGraph G C D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    (J.edgeFinset.card : ℝ) ≤ a * ((L + 1 : ℕ) : ℝ) ^ 4 * Fintype.card A := by
  have hh := dart_bound G C D R L hL J e hinj heD hedge hlocal hden ha
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hh
  push_cast at hh ⊢
  nlinarith

/-- Hereditary induced density of the actual gated owner graph. This
constant is derived from physical minor density, not an additional oracle. -/
theorem induced_density (C : V → Finset V) (D R : Finset V) (L : ℕ) (hL : 1 ≤ L)
    (hlocal : ∀ r ∈ R, C r ⊆ closed G r)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    Incidence.InducedDensityBound (ownerGraph G C D R L) (a * ((L + 1 : ℕ) : ℝ) ^ 4) := by
  intro S
  let J := (ownerGraph G C D R L).induce (S : Set D)
  let e : ↥(S : Set D) → V := fun x => x.val.val
  have hinj : Function.Injective e := by
    intro x y he
    exact Subtype.ext (Subtype.ext he)
  have heD : ∀ x : (S : Set D), e x ∈ D := fun x => x.val.property
  have hedge : ∀ x y : (S : Set D), J.Adj x y →
      (ownerGraph G C D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩ := fun _ _ h => h
  have hh := count G C D R L hL J e hinj heD hedge hlocal hden ha
  change (J.edgeFinset.card : ℝ) ≤ _
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using hh

end Paper.GeneralCoveringOwnerGraphCount

#print axioms Paper.GeneralCoveringOwnerGraphCount.sampled_density
#print axioms Paper.GeneralCoveringOwnerGraphCount.survival_card
#print axioms Paper.GeneralCoveringOwnerGraphCount.alive_card
#print axioms Paper.GeneralCoveringOwnerGraphCount.alive_density
#print axioms Paper.GeneralCoveringOwnerGraphCount.dart_bound
#print axioms Paper.GeneralCoveringOwnerGraphCount.count
#print axioms Paper.GeneralCoveringOwnerGraphCount.induced_density
