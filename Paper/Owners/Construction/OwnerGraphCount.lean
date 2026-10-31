import Paper.Owners.Construction.OwnerEdgeCylinder
import Paper.Averaging.Tasks.FiniteIncidenceAverage

/-! Finite counting of every graph injectively represented by owner labels.
The experiment is masked to precisely the represented owner set. -/
namespace Paper.OwnerGraphCount
attribute [local instance] Classical.propDecidable Classical.decEq
open OwnerExperiment OwnerEdgeCylinder
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def alive (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L) (J : SimpleGraph A)
    [DecidableRel J.Adj] (e : A → V) (ω : V ⊕ V → Fin (L + 1)) : Finset J.Dart :=
  Finset.univ.filter (fun d => Survives G D R L (OwnerMask.mask I hL ω) (e d.fst) (e d.snd))

theorem alive_card (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L) (J : SimpleGraph A)
    [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e) (ω : V ⊕ V → Fin (L + 1)) :
    (alive G D R I L hL J e ω).card ≤
      2 * (OwnerExperiment.graph G D R L (OwnerMask.mask I hL ω)).edgeFinset.card := by
  classical
  let K := OwnerExperiment.graph G D R L (OwnerMask.mask I hL ω)
  let E := alive G D R I L hL J e ω
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

set_option maxHeartbeats 2000000 in
theorem count (D R : Finset V) (L : ℕ) (hL : 1 ≤ L) (J : SimpleGraph A)
    [DecidableRel J.Adj] (e : A → V) (hinj : Function.Injective e) (heD : ∀ x, e x ∈ D)
    (hedge : ∀ x y, J.Adj x y → (OwnerInteraction.augmentedGraph G D R L).Adj ⟨e x, heD x⟩ ⟨e y, heD y⟩)
    {a : ℝ} (hden : MinorDensity.Bound G a) (ha : 0 ≤ a) :
    (J.edgeFinset.card : ℝ) ≤ a * ((L + 1 : ℕ) : ℝ) ^ 4 * Fintype.card A := by
  classical
  let I := Finset.univ.image e
  have hIc : I.card = Fintype.card A := by simp only [I, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  let W : Finset (V ⊕ V → Fin (L + 1)) := Finset.univ
  have hW : W.Nonempty := ⟨fun _ => 0, Finset.mem_univ _⟩
  have hh : (Fintype.card J.Dart : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ 4 * (2 * a * Fintype.card A) := by
    rw [← Nat.cast_pow, ← Finset.card_univ (α := J.Dart)]
    apply FiniteIncidenceAverage.bound Finset.univ W hW
      (fun d ω => Survives G D R L (OwnerMask.mask I hL ω) (e d.fst) (e d.snd)) ((L + 1) ^ 4) (2 * a * Fintype.card A)
    · intro d _
      have hiI : e d.fst ∈ I := Finset.mem_image.mpr ⟨d.fst, Finset.mem_univ _, rfl⟩
      have hjI : e d.snd ∈ I := Finset.mem_image.mpr ⟨d.snd, Finset.mem_univ _, rfl⟩
      obtain ⟨F, hF, target, ht⟩ := cylinder_survives G D R I L hL hiI hjI (hedge _ _ d.adj)
      have hs : FiniteCylinder.cylinder F target ⊆ W.filter
          (fun ω => Survives G D R L (OwnerMask.mask I hL ω) (e d.fst) (e d.snd)) := by
        intro ω hω
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht ω hω⟩
      have hc := FiniteCylinder.bounded_coordinates F target 4 (by omega) hF
      have hc' : W.card ≤ (L + 1) ^ 4 * (FiniteCylinder.cylinder F target).card := by
        simpa only [W, Finset.card_univ] using hc
      exact hc'.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hs))
    · intro ω _
      have hc := alive_card G D R I L hL J e hinj ω
      have hc' : ((alive G D R I L hL J e ω).card : ℝ) ≤
          2 * ((OwnerExperiment.graph G D R L (OwnerMask.mask I hL ω)).edgeFinset.card : ℝ) := by exact_mod_cast hc
      have hd := OwnerMask.density G D R I hL ω hden ha
      rw [hIc] at hd
      exact hc'.trans (by nlinarith [hd])
  rw [SimpleGraph.dart_card_eq_twice_card_edges] at hh
  push_cast at hh ⊢
  nlinarith
end Paper.OwnerGraphCount
