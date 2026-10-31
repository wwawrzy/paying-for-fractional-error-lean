import Paper.Solver.LocalSearch.GeneralCoveringOwnerExperiment
import Paper.Preliminaries.FiniteCylinder

/-! Four-coordinate survival for the actual optional-C-owner experiment.
The owner bit and candidate pick have separate sum tags. An absent owner
contributes no coordinate. Sampling and the mask are proof-side only;
hereditary owner density and edge counting are not assumed or proved here. -/
namespace Paper.GeneralCoveringOwnerEdgeCylinder
open SevenFoundation GeneralCoveringTaskGeometry GeneralCoveringOwnerExperiment
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def mask (I : Finset V) {L : ℕ} (hL : 1 ≤ L)
    (ω : V ⊕ V → Fin (L + 1)) : V ⊕ V → Fin (L + 1)
  | .inl d => if d ∈ I then ω (.inl d) else ⟨1, by omega⟩
  | .inr v => ω (.inr v)

theorem sampled_subset (D I : Finset V) {L : ℕ} (hL : 1 ≤ L)
    (ω : V ⊕ V → Fin (L + 1)) : sampled D (mask I hL ω) ⊆ I := by
  intro d hd
  have hz := (Finset.mem_filter.mp hd).2
  by_contra hn
  simp [mask, hn] at hz

def pattern (L : ℕ) (hL : 1 ≤ L) (i j v : V) (slot : Fin (L + 1)) :
    V ⊕ V → Fin (L + 1)
  | .inl d => if d = i ∨ d = j then 0 else ⟨1, by omega⟩
  | .inr u => if u = v then slot else 0

def coordinates (i j v : V) (o : Option V) : Finset (V ⊕ V) :=
  {.inl i, .inl j, .inr v} ∪ o.toFinset.image Sum.inl

theorem coordinates_none (i j v : V) :
    coordinates i j v none = {.inl i, .inl j, .inr v} := by simp [coordinates]

theorem coordinates_bound (i j v : V) (o : Option V) :
    (coordinates i j v o).card ≤ 4 := by
  have h₀ : ({Sum.inl i, Sum.inl j, Sum.inr v} : Finset (V ⊕ V)).card ≤ 3 := by
    have h₁ := Finset.card_insert_le (Sum.inl i) ({Sum.inl j, Sum.inr v} : Finset (V ⊕ V))
    have h₂ := Finset.card_insert_le (Sum.inl j) ({Sum.inr v} : Finset (V ⊕ V))
    simp only [Finset.card_singleton] at h₂
    omega
  have ho : o.toFinset.card ≤ 1 := by cases o <;> simp
  have him : (o.toFinset.image (Sum.inl : V → V ⊕ V)).card ≤ 1 :=
    Finset.card_image_le.trans ho
  exact (Finset.card_union_le _ _).trans (by omega)

/-- Normalize only the imported cylinder's membership predicate. This
does not install an equality or proposition-decision instance. -/
theorem cylinder_agrees (F : Finset (V ⊕ V)) {c : ℕ}
    (target ω : V ⊕ V → Fin c) (hω : ω ∈ FiniteCylinder.cylinder F target) :
    ∀ z ∈ F, ω z = target z := by
  unfold FiniteCylinder.cylinder at hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
  have heq : (fun a b : V ⊕ V => Classical.propDecidable (a = b)) =
      (inferInstance : DecidableEq (V ⊕ V)) := Subsingleton.elim _ _
  simpa only [heq] using hω

def Survives {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) (i j : V) : Prop :=
  i ∈ sampled D ω ∧ j ∈ sampled D ω ∧
    BlowupEdge.Crosses G (label G C D R L ω) i j

theorem label_from_pick {c : ℕ} (C : V → Finset V) (D R : Finset V) (L : ℕ)
    (ω : V ⊕ V → Fin c) {v i : V}
    (hb : ¬ ∃ d, GeneralCoveringOwners.owner C D R v = some d ∧ d ∈ sampled D ω)
    (hp : pick G C D R L ω v = some i) (hi : i ∈ sampled D ω) :
    label G C D R L ω v = some i := by
  rw [label, if_neg hb, hp]
  exact if_pos hi

/-- Each true gated owner edge survives on an explicit finite cylinder.
No locality beyond the accepted S0 definition is needed for this step. -/
theorem cylinder_survives (C : V → Finset V) (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {i j : D} (hiI : i.val ∈ I) (hjI : j.val ∈ I)
    (hab : (ownerGraph G C D R L).Adj i j) :
    ∃ F : Finset (V ⊕ V), F.card ≤ 4 ∧ ∃ target : V ⊕ V → Fin (L + 1),
      ∀ ω ∈ FiniteCylinder.cylinder F target,
        Survives G C D R L (mask I hL ω) i.val j.val := by
  obtain ⟨hne, v, hi, hj⟩ := hab
  have hiS := (mem_lightSupport G C D R L v i.val).mp hi
  have hjS := (mem_lightSupport G C D R L v j.val).mp hj
  have hne' : i.val ≠ j.val := fun he => hne (Subtype.ext he)
  have hcard := lightSupport_bound G C D R L v
  have hmem := (Finset.mem_sort (· ≤ ·)).mpr hi
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hmem
  have hnlt : n < L + 1 := by
    have hh := (List.getElem?_eq_some_iff.mp hn).choose
    have hh' : n < (lightSupport G C D R L v).card := by
      simpa only [Finset.length_sort] using hh
    omega
  let slot : Fin (L + 1) := ⟨n, hnlt⟩
  let target := pattern L hL i.val j.val v slot
  let F := coordinates i.val j.val v (GeneralCoveringOwners.owner C D R v)
  refine ⟨F, coordinates_bound i.val j.val v _, target, ?_⟩
  intro ω₀ hω
  let ω := mask I hL ω₀
  change Survives G C D R L ω i.val j.val
  have he₀ := cylinder_agrees F target ω₀ hω
  have he : ∀ z ∈ F, ω z = target z := by
    intro z hz
    cases z with
    | inl d =>
      by_cases hd : d ∈ I
      · simpa only [ω, mask, if_pos hd] using he₀ (.inl d) hz
      · have hdi : d ≠ i.val := fun h => hd (h ▸ hiI)
        have hdj : d ≠ j.val := fun h => hd (h ▸ hjI)
        simp [ω, mask, hd, target, pattern, hdi, hdj]
    | inr u => exact he₀ (.inr u) hz
  have hii : i.val ∈ sampled D ω := by
    refine Finset.mem_filter.mpr ⟨i.property, ?_⟩
    rw [he (.inl i.val) (by simp [F, coordinates])]
    simp [target, pattern]
  have hjj : j.val ∈ sampled D ω := by
    refine Finset.mem_filter.mpr ⟨j.property, ?_⟩
    rw [he (.inl j.val) (by simp [F, coordinates])]
    simp [target, pattern]
  have hpick : pick G C D R L ω v = some i.val := by
    have hs : ω (.inr v) = slot := by
      rw [he (.inr v) (by simp [F, coordinates])]
      simp [target, pattern]
    simpa only [pick, hs, slot] using hn
  have hvlab : label G C D R L ω v = some i.val ∨ label G C D R L ω v = some j.val := by
    cases ho : GeneralCoveringOwners.owner C D R v with
    | none =>
      have hb : ¬ ∃ d, GeneralCoveringOwners.owner C D R v = some d ∧ d ∈ sampled D ω := by
        rintro ⟨d, hd, _⟩
        rw [ho] at hd
        cases hd
      exact Or.inl (label_from_pick G C D R L ω hb hpick hii)
    | some d =>
      by_cases hdi : d = i.val
      · exact Or.inl (label_base G C D R L ω (hdi ▸ ho) hii)
      by_cases hdj : d = j.val
      · exact Or.inr (label_base G C D R L ω (hdj ▸ ho) hjj)
      have hnot : d ∉ sampled D ω := by
        intro hd
        have hz := (Finset.mem_filter.mp hd).2
        rw [he (.inl d) (by simp [F, coordinates, ho])] at hz
        simp [target, pattern, hdi, hdj] at hz
      have hb : ¬ ∃ e, GeneralCoveringOwners.owner C D R v = some e ∧ e ∈ sampled D ω := by
        rintro ⟨e, he, hs⟩
        have hde : d = e := Option.some.inj (ho.symm.trans he)
        exact hnot (hde.symm ▸ hs)
      exact Or.inl (label_from_pick G C D R L ω hb hpick hii)
  obtain ⟨u, hu, hui⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v i.val).mp hiS.2.2
  obtain ⟨w, hw, hwj⟩ := (GeneralCoveringOwnerSupport.mem_support G C D R v j.val).mp hjS.2.2
  have hulab := label_base G C D R L ω hui hii
  have hwlab := label_base G C D R L ω hwj hjj
  refine ⟨hii, hjj, ?_⟩
  apply BlowupEdge.path_crosses G (label G C D R L ω) hne' u v w w hulab hwlab hvlab (Or.inr hwlab)
  · exact ((mem_closed G u v).mp hu).elim Or.inl (fun ha => Or.inr ha.symm)
  · exact ((mem_closed G w v).mp hw).elim (fun he => Or.inl he.symm) Or.inr
  · exact Or.inl rfl

end Paper.GeneralCoveringOwnerEdgeCylinder

#print axioms Paper.GeneralCoveringOwnerEdgeCylinder.sampled_subset
#print axioms Paper.GeneralCoveringOwnerEdgeCylinder.coordinates_none
#print axioms Paper.GeneralCoveringOwnerEdgeCylinder.coordinates_bound
#print axioms Paper.GeneralCoveringOwnerEdgeCylinder.cylinder_agrees
#print axioms Paper.GeneralCoveringOwnerEdgeCylinder.label_from_pick
#print axioms Paper.GeneralCoveringOwnerEdgeCylinder.cylinder_survives
