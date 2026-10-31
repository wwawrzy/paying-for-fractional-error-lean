import Paper.Owners.Construction.OwnerMask

/-! Four-coordinate finite cylinders preserve each augmented owner edge.
Owner and candidate coordinates have separate sum tags, even at one vertex. -/
namespace Paper.OwnerEdgeCylinder
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair OwnerExperiment
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def pattern (L : ℕ) (hL : 1 ≤ L) (i j v : V) (slot : Fin (L + 1)) : V ⊕ V → Fin (L + 1)
  | .inl d => if d = i ∨ d = j then 0 else ⟨1, by omega⟩
  | .inr u => if u = v then slot else 0

def Survives {c : ℕ} (D R : Finset V) (L : ℕ) (ω : V ⊕ V → Fin c) (i j : V) : Prop :=
  i ∈ sampled D ω ∧ j ∈ sampled D ω ∧ BlowupEdge.Crosses G (label G D R L ω) i j

theorem cylinder_survives (D R I : Finset V) (L : ℕ) (hL : 1 ≤ L)
    {i j : D} (hiI : i.val ∈ I) (hjI : j.val ∈ I)
    (hab : (OwnerInteraction.augmentedGraph G D R L).Adj i j) :
    ∃ F : Finset (V ⊕ V), F.card ≤ 4 ∧ ∃ target : V ⊕ V → Fin (L + 1),
      ∀ ω ∈ FiniteCylinder.cylinder F target,
        Survives G D R L (OwnerMask.mask I hL ω) i.val j.val := by
  classical
  letI : DecidableLE V := fun a b => Classical.propDecidable (a ≤ b)
  obtain ⟨hne, v, hi, hj⟩ := hab
  have hv : v ∉ heavy G D R L := by
    intro hv
    simp [OwnerInteraction.lightSupport, hv] at hi
  have hiW : i.val ∈ support G D R v := by simpa [OwnerInteraction.lightSupport, hv] using hi
  have hjW : j.val ∈ support G D R v := by simpa [OwnerInteraction.lightSupport, hv] using hj
  have hne' : i.val ≠ j.val := fun he => hne (Subtype.ext he)
  have hcard : (support G D R v).card ≤ L := by
    have hh : ¬ L < (support G D R v).card := fun h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  have hmem := (Finset.mem_sort (· ≤ ·)).mpr hiW
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hmem
  have hnlt : n < L + 1 := by
    have hh := (List.getElem?_eq_some_iff.mp hn).choose
    have hh' : n < (support G D R v).card := by simpa only [Finset.length_sort] using hh
    omega
  let slot : Fin (L + 1) := ⟨n, hnlt⟩
  let target := pattern L hL i.val j.val v slot
  let F : Finset (V ⊕ V) := {.inl i.val, .inl j.val, .inl (owner G D v), .inr v}
  refine ⟨F, ?_, target, ?_⟩
  · dsimp [F]
    have h₀ := Finset.card_insert_le (Sum.inl i.val) ({.inl j.val, .inl (owner G D v), .inr v} : Finset (V ⊕ V))
    have h₁ := Finset.card_insert_le (Sum.inl j.val) ({.inl (owner G D v), .inr v} : Finset (V ⊕ V))
    have h₂ := Finset.card_insert_le (Sum.inl (owner G D v)) ({.inr v} : Finset (V ⊕ V))
    simp only [Finset.card_singleton] at h₂
    omega
  · intro ω₀ hω
    let ω := OwnerMask.mask I hL ω₀
    change Survives G D R L ω i.val j.val
    have he₀ : ∀ z ∈ F, ω₀ z = target z := (Finset.mem_filter.mp hω).2
    have he : ∀ z ∈ F, ω z = target z := by
      intro z hz
      cases z with
      | inl d =>
        by_cases hd : d ∈ I
        · simpa only [ω, OwnerMask.mask, if_pos hd] using he₀ (.inl d) hz
        · have hdi : d ≠ i.val := fun h => hd (h ▸ hiI)
          have hdj : d ≠ j.val := fun h => hd (h ▸ hjI)
          simp [ω, OwnerMask.mask, hd, target, pattern, hdi, hdj]
      | inr u => exact he₀ (.inr u) hz
    have hii : i.val ∈ sampled D ω := by
      refine Finset.mem_filter.mpr ⟨i.property, ?_⟩
      rw [he (.inl i.val) (by simp [F])]
      simp [target, pattern]
    have hjj : j.val ∈ sampled D ω := by
      refine Finset.mem_filter.mpr ⟨j.property, ?_⟩
      rw [he (.inl j.val) (by simp [F])]
      simp [target, pattern]
    have hvlab : label G D R L ω v = some i.val ∨ label G D R L ω v = some j.val := by
      by_cases hvi : owner G D v = i.val
      · left
        have hh := label_base G D R L ω (v := v) (by simpa only [hvi] using hii)
        simpa only [hvi] using hh
      by_cases hvj : owner G D v = j.val
      · right
        have hh := label_base G D R L ω (v := v) (by simpa only [hvj] using hjj)
        simpa only [hvj] using hh
      have hnot : owner G D v ∉ sampled D ω := by
        intro hmem
        have hz := (Finset.mem_filter.mp hmem).2
        rw [he (.inl (owner G D v)) (by simp [F])] at hz
        simp [target, pattern, hvi, hvj] at hz
      have hpick : pick G D R ω v = some i.val := by
        have hs : ω (.inr v) = slot := by
          rw [he (.inr v) (by simp [F])]
          simp [target, pattern]
        simpa only [pick, hs, slot] using hn
      left
      simp only [label, if_neg hnot, if_neg hv, hpick]
      exact if_pos hii
    obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hiW
    obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp hjW
    have hulab : label G D R L ω u = some i.val := by
      have hh := label_base G D R L ω (v := u) (by simpa only [hui] using hii)
      simpa only [hui] using hh
    have hwlab : label G D R L ω w = some j.val := by
      have hh := label_base G D R L ω (v := w) (by simpa only [hwj] using hjj)
      simpa only [hwj] using hh
    refine ⟨hii, hjj, ?_⟩
    apply BlowupEdge.path_crosses G (label G D R L ω) hne' u v w w hulab hwlab hvlab (Or.inr hwlab)
    · exact ((mem_closed G u v).mp (Finset.mem_inter.mp hu).1).elim Or.inl (fun ha => Or.inr ha.symm)
    · exact ((mem_closed G w v).mp (Finset.mem_inter.mp hw).1).elim (fun he => Or.inl he.symm) Or.inr
    · exact Or.inl rfl
end Paper.OwnerEdgeCylinder
