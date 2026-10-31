import Paper.Preliminaries.FiniteCylinder

/-! Exact cardinalities of prescribed independent finite coordinates. -/
namespace Paper.FiniteCoordinateCount
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A] [DecidableEq A] {Q : ℕ}

noncomputable def split (F : Finset A) (target : A → Fin Q) :
    (A → Fin Q) ≃ (FiniteCylinder.cylinder F target) × (F → Fin Q) where
  toFun ω := (⟨FiniteCylinder.overwrite F target ω, FiniteCylinder.overwrite_mem F target ω⟩,
    fun x => ω x.val)
  invFun p v := if hv : v ∈ F then p.2 ⟨v, hv⟩ else p.1.val v
  left_inv ω := by
    funext v
    by_cases hv : v ∈ F <;> simp [FiniteCylinder.overwrite, hv]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      funext v
      by_cases hv : v ∈ F
      · have h := (Finset.mem_filter.mp p.1.property).2 v hv
        simpa only [FiniteCylinder.overwrite, if_pos hv] using h.symm
      · simp [FiniteCylinder.overwrite, hv]
    · funext v
      simp [v.property]

theorem exact_count (F : Finset A) (target : A → Fin Q) :
    Q ^ F.card * (FiniteCylinder.cylinder F target).card = Fintype.card (A → Fin Q) := by
  have h := Fintype.card_congr (split F target)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, mul_comm] using h.symm

theorem one (s : A) (b : Fin Q) :
    Q * (Finset.univ.filter (fun ω : A → Fin Q => ω s = b)).card = Fintype.card (A → Fin Q) := by
  have h := exact_count ({s} : Finset A) (fun _ => b)
  simpa [FiniteCylinder.cylinder] using h

theorem two (s t : A) (hst : s ≠ t) (b c : Fin Q) :
    Q ^ 2 * (Finset.univ.filter (fun ω : A → Fin Q => ω s = b ∧ ω t = c)).card = Fintype.card (A → Fin Q) := by
  let target : A → Fin Q := fun x => if x = s then b else c
  have h := exact_count ({s, t} : Finset A) target
  have he : FiniteCylinder.cylinder ({s, t} : Finset A) target =
      Finset.univ.filter (fun ω : A → Fin Q => ω s = b ∧ ω t = c) := by
    ext ω
    simp [FiniteCylinder.cylinder, target, hst, hst.symm]
  rw [he] at h
  simpa [hst] using h
end Paper.FiniteCoordinateCount
