import Mathlib

/-! Exact finite counting for at most m prescribed independent coordinates.
No probability measure or asymptotic randomness is used. -/
namespace Paper.FiniteCylinder
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ}

noncomputable def cylinder (F : Finset V) (target : V → Fin c) : Finset (V → Fin c) :=
  Finset.univ.filter (fun ω => ∀ v ∈ F, ω v = target v)

noncomputable def overwrite (F : Finset V) (target ω : V → Fin c) (v : V) : Fin c :=
  if v ∈ F then target v else ω v

theorem overwrite_mem (F : Finset V) (target ω : V → Fin c) :
    overwrite F target ω ∈ cylinder F target := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => by simp [overwrite, hv]⟩

theorem cardinal_bound (F : Finset V) (target : V → Fin c) :
    Fintype.card (V → Fin c) ≤ c ^ F.card * (cylinder F target).card := by
  classical
  let encode : (V → Fin c) → (cylinder F target) × (F → Fin c) := fun ω =>
    (⟨overwrite F target ω, overwrite_mem F target ω⟩, fun v => ω v.val)
  have hinj : Function.Injective encode := by
    intro ω η he
    have hfirst : overwrite F target ω = overwrite F target η :=
      congrArg (fun p : (cylinder F target) × (F → Fin c) => p.1.val) he
    have hsecond : (fun v : F => ω v.val) = (fun v : F => η v.val) :=
      congrArg Prod.snd he
    funext v
    by_cases hv : v ∈ F
    · exact congrFun hsecond ⟨v, hv⟩
    · have hh := congrFun hfirst v
      simpa [overwrite, hv] using hh
  have hc := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, mul_comm] using hc

theorem bounded_coordinates (F : Finset V) (target : V → Fin c) (m : ℕ)
    (hc : 1 ≤ c) (hF : F.card ≤ m) :
    Fintype.card (V → Fin c) ≤ c ^ m * (cylinder F target).card := by
  apply (cardinal_bound F target).trans
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hc hF)
end Paper.FiniteCylinder
