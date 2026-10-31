import Paper.Preliminaries.BlowupProjection
import Paper.Preliminaries.FiniteCylinder

/-! Each shallow-minor edge with different physical roots survives a
cylinder fixing at most four physical coordinates. -/
namespace Paper.BlowupEdge
attribute [local instance] Classical.propDecidable
open BlowupProjection
universe u
variable {V A : Type u} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Crosses (label : V → Option A) (a b : A) : Prop :=
  ∃ u v, label u = some a ∧ label v = some b ∧ G.Adj u v

theorem path_crosses (label : V → Option A) {a b : A} (hne : a ≠ b)
    (v₀ v₁ v₂ v₃ : V) (h₀ : label v₀ = some a) (h₃ : label v₃ = some b)
    (h₁ : label v₁ = some a ∨ label v₁ = some b)
    (h₂ : label v₂ = some a ∨ label v₂ = some b)
    (e₀ : v₀ = v₁ ∨ G.Adj v₀ v₁) (e₁ : v₁ = v₂ ∨ G.Adj v₁ v₂)
    (e₂ : v₂ = v₃ ∨ G.Adj v₂ v₃) : Crosses G label a b := by
  have step : ∀ u v, label u = some a → label v = some b → u = v ∨ G.Adj u v → Crosses G label a b := by
    intro u v hu hv he
    rcases he with he | ha
    · subst v
      exact False.elim (hne (Option.some.inj (hu.symm.trans hv)))
    · exact ⟨u, v, hu, hv, ha⟩
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact step v₂ v₃ h₂ h₃ e₂
    · exact step v₁ v₂ h₁ h₂ e₁
  · exact step v₀ v₁ h₀ h₁ e₀

noncomputable def pattern {c : ℕ} (z₀ z₁ z₂ z₃ : V × Fin c) (v : V) : Fin c :=
  if v = z₀.1 then z₀.2 else if v = z₁.1 then z₁.2 else if v = z₂.1 then z₂.2 else z₃.2

variable {G} {c : ℕ} {J : SimpleGraph A} (M : DepthOne.StarModel J (blowup G c))

def Survives (ω : V → Fin c) (a b : A) : Prop :=
  sampleLabel M ω (M.root a).1 = some a ∧ sampleLabel M ω (M.root b).1 = some b ∧
    Crosses G (sampleLabel M ω) a b

theorem cylinder_survives {a b : A} (hab : J.Adj a b) (hphys : (M.root a).1 ≠ (M.root b).1) :
    ∃ F : Finset V, F.card ≤ 4 ∧ ∃ target : V → Fin c,
      ∀ ω ∈ FiniteCylinder.cylinder F target, Survives M ω a b := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := M.adjacent a b hab
  let target := pattern (M.root a) (M.root b) u v
  let F : Finset V := {(M.root a).1, (M.root b).1, u.1, v.1}
  have hLa : sampleLabel M target (M.root a).1 = some a := by
    simpa only [sampleLabel, target, pattern, if_pos rfl, Prod.mk.eta] using label_of_mem M (M.root_mem a)
  have hLb : sampleLabel M target (M.root b).1 = some b := by
    simpa only [sampleLabel, target, pattern, if_neg hphys.symm, if_pos rfl, Prod.mk.eta] using label_of_mem M (M.root_mem b)
  have hLu : sampleLabel M target u.1 = some a ∨ sampleLabel M target u.1 = some b := by
    by_cases hua : u.1 = (M.root a).1
    · exact Or.inl (hua ▸ hLa)
    by_cases hub : u.1 = (M.root b).1
    · exact Or.inr (hub ▸ hLb)
    · left
      simpa only [sampleLabel, target, pattern, if_neg hua, if_neg hub, if_pos rfl, Prod.mk.eta] using label_of_mem M hu
  have hLv : sampleLabel M target v.1 = some a ∨ sampleLabel M target v.1 = some b := by
    by_cases hva : v.1 = (M.root a).1
    · exact Or.inl (hva ▸ hLa)
    by_cases hvb : v.1 = (M.root b).1
    · exact Or.inr (hvb ▸ hLb)
    by_cases hvu : v.1 = u.1
    · exact hvu ▸ hLu
    · right
      simpa only [sampleLabel, target, pattern, if_neg hva, if_neg hvb, if_neg hvu, Prod.mk.eta] using label_of_mem M hv
  refine ⟨F, ?_, target, ?_⟩
  · dsimp [F]
    exact (Finset.card_insert_le _ _).trans (by
      have h₁ := Finset.card_insert_le (M.root b).1 ({u.1, v.1} : Finset V)
      have h₂ := Finset.card_insert_le u.1 ({v.1} : Finset V)
      simp only [Finset.card_singleton] at h₂
      omega)
  · intro ω hω
    have he : ∀ z ∈ F, sampleLabel M ω z = sampleLabel M target z := by
      intro z hz
      exact congrArg (fun i => copyLabel M (z, i)) ((Finset.mem_filter.mp hω).2 z hz)
    have he₀ := he (M.root a).1 (by simp [F])
    have he₁ := he (M.root b).1 (by simp [F])
    have heu := he u.1 (by simp [F])
    have hev := he v.1 (by simp [F])
    refine ⟨he₀.trans hLa, he₁.trans hLb, ?_⟩
    apply path_crosses G (sampleLabel M ω) hab.ne (M.root a).1 u.1 v.1 (M.root b).1
      (he₀.trans hLa) (he₁.trans hLb) (by rwa [heu]) (by rwa [hev])
    · rcases M.radius_one a u hu with h | h
      · exact Or.inl (congrArg Prod.fst h)
      · exact h.2
    · exact huv.2
    · rcases M.radius_one b v hv with h | h
      · exact Or.inl (congrArg Prod.fst h).symm
      · exact h.2.elim (fun he => Or.inl he.symm) (fun ha => Or.inr ha.symm)
end Paper.BlowupEdge
