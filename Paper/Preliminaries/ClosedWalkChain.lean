import Mathlib

/-! Turn a finite closed-neighborhood chain into an actual graph walk,
omitting repeated consecutive vertices and introducing no new vertices. -/
namespace Paper.ClosedWalkChain
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

theorem step {u v : V} (h : u = v ∨ G.Adj u v) :
    ∃ p : G.Walk u v, ∀ z ∈ p.support, z = u ∨ z = v := by
  rcases h with he | ha
  · subst v
    exact ⟨.nil, by simp⟩
  · exact ⟨ha.toWalk, by simp [SimpleGraph.Adj.toWalk]⟩

theorem chain5 (v₀ v₁ v₂ v₃ v₄ : V)
    (h₀ : v₀ = v₁ ∨ G.Adj v₀ v₁) (h₁ : v₁ = v₂ ∨ G.Adj v₁ v₂)
    (h₂ : v₂ = v₃ ∨ G.Adj v₂ v₃) (h₃ : v₃ = v₄ ∨ G.Adj v₃ v₄) :
    ∃ p : G.Walk v₀ v₄, ∀ z ∈ p.support, z ∈ ({v₀, v₁, v₂, v₃, v₄} : Finset V) := by
  obtain ⟨p₀, hp₀⟩ := step G h₀
  obtain ⟨p₁, hp₁⟩ := step G h₁
  obtain ⟨p₂, hp₂⟩ := step G h₂
  obtain ⟨p₃, hp₃⟩ := step G h₃
  refine ⟨((p₀.append p₁).append p₂).append p₃, ?_⟩
  intro z hz
  simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
  rcases hz with ((hz | hz) | hz) | hz
  · rcases hp₀ z hz with rfl | rfl <;> simp
  · rcases hp₁ z hz with rfl | rfl <;> simp
  · rcases hp₂ z hz with rfl | rfl <;> simp
  · rcases hp₃ z hz with rfl | rfl <;> simp
end Paper.ClosedWalkChain
