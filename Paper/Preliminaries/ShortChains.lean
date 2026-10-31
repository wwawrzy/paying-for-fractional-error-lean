import Mathlib

/-! Actual short closed-incidence chains, with length and support bounds,
and exact lifting to the physical induced communication region. -/
namespace Paper.ShortChains
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

theorem step {u v : V} (h : u = v ∨ G.Adj u v) :
    ∃ p : G.Walk u v, p.length ≤ 1 ∧ ∀ z ∈ p.support, z = u ∨ z = v := by
  rcases h with he | ha
  · subst v
    exact ⟨.nil, by simp, by simp⟩
  · exact ⟨ha.toWalk, by rfl, by simp [SimpleGraph.Adj.toWalk]⟩

theorem chain3 (u v w : V) (h₀ : u = v ∨ G.Adj u v) (h₁ : v = w ∨ G.Adj v w) :
    ∃ p : G.Walk u w, p.length ≤ 2 ∧ ∀ z ∈ p.support, z ∈ ({u, v, w} : Finset V) := by
  obtain ⟨p, hp, hps⟩ := step G h₀
  obtain ⟨q, hq, hqs⟩ := step G h₁
  refine ⟨p.append q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_append]
    omega
  · intro z hz
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · rcases hps z hz with rfl | rfl <;> simp
    · rcases hqs z hz with rfl | rfl <;> simp

theorem chain5 (v₀ v₁ v₂ v₃ v₄ : V)
    (h₀ : v₀ = v₁ ∨ G.Adj v₀ v₁) (h₁ : v₁ = v₂ ∨ G.Adj v₁ v₂)
    (h₂ : v₂ = v₃ ∨ G.Adj v₂ v₃) (h₃ : v₃ = v₄ ∨ G.Adj v₃ v₄) :
    ∃ p : G.Walk v₀ v₄, p.length ≤ 4 ∧ ∀ z ∈ p.support, z ∈ ({v₀, v₁, v₂, v₃, v₄} : Finset V) := by
  obtain ⟨p, hp, hps⟩ := chain3 G v₀ v₁ v₂ h₀ h₁
  obtain ⟨q, hq, hqs⟩ := chain3 G v₂ v₃ v₄ h₂ h₃
  refine ⟨p.append q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.length_append]
    omega
  · intro z hz
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have hh := hps z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> simp
    · have hh := hqs z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> simp

theorem induce_length {u v : V} (H : Finset V) (p : G.Walk u v)
    (hp : ∀ z ∈ p.support, z ∈ H) : (p.induce (H : Set V) hp).length = p.length := by
  have h := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.map_induce (s := (H : Set V)) p hp)
  simpa only [SimpleGraph.Walk.length_map] using h

theorem lift_walk {A : Type*} (K : SimpleGraph A) (root : A → V) (c : ℕ)
    (hedge : ∀ {a b}, K.Adj a b → ∃ p : G.Walk (root a) (root b), p.length ≤ c)
    {a b : A} (p : K.Walk a b) : ∃ q : G.Walk (root a) (root b), q.length ≤ c * p.length := by
  induction p with
  | nil => exact ⟨.nil, by simp⟩
  | @cons a b d hab p ih =>
    obtain ⟨q, hq⟩ := hedge hab
    obtain ⟨r, hr⟩ := ih
    refine ⟨q.append r, ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons]
    nlinarith
end Paper.ShortChains
