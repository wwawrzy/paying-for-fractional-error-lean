import Mathlib

/-! Project walks and connected sets when an edge may collapse to a vertex.
This handles vertical transitions of the layered connecting-set graph. -/
namespace Paper.WeakProjection
attribute [local instance] Classical.propDecidable
variable {U V : Type*} [DecidableEq U] [DecidableEq V]
variable (J : SimpleGraph U) (G : SimpleGraph V) (φ : U → V)
variable (hedge : ∀ u v, J.Adj u v → φ u = φ v ∨ G.Adj (φ u) (φ v))

include hedge in
theorem walk {u v : U} (p : J.Walk u v) :
    ∃ q : G.Walk (φ u) (φ v), q.support.toFinset ⊆ p.support.toFinset.image φ ∧ q.length ≤ p.length := by
  classical
  induction p with
  | nil => exact ⟨.nil, by simp, by simp⟩
  | @cons u w v ha p ih =>
    obtain ⟨q, hq, hlen⟩ := ih
    have htail : p.support.toFinset.image φ ⊆ (SimpleGraph.Walk.cons ha p).support.toFinset.image φ := by
      apply Finset.image_mono
      intro z hz
      simp only [List.mem_toFinset, SimpleGraph.Walk.support_cons, List.mem_cons] at hz ⊢
      exact Or.inr hz
    rcases hedge u w ha with he | hadj
    · rw [he]
      exact ⟨q, hq.trans htail, by simp only [SimpleGraph.Walk.length_cons]; omega⟩
    · refine ⟨.cons hadj q, ?_, by simp only [SimpleGraph.Walk.length_cons]; omega⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.toFinset_cons, Finset.mem_insert] at hz
      rcases hz with he | hz
      · exact Finset.mem_image.mpr ⟨u, by simp, he.symm⟩
      · exact htail (hq hz)

include hedge in
theorem connected_image (S : Set U) (hS : (J.induce S).Connected) :
    (G.induce (φ '' S)).Connected := by
  classical
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at hS ⊢
  obtain ⟨u, hu⟩ := hS
  refine ⟨⟨φ u.val, Set.mem_image_of_mem φ u.property⟩, ?_⟩
  intro v
  obtain ⟨w, hw, he⟩ := v.property
  obtain ⟨p⟩ := hu ⟨w, hw⟩
  obtain ⟨q, hq, _⟩ := walk (J.induce S) G (fun x : S => φ x.val)
    (fun x y h => hedge x.val y.val h) p
  have hs : ∀ z ∈ q.support, z ∈ φ '' S := by
    intro z hz
    have hm := hq (List.mem_toFinset.mpr hz)
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hm
    exact ⟨x.val, x.property, hx⟩
  have hr := (q.induce (φ '' S) hs).reachable
  simpa only [he] using hr

theorem image_support_card {u v : U} (p : J.Walk u v) :
    (p.support.toFinset.image φ).card ≤ p.length + 1 := by
  have h₁ := Finset.card_image_le (s := p.support.toFinset) (f := φ)
  have h₂ := List.toFinset_card_le p.support
  rw [SimpleGraph.Walk.length_support] at h₂
  omega
end Paper.WeakProjection
