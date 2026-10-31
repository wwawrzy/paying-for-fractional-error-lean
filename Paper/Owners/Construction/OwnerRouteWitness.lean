import Paper.Owners.Construction.OwnerRouteLabels
import Paper.Owners.Construction.OwnerExperiment
import Paper.Preliminaries.ClosedWalkChain

/-! Actual five-vertex chains represent owner edges and carry endpoint
labels at every physical vertex, including heavy representatives. -/
namespace Paper.OwnerRouteWitness
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation OwnerSupport HeavyRepair
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Witness (D R : Finset V) (L : ℕ) (a b : V) where
  left : V
  mid : V
  right : V
  a_mem : a ∈ D
  b_mem : b ∈ D
  light : mid ∉ heavy G D R L
  mid_a : a ∈ support G D R mid
  mid_b : b ∈ support G D R mid
  left_owned : left ∈ R ∪ D
  right_owned : right ∈ R ∪ D
  left_label : owner G D left = a
  right_label : owner G D right = b
  left_closed : left ∈ closed G mid
  right_closed : right ∈ closed G mid

theorem exists_witness (D R : Finset V) (L : ℕ) {a b : D}
    (h : (OwnerInteraction.augmentedGraph G D R L).Adj a b) : Nonempty (Witness G D R L a.val b.val) := by
  classical
  obtain ⟨_, v, ha, hb⟩ := h
  have hv : v ∉ heavy G D R L := by intro hv; simp [OwnerInteraction.lightSupport, hv] at ha
  have ha' : a.val ∈ support G D R v := by simpa only [OwnerInteraction.lightSupport, if_neg hv] using ha
  have hb' : b.val ∈ support G D R v := by simpa only [OwnerInteraction.lightSupport, if_neg hv] using hb
  obtain ⟨u, hu, hua⟩ := Finset.mem_image.mp ha'
  obtain ⟨w, hw, hwb⟩ := Finset.mem_image.mp hb'
  exact ⟨{
    left := u, mid := v, right := w, a_mem := a.property, b_mem := b.property,
    light := hv, mid_a := ha', mid_b := hb',
    left_owned := (Finset.mem_inter.mp hu).2, right_owned := (Finset.mem_inter.mp hw).2,
    left_label := hua, right_label := hwb,
    left_closed := (Finset.mem_inter.mp hu).1, right_closed := (Finset.mem_inter.mp hw).1 }⟩

theorem route_exists {D R : Finset V} {L : ℕ} {a b : V} (W : Witness G D R L a b) :
    ∃ p : G.Walk a b, ∀ z ∈ p.support, z ∈ ({a, W.left, W.mid, W.right, b} : Finset V) := by
  apply ClosedWalkChain.chain5 G a W.left W.mid W.right b
  · simpa only [W.left_label] using OwnerExperiment.owner_star G D W.left
  · exact ((mem_closed G W.left W.mid).mp W.left_closed).elim Or.inl (fun ha => Or.inr ha.symm)
  · exact ((mem_closed G W.right W.mid).mp W.right_closed).elim (fun he => Or.inl he.symm) Or.inr
  · have hh := OwnerExperiment.owner_star G D W.right
    rw [W.right_label] at hh
    exact hh.elim (fun he => Or.inl he.symm) (fun ha => Or.inr ha.symm)

theorem labels_guard {D R : Finset V} {L : ℕ} {a b : V} (W : Witness G D R L a b)
    {z : V} (hz : z ∈ ({a, W.left, W.mid, W.right, b} : Finset V)) :
    a ∈ OwnerRouteLabels.labels G D R L z ∨ b ∈ OwnerRouteLabels.labels G D R L z := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with ha | hl | hm | hr | hb
  · subst z; exact Or.inl (OwnerRouteLabels.root_label G D R L W.a_mem)
  · subst z
    have hh := OwnerRouteLabels.owner_label G D R L W.left_owned
    left
    simpa only [W.left_label] using hh
  · subst z; exact Or.inl (OwnerRouteLabels.light_label G D R L W.light W.mid_a)
  · subst z
    have hh := OwnerRouteLabels.owner_label G D R L W.right_owned
    right
    simpa only [W.right_label] using hh
  · subst z; exact Or.inr (OwnerRouteLabels.root_label G D R L W.b_mem)
end Paper.OwnerRouteWitness
