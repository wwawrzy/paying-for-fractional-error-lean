import Paper.Preliminaries.SevenFoundation

/-! Actual minimum-identifier owners and augmented support sets for the
partial weighted solver. Each owner owns itself. -/
namespace Paper.OwnerSupport
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def owner (D : Finset V) (u : V) : V :=
  if u ∈ D then u else if h : ((closed G u) ∩ D).Nonempty then ((closed G u) ∩ D).min' h else u

theorem owner_center (D : Finset V) {u : V} (hu : u ∈ D) : owner G D u = u := by
  simp [owner, hu]

theorem owner_of_covered (D : Finset V) {u : V} (hu : u ∈ covered G D) :
    owner G D u ∈ D ∧ (owner G D u = u ∨ G.Adj (owner G D u) u) := by
  classical
  by_cases hud : u ∈ D
  · exact ⟨by simpa [owner_center G D hud] using hud, Or.inl (owner_center G D hud)⟩
  have hn : ((closed G u) ∩ D).Nonempty := by
    obtain ⟨d, hd, hud⟩ := Finset.mem_biUnion.mp hu
    exact ⟨d, Finset.mem_inter.mpr ⟨(closed_symm G u d).mp hud, hd⟩⟩
  have hm := Finset.min'_mem ((closed G u) ∩ D) hn
  have ho : owner G D u = ((closed G u) ∩ D).min' hn := by simp [owner, hud, hn]
  rw [← ho] at hm
  have hx := Finset.mem_inter.mp hm
  exact ⟨hx.2, ((mem_closed G _ _).mp hx.1).elim Or.inl (fun ha => Or.inr ha.symm)⟩

theorem owner_minimum (D : Finset V) {u : V} (hu : u ∉ D) (hc : u ∈ covered G D)
    {d : V} (hd : d ∈ D) (hadj : G.Adj d u) : owner G D u ≤ d := by
  classical
  have hn : ((closed G u) ∩ D).Nonempty :=
    ⟨d, Finset.mem_inter.mpr ⟨(mem_closed G d u).mpr (Or.inr hadj.symm), hd⟩⟩
  simp only [owner, if_neg hu, dif_pos hn]
  exact Finset.min'_le _ _ (Finset.mem_inter.mpr ⟨(mem_closed G d u).mpr (Or.inr hadj.symm), hd⟩)

noncomputable def support (D R : Finset V) (v : V) : Finset V :=
  ((closed G v) ∩ (R ∪ D)).image (owner G D)

theorem support_labels (D R : Finset V) (hcover : R ⊆ covered G D) (v : V) :
    support G D R v ⊆ D := by
  intro d hd
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hd
  have huO := (Finset.mem_inter.mp hu).2
  have hc : u ∈ covered G D := (Finset.mem_union.mp huO).elim (fun h => hcover h) (fun h => subset_covered G D h)
  exact (owner_of_covered G D hc).1

theorem self_label (D R : Finset V) {v : V} (hv : v ∈ R ∪ D) :
    owner G D v ∈ support G D R v :=
  Finset.mem_image.mpr ⟨v, Finset.mem_inter.mpr ⟨self_mem_closed G v, hv⟩, rfl⟩

theorem owner_owned (D R : Finset V) (hcover : R ⊆ covered G D) {u : V} (hu : u ∈ R ∪ D) :
    owner G D u ∈ D ∧ (owner G D u = u ∨ G.Adj (owner G D u) u) :=
  owner_of_covered G D ((Finset.mem_union.mp hu).elim (fun h => hcover h) (fun h => subset_covered G D h))

theorem label_idempotent (D R : Finset V) (hcover : R ⊆ covered G D) {u : V} (hu : u ∈ R ∪ D) :
    owner G D (owner G D u) = owner G D u :=
  owner_center G D (owner_owned G D R hcover hu).1
end Paper.OwnerSupport
