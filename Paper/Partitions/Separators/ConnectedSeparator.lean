import Paper.Preliminaries.ComponentContainment

/-! Half-balanced deletion separators equivalently bound every connected
region avoiding the deleted set. This form transports through embeddings. -/
namespace Paper.ConnectedSeparator
open DeletionComponents
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Good (X : Finset V) (bound : ℝ) : Prop :=
  ∀ S : Finset V, (G.induce (S : Set V)).Connected → Disjoint S X → (S.card : ℝ) ≤ bound

theorem of_components (X : Finset V) (bound : ℝ)
    (h : ∀ C : (deleted G X).ConnectedComponent, ((physical G X C).card : ℝ) ≤ bound) : Good G X bound := by
  intro S hc hd
  obtain ⟨u⟩ := hc.nonempty
  have hu : u.val ∉ X := fun hx => Finset.disjoint_left.mp hd u.property hx
  let C := (deleted G X).connectedComponentMk ⟨u.val, hu⟩
  have hm : (S ∩ physical G X C).Nonempty :=
    ⟨u.val, Finset.mem_inter.mpr ⟨u.property, DeletionComponents.covers G X hu⟩⟩
  have hs := ComponentContainment.subset G X C S hc hd hm
  exact (show (S.card : ℝ) ≤ (physical G X C).card by exact_mod_cast Finset.card_le_card hs).trans (h C)

theorem to_components (X : Finset V) (bound : ℝ) (h : Good G X bound) :
    ∀ C : (deleted G X).ConnectedComponent, ((physical G X C).card : ℝ) ≤ bound :=
  fun C => h _ (DeletionComponents.connected G X C) (DeletionComponents.avoids G X C)

theorem all_deleted (bound : ℝ) : Good G Finset.univ bound := by
  intro S hc hd
  obtain ⟨u⟩ := hc.nonempty
  exact False.elim (Finset.disjoint_left.mp hd u.property (Finset.mem_univ u.val))

theorem isolated_card (S : Finset V) (hc : (G.induce (S : Set V)).Connected)
    (v : V) (hv : v ∈ S) (hn : G.neighborFinset v = ∅) : S.card ≤ 1 := by
  have he : ∀ u ∈ S, u = v := by
    intro u hu
    obtain ⟨p⟩ := hc ⟨v, hv⟩ ⟨u, hu⟩
    cases p with
    | nil => rfl
    | @cons w x y ha p =>
      have hm : x.val ∈ G.neighborFinset v := (G.mem_neighborFinset v x.val).mpr ha
      rw [hn] at hm
      exact False.elim (Finset.notMem_empty _ hm)
  exact Finset.card_le_one.mpr (fun u hu w hw => (he u hu).trans (he w hw).symm)

end Paper.ConnectedSeparator
