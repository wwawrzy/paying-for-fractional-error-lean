import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Push a finite virtual graph into the public physical identifier type.
Vertices outside the embedding image are isolated. This is a proof model,
not a global subtype decoder supplied to any runtime program. -/
namespace Paper.PublicEmbedding
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
variable (J : SimpleGraph W) [DecidableRel J.Adj] (e : W ↪ V)

noncomputable def graph : SimpleGraph V := J.map e

noncomputable local instance mappedAdj : DecidableRel (graph J e).Adj := fun _ _ => Classical.propDecidable _

theorem adj_iff (u v : V) : (graph J e).Adj u v ↔
    ∃ i j : W, J.Adj i j ∧ e i = u ∧ e j = v := SimpleGraph.map_adj e J u v

theorem neighbor_at (i : W) :
    (graph J e).neighborFinset (e i) = (J.neighborFinset i).image e := by
  ext v
  rw [SimpleGraph.mem_neighborFinset, adj_iff, Finset.mem_image]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have he : a = i := e.injective ha
    subst a
    exact ⟨b, (SimpleGraph.mem_neighborFinset J i b).mpr hab, hb⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨i, b, (SimpleGraph.mem_neighborFinset J i b).mp hb, rfl, rfl⟩

theorem neighbor_outside (v : V) (hv : v ∉ Set.range e) : (graph J e).neighborFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨a, _, _, ha, _⟩ := (adj_iff J e v u).mp ((SimpleGraph.mem_neighborFinset _ v u).mp hu)
  exact hv ⟨a, ha⟩

theorem degree_at (i : W) : (graph J e).degree (e i) = J.degree i := by
  change ((graph J e).neighborFinset (e i)).card = (J.neighborFinset i).card
  rw [neighbor_at, Finset.card_image_of_injective _ e.injective]

theorem degree_outside (v : V) (hv : v ∉ Set.range e) : (graph J e).degree v = 0 := by
  change ((graph J e).neighborFinset v).card = 0
  rw [neighbor_outside J e v hv, Finset.card_empty]

theorem degree_bound (Δ : ℕ) (hΔ : ∀ i, J.degree i ≤ Δ) : ∀ v, (graph J e).degree v ≤ Δ := by
  intro v
  by_cases hv : v ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hv
    rw [degree_at]
    exact hΔ i
  · rw [degree_outside J e v hv]
    exact Nat.zero_le _

noncomputable def imageIso : J ≃g (graph J e).induce (Set.range e) where
  toEquiv := Equiv.ofInjective e e.injective
  map_rel_iff' := by
    intro i j
    change (J.map e).Adj (e i) (e j) ↔ J.Adj i j
    exact SimpleGraph.map_adj_apply
end Paper.PublicEmbedding
