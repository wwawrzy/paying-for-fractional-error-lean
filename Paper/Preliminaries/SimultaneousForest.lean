import Paper.Preliminaries.SparseOrder
import Paper.Preliminaries.WitnessForest

/-! A single witness forest for all B passes/roles, from actual sparse order
and actual eligible-neighbor counts. For the initializer, B=2T. -/
namespace Paper.SimultaneousForest
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def eligible {d B : ℕ} (O : SparseOrder.Model G d)
    (A : Fin B → V → Finset V) (j : Fin B) (v : V) : Finset V :=
  (A j v).filter (fun u => O.rank v < O.rank u)

theorem row_bound {d B : ℕ} (O : SparseOrder.Model G d) (A : Fin B → V → Finset V)
    (hedge : ∀ j v u, u ∈ A j v → G.Adj v u) (k : Fin B → V → ℕ)
    (hrow : ∀ j v, 0 < k j v → d + (B * d) * k j v ≤ (A j v).card) (j : Fin B) (v : V) :
    (B * d) * k j v ≤ (eligible G O A j v).card := by
  classical
  by_cases hk : k j v = 0
  · simp only [hk, mul_zero, zero_le]
  have hhigh := hrow j v (by omega)
  let Low := (A j v).filter (fun u => O.rank u < O.rank v)
  have hsub : A j v ⊆ eligible G O A j v ∪ Low := by
    intro u hu
    have ha := hedge j v u hu
    have hne : O.rank u ≠ O.rank v := fun he => ha.ne (O.injective he).symm
    by_cases hlt : O.rank v < O.rank u
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu, hlt⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, by omega⟩)
  have hlow : Low.card ≤ d := by
    have hs : Low ⊆ Finset.univ.filter (fun u => O.rank u < O.rank v ∧ G.Adj v u) := by
      intro u hu
      have hh := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh.2, hedge j v u hh.1⟩
    exact (Finset.card_le_card hs).trans (O.bound v)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

theorem column_bound {d B : ℕ} (O : SparseOrder.Model G d) (A : Fin B → V → Finset V)
    (hedge : ∀ j v u, u ∈ A j v → G.Adj v u) (u : V) :
    (Finset.univ.filter (fun r : Fin B × V => u ∈ eligible G O A r.1 r.2)).card ≤ B * d := by
  classical
  let Low := Finset.univ.filter (fun v => O.rank v < O.rank u ∧ G.Adj u v)
  have hs : Finset.univ.filter (fun r : Fin B × V => u ∈ eligible G O A r.1 r.2) ⊆
      (Finset.univ : Finset (Fin B)) ×ˢ Low := by
    intro r hr
    have hm := Finset.mem_filter.mp (Finset.mem_filter.mp hr).2
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hm.2, (hedge r.1 r.2 u hm.1).symm⟩⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hc
  exact hc.trans (Nat.mul_le_mul_left B (O.bound u))

/-- All B groups of requirements are met in one actual acyclic subgraph.
No supplied forest or matching is assumed. -/
theorem exists_model {d B : ℕ} (O : SparseOrder.Model G d) (hd : 1 ≤ d) (hB : 1 ≤ B)
    (A : Fin B → V → Finset V) (k : Fin B → V → ℕ)
    (hedge : ∀ j v u, u ∈ A j v → G.Adj v u)
    (hrow : ∀ j v, 0 < k j v → d + (B * d) * k j v ≤ (A j v).card) :
    Nonempty (WitnessForest.Model G
      (fun r : Fin B × V => eligible G O A r.1 r.2) (fun r => k r.1 r.2) Prod.snd O.rank) := by
  apply WitnessForest.exists_model G _ _ Prod.snd O.rank (B * d) (by nlinarith)
  · intro r
    exact row_bound G O A hedge k hrow r.1 r.2
  · exact column_bound G O A hedge
  · intro r u hu
    exact (Finset.mem_filter.mp hu).2
  · intro r u hu
    exact hedge r.1 r.2 u (Finset.mem_filter.mp hu).1
/-- The order and the forest are both constructed from the induced-density
bound and actual neighbor counts. -/
theorem exists_from_density {d B : ℕ} (hd : 1 ≤ d) (hB : 1 ≤ B)
    {t : ℝ} (hden : Incidence.InducedDensityBound G t) (hdt : 2 * t ≤ d)
    (A : Fin B → V → Finset V) (k : Fin B → V → ℕ)
    (hedge : ∀ j v u, u ∈ A j v → G.Adj v u)
    (hrow : ∀ j v, 0 < k j v → d + (B * d) * k j v ≤ (A j v).card) :
    ∃ O : SparseOrder.Model G d, Nonempty (WitnessForest.Model G
      (fun r : Fin B × V => eligible G O A r.1 r.2) (fun r => k r.1 r.2) Prod.snd O.rank) := by
  obtain ⟨O⟩ := SparseOrder.exists_of_density G d hden hdt
  exact ⟨O, exists_model G O hd hB A k hedge hrow⟩
end Paper.SimultaneousForest
