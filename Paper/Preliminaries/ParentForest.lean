import Mathlib

/-! A genuine forest from a functional parent relation with decreasing rank. -/
namespace Paper.ParentForest
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

def graph (parent : V → Option V) (rank : V → ℕ)
    (hparent : ∀ u v, parent u = some v → rank v < rank u) : SimpleGraph V where
  Adj u v := parent u = some v ∨ parent v = some u
  symm := fun _ _ => Or.symm
  loopless := ⟨by
    intro u h
    rcases h with h | h <;> exact Nat.lt_irrefl _ (hparent u u h)⟩

/-- At a maximum-rank cycle vertex both incident edges would have to be its
unique parent edge. The two neighbors of a simple cycle are distinct. -/
theorem isAcyclic (parent : V → Option V) (rank : V → ℕ)
    (hparent : ∀ u v, parent u = some v → rank v < rank u) :
    (graph parent rank hparent).IsAcyclic := by
  classical
  intro v p hp
  have hnon : p.support.toFinset.Nonempty :=
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image p.support.toFinset rank hnon
  have hx' : x ∈ p.support := List.mem_toFinset.mp hx
  let q := p.rotate x hx'
  have hq : q.IsCycle := hp.rotate hx'
  have hbound : ∀ u ∈ q.support, rank u ≤ rank x := by
    intro u hu
    have hu' : u ∈ p.support := (p.mem_support_rotate_iff x hx').mp hu
    exact hmax u (List.mem_toFinset.mpr hu')
  have hs := q.adj_snd hq.not_nil
  have ht := (q.adj_penultimate hq.not_nil).symm
  have hps : parent x = some q.snd := by
    rcases hs with h | h
    · exact h
    · have hle := hbound q.snd (q.getVert_mem_support 1)
      exact False.elim (Nat.not_lt_of_ge hle (hparent _ _ h))
  have hpt : parent x = some q.penultimate := by
    rcases ht with h | h
    · exact h
    · have hle := hbound q.penultimate (q.getVert_mem_support _)
      exact False.elim (Nat.not_lt_of_ge hle (hparent _ _ h))
  exact hq.snd_ne_penultimate (Option.some.inj (hps.symm.trans hpt))
end Paper.ParentForest
