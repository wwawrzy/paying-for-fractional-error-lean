import Paper.Preliminaries.PathGraphTree
import GraphTheory.SimpleGraph.Treewidth.Defs

/-! Powers of a finite path, with an explicit width-t path decomposition.
These are the actual graph witnesses for the ID-LOCAL treewidth lower bound. -/
namespace Paper.PathPowerTreewidth
open SimpleGraph

def graph (n t : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ≤ v.val + t ∧ v.val ≤ u.val + t
  symm _ _ h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance adj (n t : ℕ) : DecidableRel (graph n t).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def decomposition (n t : ℕ) (hn : 0 < n) : (graph n t).TreeDecomposition (pathGraph n) where
  bag i := {v | i.val ≤ v.val ∧ v.val ≤ i.val + t}
  isTree := PathGraphTree.tree n hn
  cover v := ⟨v, le_rfl, by omega⟩
  edge_mem u v huv := by
    by_cases he : u.val ≤ v.val
    · exact ⟨u, ⟨le_rfl, by omega⟩, ⟨he, huv.2.2⟩⟩
    · exact ⟨v, ⟨by omega, huv.2.1⟩, ⟨le_rfl, by omega⟩⟩
  bag_connected v i j p hp hi hj r hr := by
    have hh := PathGraphTree.path_interval n p hp hr
    dsimp only [Set.mem_setOf_eq] at hi hj ⊢
    omega

theorem width (n t : ℕ) (hn : 0 < n) : (decomposition n t hn).IsWidthLE t := by
  classical
  intro i
  refine ⟨Set.toFinite _, ?_⟩
  let f : (decomposition n t hn).bag i → Fin (t + 1) := fun v =>
    ⟨v.val.val - i.val, by have h := v.property; dsimp only [decomposition, Set.mem_setOf_eq] at h; omega⟩
  have hf : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    apply Fin.ext
    have hv := v.property
    have hw := w.property
    have hh := congrArg Fin.val he
    dsimp only [f, decomposition, Set.mem_setOf_eq] at hv hw hh
    omega
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_coe_set_eq, Nat.card_fin] using hc

theorem treeWidth_le (n t : ℕ) : (graph n t).treeWidth ≤ t := by
  by_cases hn : 0 < n
  · exact treeWidth_le_of_isWidthLE (decomposition n t hn) (width n t hn)
  · have he : n = 0 := by omega
    subst n
    exact (graph 0 t).treeWidth_le_card_sub_one'.trans (by simp)

end Paper.PathPowerTreewidth
