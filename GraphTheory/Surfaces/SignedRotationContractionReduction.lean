import GraphTheory.SimpleGraph.Minor.Contraction
import GraphTheory.Surfaces.SignedRotationSubgraphGenus
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u v : V)
/-- Keep the u-copy of every edge duplicated by contracting u with v. -/
def contractionReduced : SimpleGraph V where
  Adj a b := G.Adj a b ∧ ¬ (a = v ∧ G.Adj u b) ∧ ¬ (b = v ∧ G.Adj u a)
  symm a b h := ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := ⟨fun a h => G.irrefl h.1⟩

theorem contractionReduced_le : contractionReduced G u v ≤ G := fun _ _ h => h.1

theorem contractionReduced_edge (huv : G.Adj u v) : (contractionReduced G u v).Adj u v := by
  exact ⟨huv, fun h => G.irrefl (h.1 ▸ huv), fun h => G.irrefl h.2⟩

theorem contractionReduced_no_common (w : V) :
    ¬ ((contractionReduced G u v).Adj u w ∧ (contractionReduced G u v).Adj v w) := by
  rintro ⟨h₁,h₂⟩
  exact h₂.2.1 ⟨rfl,h₁.1⟩

theorem contractionReduced_contract (huv : u ≠ v) : contrGraph (contractionReduced G u v) u v = contrGraph G u v := by
  ext x y
  constructor
  · rintro ⟨hne,a,b,ha,hb,hab⟩
    exact ⟨hne,a,b,ha,hb,hab.1⟩
  · rintro ⟨hne,a,b,ha,hb,hab⟩
    have hclasses : contrMk u v a ≠ contrMk u v b := by simpa [ha,hb] using hne
    by_cases h₁ : a = v ∧ G.Adj u b
    · have hbne : b ≠ v := by
        intro he
        apply hclasses
        rw [h₁.1,he]
      refine ⟨hne,u,b,?_,hb,?_⟩
      · exact (contrMk_eq u v).trans (h₁.1 ▸ ha)
      · exact ⟨h₁.2, fun h => huv h.1, fun h => hbne h.1⟩
    · by_cases h₂ : b = v ∧ G.Adj u a
      · have hane : a ≠ v := by
          intro he
          apply hclasses
          rw [h₂.1,he]
        refine ⟨hne,a,u,ha,?_,?_⟩
        · exact (contrMk_eq u v).trans (h₂.1 ▸ hb)
        · exact ⟨h₂.2.symm, fun h => hane h.1, fun h => huv h.1⟩
      · exact ⟨hne,a,b,ha,hb,hab,h₁,h₂⟩
theorem exists_contractionReduced_rotation [Fintype V] [DecidableRel G.Adj]
    (r : SignedRotation G) :
    ∃ q : SignedRotation (contractionReduced G u v), q.eulerGenus ≤ r.eulerGenus := by
  classical
  exact exists_subgraph_genus_le G r (contractionReduced G u v) (contractionReduced_le G u v)

theorem contractionReduced_reachable_of_adj (huv : G.Adj u v) {a b : V} (hab : G.Adj a b) :
    (contractionReduced G u v).Reachable a b := by
  let K := contractionReduced G u v
  have hedge : K.Adj u v := contractionReduced_edge G u v huv
  by_cases h₁ : a = v ∧ G.Adj u b
  · have hbne : b ≠ v := by intro he; exact hab.ne (h₁.1.trans he.symm)
    have hkeep : K.Adj u b := ⟨h₁.2,fun h => huv.ne h.1,fun h => hbne h.1⟩
    rw [h₁.1]
    exact hedge.symm.reachable.trans hkeep.reachable
  · by_cases h₂ : b = v ∧ G.Adj u a
    · have hane : a ≠ v := by intro he; exact hab.ne (he.trans h₂.1.symm)
      have hkeep : K.Adj a u := ⟨h₂.2.symm,fun h => hane h.1,fun h => huv.ne h.1⟩
      rw [h₂.1]
      exact hkeep.reachable.trans hedge.reachable
    · exact (show K.Adj a b from ⟨hab,h₁,h₂⟩).reachable

theorem contractionReduced_connected (huv : G.Adj u v) (hG : G.Connected) :
    (contractionReduced G u v).Connected := by
  letI : Nonempty V := hG.nonempty
  have hw : ∀ {a b : V}, G.Walk a b → (contractionReduced G u v).Reachable a b := by
    intro a b p
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b c hab p ih => exact (contractionReduced_reachable_of_adj G u v huv hab).trans ih
  exact ⟨fun a b => by obtain ⟨p⟩ := hG.preconnected a b; exact hw p⟩

end SimpleGraph.SignedRotation


