import GraphTheory.Surfaces.SignedRotationPartitionGenus
import GraphTheory.Surfaces.SignedRotationGeneralDeletion
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem exists_subgraph_genus_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : SignedRotation H) (G : SimpleGraph V) [DecidableRel G.Adj] (hGH : G ≤ H) :
    ∃ s : SignedRotation G, s.eulerGenus ≤ r.eulerGenus := by
  classical
  by_cases he : H = G
  · exact ⟨he ▸ r, le_of_eq (eulerGenus_transport he r)⟩
  have hex : ∃ u v, H.Adj u v ∧ ¬ G.Adj u v := by
    by_contra hn
    push Not at hn
    apply he
    exact le_antisymm (fun u v huv => hn u v huv) hGH
  obtain ⟨u,v,huv,hmiss⟩ := hex
  let K := H \ edge u v
  have hK : ¬ K.Adj u v := by
    change ¬ (H.Adj u v ∧ ¬ (edge u v).Adj u v)
    simp [edge_adj,huv.ne]
  have hGK : G ≤ K := by
    intro x y hxy
    refine ⟨hGH hxy, ?_⟩
    intro he
    rcases (edge_adj u v x y).mp he with ⟨h|h,_⟩
    · exact hmiss (by simpa only [h.1,h.2] using hxy)
    · exact hmiss (by simpa only [h.1,h.2] using hxy.symm)
  have hH : K ⊔ edge u v = H := by
    ext x y
    change (H.Adj x y ∧ ¬ (edge u v).Adj x y ∨ (edge u v).Adj x y) ↔ H.Adj x y
    have hedge : (edge u v).Adj x y → H.Adj x y := by
      intro h
      rcases (edge_adj u v x y).mp h with ⟨h|h,_⟩
      · simpa only [h.1,h.2] using huv
      · simpa only [h.1,h.2] using huv.symm
    tauto
  have hcard : K.edgeFinset.card < H.edgeFinset.card := by
    have hc := K.card_edgeFinset_sup_edge hK huv.ne
    simp only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at hc ⊢
    rw [hH] at hc
    omega
  let r' : SignedRotation (K ⊔ edge u v) := hH.symm ▸ r
  have hr' : r'.eulerGenus = r.eulerGenus := eulerGenus_transport hH.symm r
  obtain ⟨t,ht⟩ := exists_deletion_genus_le K u v huv.ne hK r'
  obtain ⟨s,hs⟩ := exists_subgraph_genus_le K t G hGK
  exact ⟨s,hs.trans (ht.trans_eq hr')⟩
termination_by H.edgeFinset.card
decreasing_by
  simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hcard
theorem eulerGenus_nonneg (H : SimpleGraph V) [DecidableRel H.Adj] (r : SignedRotation H) :
    0 ≤ r.eulerGenus := by
  classical
  obtain ⟨s,hs⟩ := exists_subgraph_genus_le H r (⊥ : SimpleGraph V) bot_le
  letI : IsEmpty (⊥ : SimpleGraph V).Dart := ⟨fun d => d.adj⟩
  rwa [s.eulerGenus_eq_zero_of_no_darts] at hs

end SimpleGraph.SignedRotation


namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (r : SignedRotation G)
def splitGraph (S : Set V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (x ∈ S ↔ y ∈ S)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

theorem restrict_genus_congr (S T : Set V)
    (hS : ∀ ⦃x y⦄, x ∈ S → G.Adj x y → y ∈ S)
    (hT : ∀ ⦃x y⦄, x ∈ T → G.Adj x y → y ∈ T) (h : S = T) :
    (r.restrictClosed S hS).eulerGenus = (r.restrictClosed T hT).eulerGenus := by
  subst T
  rfl

theorem restrictClosed_genus_le (S : Set V)
    (hS : ∀ ⦃x y⦄, x ∈ S → G.Adj x y → y ∈ S) :
    (r.restrictClosed S hS).eulerGenus ≤ r.eulerGenus := by
  classical
  by_cases hse : S.Nonempty
  · obtain ⟨w,hw⟩ := hse
    let H := splitGraph S
    have hGH : G ≤ H := by
      intro x y hxy
      exact ⟨hxy.ne,⟨fun hx => hS hx hxy,fun hy => hS hy hxy.symm⟩⟩
    let c := H.connectedComponentMk w
    have he : c.supp = S := by
      ext x
      change H.connectedComponentMk x = H.connectedComponentMk w ↔ x ∈ S
      constructor
      · intro hx
        obtain ⟨p⟩ := ConnectedComponent.exact hx
        have hm {a b : V} (p : H.Walk a b) : a ∈ S ↔ b ∈ S := by
          induction p with
          | nil => rfl
          | cons h p ih => exact h.2.trans ih
        exact (hm p).mpr hw
      · intro hx
        apply ConnectedComponent.sound
        by_cases hxw : x = w
        · subst x; exact Reachable.refl w
        · exact (show H.Adj x w from ⟨hxw,by tauto⟩).reachable
    letI : Fintype H.ConnectedComponent := Fintype.ofFinite _
    have hb : (r.restrictClosed c.supp
        (fun {_ _} hu huv => c.mem_supp_of_adj_mem_supp hu (hGH huv))).eulerGenus ≤ r.eulerGenus := by
      rw [partition_eulerGenus_sum H hGH r]
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun d : H.ConnectedComponent => (r.restrictClosed d.supp
          (fun {_ _} hu huv => d.mem_supp_of_adj_mem_supp hu (hGH huv))).eulerGenus)
        (fun d _ => eulerGenus_nonneg _ _) (Finset.mem_univ c)
    rw [restrict_genus_congr r c.supp S _ hS he] at hb
    exact hb
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hse
    subst S
    letI : IsEmpty (G.induce (∅ : Set V)).Dart := ⟨fun d => d.fst.property⟩
    rw [(r.restrictClosed ∅ hS).eulerGenus_eq_zero_of_no_darts]
    exact eulerGenus_nonneg G r
end SimpleGraph.SignedRotation

namespace SimpleGraph.SignedRotation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : SignedRotation G)
theorem exists_induce_genus_le (S : Set V) :
    ∃ s : SignedRotation (G.induce S), s.eulerGenus ≤ r.eulerGenus := by
  classical
  let K := G ⊓ splitGraph S
  obtain ⟨q,hq⟩ := exists_subgraph_genus_le G r K inf_le_left
  have hS : ∀ ⦃x y⦄, x ∈ S → K.Adj x y → y ∈ S := by
    intro x y hx hxy
    exact hxy.2.2.mp hx
  have he : K.induce S = G.induce S := by
    ext x y
    change (G.Adj x.val y.val ∧ x.val ≠ y.val ∧ (x.val ∈ S ↔ y.val ∈ S)) ↔ G.Adj x.val y.val
    constructor
    · exact And.left
    · intro h
      exact ⟨h,h.ne,by simp only [x.property,y.property]⟩
  let s : SignedRotation (G.induce S) := he ▸ q.restrictClosed S hS
  have hs : s.eulerGenus = (q.restrictClosed S hS).eulerGenus :=
    eulerGenus_transport he (q.restrictClosed S hS)
  exact ⟨s,hs.le.trans ((restrictClosed_genus_le q S hS).trans hq)⟩
end SimpleGraph.SignedRotation
