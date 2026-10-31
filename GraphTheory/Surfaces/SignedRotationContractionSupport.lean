import GraphTheory.SimpleGraph.Minor.Contraction
import GraphTheory.Surfaces.SignedRotationVertices
namespace SimpleGraph.SignedRotation
open SimpleGraph.EdgeContraction
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u v : V)
theorem contraction_support_image (hm : contrMk u v u ∈ (contrGraph G u v).support)
    (a : V) (ha : a ∈ G.support) : contrMk u v a ∈ (contrGraph G u v).support := by
  obtain ⟨b,hab⟩ := G.mem_support.mp ha
  by_cases he : contrMk u v a = contrMk u v b
  · rcases (contrMk_eq_iff u v a b).mp he with he | ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact False.elim (hab.ne he)
    · simpa only [ha] using hm
    · rw [ha,← contrMk_eq u v]
      exact hm
  · exact (contrGraph G u v).mem_support.mpr ⟨contrMk u v b,contrGraph_adj_of_adj G u v hab he⟩

noncomputable def contractionSupportMap
    (hm : contrMk u v u ∈ (contrGraph G u v).support) : G.support → (contrGraph G u v).support :=
  fun a => ⟨contrMk u v a.val,contraction_support_image G u v hm a.val a.property⟩

theorem contraction_support_card_lower [Fintype V] [DecidableRel G.Adj]
    (huv : G.Adj u v) (hm : contrMk u v u ∈ (contrGraph G u v).support) :
    Nat.card G.support ≤ Nat.card (contrGraph G u v).support + 1 := by
  classical
  let vs : G.support := ⟨v,G.mem_support.mpr ⟨u,huv.symm⟩⟩
  let f : {a : G.support // a ≠ vs} → (contrGraph G u v).support :=
    fun a => contractionSupportMap G u v hm a.val
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.val_injective
    apply Subtype.val_injective
    apply contrMk_injOn_compl_v u v
    · exact fun he => a.property (Subtype.ext he)
    · exact fun he => b.property (Subtype.ext he)
    · exact congrArg Subtype.val h
  have hc := Nat.card_le_card_of_injective f hi
  have he : Nat.card {a : G.support // a ≠ vs} = Nat.card G.support - 1 := by
    simp only [Nat.card_eq_fintype_card]
    simpa using Fintype.card_subtype_compl (fun a : G.support => a = vs)
  have hp : 0 < Nat.card G.support := by
    letI : Nonempty G.support := ⟨vs⟩
    exact Nat.card_pos
  rw [he] at hc
  omega
end SimpleGraph.SignedRotation
