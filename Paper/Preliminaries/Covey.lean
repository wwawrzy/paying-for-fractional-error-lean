import Paper.Preliminaries.MinorDensity

/-! Actual disjoint connected branch sets with pairwise contact form a
complete-graph minor. Minor density therefore bounds their number. -/
namespace Paper.Covey
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def Contacts (S T : Finset V) : Prop := ∃ u ∈ S, ∃ v ∈ T, G.Adj u v

theorem contacts_symm {S T : Finset V} (h : Contacts G S T) : Contacts G T S := by
  obtain ⟨u, hu, v, hv, ha⟩ := h
  exact ⟨v, hv, u, hu, ha.symm⟩

theorem contacts_mono {S T S' T' : Finset V} (h : Contacts G S T) (hS : S ⊆ S') (hT : T ⊆ T') :
    Contacts G S' T' := by
  obtain ⟨u, hu, v, hv, ha⟩ := h
  exact ⟨u, hS hu, v, hT hv, ha⟩

structure IsCovey (C : Finset (Finset V)) : Prop where
  connected : ∀ S ∈ C, (G.induce (S : Set V)).Connected
  disjoint : ∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T
  contact : ∀ S ∈ C, ∀ T ∈ C, S ≠ T → Contacts G S T

theorem nonempty {C : Finset (Finset V)} (h : IsCovey G C) {S : Finset V} (hS : S ∈ C) : S.Nonempty := by
  obtain ⟨v⟩ := (h.connected S hS).nonempty
  exact ⟨v.val, v.property⟩

noncomputable def model {C : Finset (Finset V)} (h : IsCovey G C) :
    SimpleGraph.MinorModel (⊤ : SimpleGraph C) G where
  branchSet S := (S.val : Set V)
  nonempty S := Covey.nonempty G h S.property
  disjoint S T hne := by
    apply Set.disjoint_left.mpr
    intro v hvS hvT
    exact Finset.disjoint_left.mp (h.disjoint S.val S.property T.val T.property
      (fun he => hne (Subtype.ext he))) hvS hvT
  connected S := h.connected S.val S.property
  adjacent S T hST := h.contact S.val S.property T.val T.property (fun he => hST.ne (Subtype.ext he))

theorem empty : IsCovey G ∅ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

theorem erase {C : Finset (Finset V)} (h : IsCovey G C) (S : Finset V) : IsCovey G (C.erase S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    exact h.connected T (Finset.mem_of_mem_erase hT)
  · intro T hT U hU hne
    exact h.disjoint T (Finset.mem_of_mem_erase hT) U (Finset.mem_of_mem_erase hU) hne
  · intro T hT U hU hne
    exact h.contact T (Finset.mem_of_mem_erase hT) U (Finset.mem_of_mem_erase hU) hne

theorem insert {C : Finset (Finset V)} (h : IsCovey G C) (S : Finset V)
    (hconn : (G.induce (S : Set V)).Connected) (hd : ∀ T ∈ C, Disjoint S T)
    (hc : ∀ T ∈ C, Contacts G S T) : IsCovey G (insert S C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hT
    rcases Finset.mem_insert.mp hT with rfl | hT
    · exact hconn
    · exact h.connected T hT
  · intro T hT U hU hne
    rcases Finset.mem_insert.mp hT with hTS | hTC
    · subst T
      rcases Finset.mem_insert.mp hU with hUS | hUC
      · subst U; exact False.elim (hne rfl)
      · exact hd U hUC
    · rcases Finset.mem_insert.mp hU with hUS | hUC
      · subst U; exact (hd T hTC).symm
      · exact h.disjoint T hTC U hUC hne
  · intro T hT U hU hne
    rcases Finset.mem_insert.mp hT with hTS | hTC
    · subst T
      rcases Finset.mem_insert.mp hU with hUS | hUC
      · subst U; exact False.elim (hne rfl)
      · exact hc U hUC
    · rcases Finset.mem_insert.mp hU with hUS | hUC
      · subst U; exact contacts_symm G (hc T hTC)
      · exact h.contact T hTC U hUC hne
end Paper.Covey
