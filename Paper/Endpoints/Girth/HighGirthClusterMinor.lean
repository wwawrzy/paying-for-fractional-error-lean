import Paper.Endpoints.Girth.HighGirthClusterCross
import GraphTheory.SimpleGraph.Minor.Defs

/-! The actual simple quotient graph and its connected branch-set minor model.
No assumption that the quotient is a minor is supplied by the caller. -/
namespace Paper.HighGirthClusterMinor
attribute [local instance] Classical.propDecidable
open HighGirthVoronoi
variable {V : Type} [LinearOrder V]

noncomputable def graph (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) :
    SimpleGraph {c // c ∈ C} where
  Adj c d := c ≠ d ∧ ∃ u v, owner G C hC u = c.val ∧ owner G C hC v = d.val ∧ G.Adj u v
  symm := by
    rintro c d ⟨hne,u,v,hu,hv,he⟩
    exact ⟨hne.symm,v,u,hv,hu,he.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def model (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) : SimpleGraph.MinorModel (graph G C hC) G where
  branchSet c := {v | owner G C hC v = c.val}
  nonempty c := ⟨c.val, owner_center G hconn C hC c.val c.property⟩
  disjoint c d hne := by
    apply Set.disjoint_left.mpr
    intro v hc hd
    exact hne (Subtype.ext (hc.symm.trans hd))
  connected c := cluster_connected G hconn C hC c.val c.property
  adjacent c d hcd := by
    obtain ⟨_,u,v,hu,hv,he⟩ := hcd
    exact ⟨u,hu,v,hv,he⟩

theorem isMinor (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) : SimpleGraph.IsMinor (graph G C hC) G :=
  ⟨model G hconn C hC⟩

noncomputable def internal [Fintype V] (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty) (c : V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => ∀ v ∈ e, owner G C hC v = c)

noncomputable def cross [Fintype V] (G : SimpleGraph V) (C : Finset V)
    (hC : C.Nonempty) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => ¬ ∃ c ∈ C, ∀ v ∈ e, owner G C hC v = c)

variable [Fintype V]

theorem internal_pair (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty)
    (c u v : V) : s(u,v) ∈ internal G C hC c ↔
    G.Adj u v ∧ owner G C hC u = c ∧ owner G C hC v = c := by
  classical
  simp [internal, Sym2.mem_iff]

theorem cross_pair (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty)
    (u v : V) : s(u,v) ∈ cross G C hC ↔ G.Adj u v ∧ owner G C hC u ≠ owner G C hC v := by
  classical
  simp only [cross, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    Sym2.mem_iff, forall_eq_or_imp, forall_eq]
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨he,?_⟩
    intro hh
    exact hn ⟨owner G C hC u,(owner_spec G C hC u).1,rfl,hh.symm⟩
  · rintro ⟨he,hn⟩
    refine ⟨he,?_⟩
    rintro ⟨c,_,hu,hv⟩
    exact hn (hu.trans hv.symm)

set_option backward.isDefEq.respectTransparency false in
theorem internal_card (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) (c : V) :
    (internal G C hC c).card = (G.induce {v | owner G C hC v = c}).edgeFinset.card := by
  classical
  let f := (Function.Embedding.subtype (fun v => owner G C hC v = c)).sym2Map
  have heq : internal G C hC c =
      (G.induce {v | owner G C hC v = c}).edgeFinset.map f := by
    dsimp [f]
    have hh := SimpleGraph.map_edgeFinset_induce (G := G) (s := {v | owner G C hC v = c})
    convert hh.symm using 1 <;> ext e <;>
      induction e using Sym2.inductionOn with
      | _ u v => simp [internal_pair, Finset.mk_mem_sym2_iff]
  calc (internal G C hC c).card =
      ((G.induce {v | owner G C hC v = c}).edgeFinset.map f).card := congrArg Finset.card heq
       _ = _ := by
         convert Finset.card_map f using 1 <;> congr 1 <;> ext e <;> simp

theorem partition_card (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) :
    G.edgeFinset.card = (∑ c ∈ C, (internal G C hC c).card) + (cross G C hC).card := by
  classical
  have hp : (C : Set V).PairwiseDisjoint (internal G C hC) := by
    intro c hc d hd hne
    apply Finset.disjoint_left.mpr
    intro e hec hed
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hcu := ((internal_pair G C hC c u v).mp hec).2.1
      have hdu := ((internal_pair G C hC d u v).mp hed).2.1
      exact hne (hcu.symm.trans hdu)
  have hd : Disjoint (C.biUnion (internal G C hC)) (cross G C hC) := by
    apply Finset.disjoint_left.mpr
    intro e hi hx
    obtain ⟨c,hc,hi⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hx).2 ⟨c,hc,(Finset.mem_filter.mp hi).2⟩
  have heq : G.edgeFinset = C.biUnion (internal G C hC) ∪ cross G C hC := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [Finset.mem_union, Finset.mem_biUnion, internal_pair, cross_pair,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      constructor
      · intro he
        by_cases hh : owner G C hC u = owner G C hC v
        · exact Or.inl ⟨owner G C hC u,(owner_spec G C hC u).1,he,rfl,hh.symm⟩
        · exact Or.inr ⟨he,hh⟩
      · rintro (⟨_,_,he,_,_⟩ | ⟨he,_⟩) <;> exact he
  rw [heq,Finset.card_union_of_disjoint hd,Finset.card_biUnion hp]

noncomputable def edgeMap (G : SimpleGraph V) (C : Finset V) (hC : C.Nonempty) :
    Sym2 V → Sym2 {c // c ∈ C} :=
  Sym2.map (fun v => ⟨owner G C hC v,(owner_spec G C hC v).1⟩)

theorem cross_card_le (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 4*R+2 < p.length) :
    (cross G C hC).card ≤ (graph G C hC).edgeFinset.card := by
  classical
  apply Finset.card_le_card_of_injOn (edgeMap G C hC)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      obtain ⟨ha,hn⟩ := (cross_pair G C hC u v).mp he
      apply (SimpleGraph.mem_edgeFinset).mpr
      change (graph G C hC).Adj _ _
      exact ⟨fun h => hn (congrArg Subtype.val h),u,v,rfl,rfl,ha⟩
  · intro e he f hf heq
    induction e using Sym2.inductionOn with
    | _ u v =>
      induction f using Sym2.inductionOn with
      | _ x y =>
        obtain ⟨huv,hne⟩ := (cross_pair G C hC u v).mp he
        obtain ⟨hxy,_⟩ := (cross_pair G C hC x y).mp hf
        have hh : (owner G C hC u = owner G C hC x ∧ owner G C hC v = owner G C hC y) ∨
            (owner G C hC u = owner G C hC y ∧ owner G C hC v = owner G C hC x) := by
          simpa only [edgeMap,Sym2.map_mk,Sym2.eq_iff,Subtype.mk.injEq] using heq
        rcases hh with ⟨hux,hvy⟩ | ⟨huy,hvx⟩
        · exact HighGirthClusterCross.unique_cross_edge G hconn C hC R hcover hgirth
            _ _ (owner_spec G C hC u).1 (owner_spec G C hC v).1 hne
            u x v y rfl hux.symm rfl hvy.symm huv hxy
        · have hz := HighGirthClusterCross.unique_cross_edge G hconn C hC R hcover hgirth
            _ _ (owner_spec G C hC u).1 (owner_spec G C hC v).1 hne
            u y v x rfl huy.symm rfl hvx.symm huv hxy.symm
          simpa only [Sym2.eq_swap] using hz

end Paper.HighGirthClusterMinor
#print axioms Paper.HighGirthClusterMinor.isMinor
#print axioms Paper.HighGirthClusterMinor.internal_card

#print axioms Paper.HighGirthClusterMinor.partition_card
#print axioms Paper.HighGirthClusterMinor.cross_card_le
