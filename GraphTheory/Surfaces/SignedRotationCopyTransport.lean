import GraphTheory.Surfaces.SignedRotationDartTransport
import GraphTheory.Surfaces.SignedRotationSubgraphGenus
import Mathlib.Combinatorics.SimpleGraph.Copy
namespace SimpleGraph.SignedRotation
variable {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
def isoDartEquiv (i : G ≃g H) : G.Dart ≃ H.Dart where
  toFun x := ⟨(i x.fst,i x.snd),i.map_rel_iff.mpr x.adj⟩
  invFun x := ⟨(i.symm x.fst,i.symm x.snd),i.symm.map_rel_iff.mpr x.adj⟩
  left_inv x := by apply Dart.ext; apply Prod.ext <;> simp
  right_inv x := by apply Dart.ext; apply Prod.ext <;> simp

theorem isoDartEquiv_source (i : G ≃g H) (a b : G.Dart) :
    (isoDartEquiv i a).fst = (isoDartEquiv i b).fst ↔ a.fst = b.fst := i.injective.eq_iff

theorem isoDartEquiv_reverse (i : G ≃g H) (a : G.Dart) :
    isoDartEquiv i a.symm = (isoDartEquiv i a).symm := rfl

noncomputable def isoTransport [Finite G.Dart] (r : SignedRotation G) (i : G ≃g H) : SignedRotation H :=
  r.dartTransport (isoDartEquiv i) (isoDartEquiv_source i) (isoDartEquiv_reverse i)

theorem isoTransport_eulerGenus [Finite G.Dart] (r : SignedRotation G) (i : G ≃g H) :
    (r.isoTransport i).eulerGenus = r.eulerGenus := r.dartTransport_eulerGenus _ _ _

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableRel G.Adj]
theorem exists_copy_genus_le (r : SignedRotation G) (f : Copy H G) :
    ∃ s : SignedRotation H, s.eulerGenus ≤ r.eulerGenus := by
  classical
  let S := f.toSubgraph.verts
  obtain ⟨s,hs⟩ := exists_induce_genus_le G r S
  have hsub : f.toSubgraph.coe ≤ G.induce S := by
    intro a b hab
    change f.toSubgraph.Adj a.val b.val at hab
    exact f.toSubgraph.adj_sub hab
  obtain ⟨t,ht⟩ := exists_subgraph_genus_le (G.induce S) s f.toSubgraph.coe hsub
  let q := t.isoTransport f.isoToSubgraph.symm
  refine ⟨q,?_⟩
  exact (t.isoTransport_eulerGenus f.isoToSubgraph.symm).le.trans (ht.trans hs)
end SimpleGraph.SignedRotation
