import GraphTheory.SimpleGraph.Minor.Contraction
import GraphTheory.SimpleGraph.Minor.Antisymmetry
namespace SimpleGraph.EdgeContraction
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u v : V) (S : Set V)
def imageVertex (a : S) : contrMk u v '' S := ⟨contrMk u v a.val,⟨a.val,a.property,rfl⟩⟩

theorem imageVertex_reachable_of_adj {a b : S} (hab : (G.induce S).Adj a b) :
    ((contrGraph G u v).induce (contrMk u v '' S)).Reachable
      (imageVertex u v S a) (imageVertex u v S b) := by
  by_cases he : contrMk u v a.val = contrMk u v b.val
  · have hh : imageVertex u v S a = imageVertex u v S b := Subtype.ext he
    rw [hh]
  · exact (show ((contrGraph G u v).induce (contrMk u v '' S)).Adj
      (imageVertex u v S a) (imageVertex u v S b) from
      contrGraph_adj_of_adj G u v hab he).reachable

theorem imageVertex_reachable_of_walk {a b : S} (p : (G.induce S).Walk a b) :
    ((contrGraph G u v).induce (contrMk u v '' S)).Reachable
      (imageVertex u v S a) (imageVertex u v S b) := by
  induction p with
  | nil => exact Reachable.refl _
  | cons hab p ih => exact (imageVertex_reachable_of_adj G u v S hab).trans ih

theorem induce_image_connected (hS : (G.induce S).Connected) :
    ((contrGraph G u v).induce (contrMk u v '' S)).Connected := by
  obtain ⟨a⟩ := hS.nonempty
  letI : Nonempty (contrMk u v '' S) := ⟨imageVertex u v S a⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨a,ha,hea⟩ := x.property
  obtain ⟨b,hb,heb⟩ := y.property
  have hx : imageVertex u v S ⟨a,ha⟩ = x := Subtype.ext hea
  have hy : imageVertex u v S ⟨b,hb⟩ = y := Subtype.ext heb
  rw [← hx,← hy]
  obtain ⟨p⟩ := hS.preconnected ⟨a,ha⟩ ⟨b,hb⟩
  exact imageVertex_reachable_of_walk G u v S p
end SimpleGraph.EdgeContraction

namespace SimpleGraph.MinorModel
open SimpleGraph.EdgeContraction
variable {W V : Type*} [DecidableEq V] {H : SimpleGraph W} {G : SimpleGraph V}
variable (m : MinorModel H G)
theorem branch_index_eq {x y : W} {a : V} (hx : a ∈ m.branchSet x) (hy : a ∈ m.branchSet y) : x = y := by
  by_contra h
  exact Set.disjoint_left.mp (m.disjoint x y h) hx hy

variable (k : W) (u v : V) (hu : u ∈ m.branchSet k) (hv : v ∈ m.branchSet k)
include hu hv in
theorem contract_branch_images_disjoint (x y : W) (hxy : x ≠ y) :
    Disjoint (contrMk u v '' m.branchSet x) (contrMk u v '' m.branchSet y) := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,he⟩ := hy
  rcases (contrMk_eq_iff u v b a).mp he with he | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hxy (m.branch_index_eq ha (he ▸ hb))
  · exact hxy ((m.branch_index_eq ha hv).trans (m.branch_index_eq hb hu).symm)
  · exact hxy ((m.branch_index_eq ha hu).trans (m.branch_index_eq hb hv).symm)

noncomputable def contractInsideBranch : MinorModel H (contrGraph G u v) where
  branchSet x := contrMk u v '' m.branchSet x
  nonempty x := (m.nonempty x).image _
  disjoint := m.contract_branch_images_disjoint k u v hu hv
  connected x := induce_image_connected G u v (m.branchSet x) (m.connected x)
  adjacent x y hxy := by
    obtain ⟨a,ha,b,hb,hab⟩ := m.adjacent x y hxy
    refine ⟨contrMk u v a,⟨a,ha,rfl⟩,contrMk u v b,⟨b,hb,rfl⟩,?_⟩
    apply contrGraph_adj_of_adj G u v hab
    intro he
    exact Set.disjoint_left.mp (m.contract_branch_images_disjoint k u v hu hv x y hxy.ne)
      ⟨a,ha,rfl⟩ ⟨b,hb,he.symm⟩
theorem exists_internal_edge (a b : V) (ha : a ∈ m.branchSet k)
    (hb : b ∈ m.branchSet k) (hne : a ≠ b) :
    ∃ x ∈ m.branchSet k, ∃ y ∈ m.branchSet k, G.Adj x y := by
  letI : Nontrivial (m.branchSet k) := ⟨⟨⟨a,ha⟩,⟨b,hb⟩,fun h => hne (congrArg Subtype.val h)⟩⟩
  obtain ⟨y,hy⟩ := (m.connected k).preconnected.exists_adj_of_nontrivial (⟨a,ha⟩ : m.branchSet k)
  exact ⟨a,ha,y.val,y.property,hy⟩

noncomputable def singletonCopy (hs : ∀ x, (m.branchSet x).Subsingleton) : Copy H G where
  toHom := {
    toFun := m.representative
    map_rel' := by
      intro x y hxy
      obtain ⟨a,ha,b,hb,hab⟩ := m.adjacent x y hxy
      have ha' := hs x ha (m.representative_mem x)
      have hb' := hs y hb (m.representative_mem y)
      simpa only [ha',hb'] using hab }
  injective' := m.representative_injective

end SimpleGraph.MinorModel


