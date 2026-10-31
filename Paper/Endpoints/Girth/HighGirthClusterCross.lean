import Paper.Endpoints.Girth.HighGirthClusterTree
import Paper.Endpoints.Girth.HighGirthDisjointPaths

/-! At most one genuine edge joins each pair of bounded-radius clusters when
all cycles have length greater than 4R+2 (R=2r in fv:hg:dilute). -/
namespace Paper.HighGirthClusterCross
open HighGirthVoronoi
variable {V : Type} [LinearOrder V]

set_option backward.isDefEq.respectTransparency false in
theorem cluster_path (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R) (c : V) (hc : c ∈ C)
    (x y : V) (hx : owner G C hC x = c) (hy : owner G C hC y = c) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 2*R ∧
      ∀ v ∈ p.support, owner G C hC v = c := by
  obtain ⟨p,hp,hps⟩ := cluster_walk G hconn C hC c hc x hx
  obtain ⟨q,hq,hqs⟩ := cluster_walk G hconn C hC c hc y hy
  let w := p.append q.reverse
  have hw : w.length ≤ 2*R := by
    have hrx := owner_radius G C hC R hcover x
    have hry := owner_radius G C hC R hcover y
    rw [hx] at hrx
    rw [hy] at hry
    simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse, hp,hq]
    omega
  have hws : ∀ v ∈ w.support, owner G C hC v = c := by
    intro v hv
    simp only [w, SimpleGraph.Walk.support_append, List.mem_append] at hv
    rcases hv with hv | hv
    · exact hps v hv
    · apply hqs v
      have hh := List.mem_of_mem_tail hv
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hh
  exact ⟨w.toPath, w.toPath.property, le_trans w.length_bypass_le hw,
    fun v hv => hws v (w.support_toPath_subset hv)⟩

theorem unique_cross_edge (G : SimpleGraph V) (hconn : G.Connected)
    (C : Finset V) (hC : C.Nonempty) (R : Nat)
    (hcover : ∀ v, ∃ c ∈ C, G.dist v c ≤ R)
    (hgirth : ∀ (v : V) (p : G.Walk v v), p.IsCycle → 4*R+2 < p.length)
    (c d : V) (hc : c ∈ C) (hd : d ∈ C) (hcd : c ≠ d)
    (x₁ x₂ y₁ y₂ : V)
    (hx₁ : owner G C hC x₁ = c) (hx₂ : owner G C hC x₂ = c)
    (hy₁ : owner G C hC y₁ = d) (hy₂ : owner G C hC y₂ = d)
    (he₁ : G.Adj x₁ y₁) (he₂ : G.Adj x₂ y₂) : s(x₁,y₁) = s(x₂,y₂) := by
  by_contra hne
  obtain ⟨p,hp,hplen,hps⟩ := cluster_path G hconn C hC R hcover c hc x₁ x₂ hx₁ hx₂
  obtain ⟨q,hq,hqlen,hqs⟩ := cluster_path G hconn C hC R hcover d hd y₂ y₁ hy₂ hy₁
  have hdisj : List.Disjoint p.support q.support := by
    intro v hvp hvq
    exact hcd ((hps v hvp).symm.trans (hqs v hvq))
  have hne' : s(y₁,x₁) ≠ s(x₂,y₂) := by simpa only [Sym2.eq_swap] using hne
  obtain ⟨w,hw,hlen⟩ := HighGirthDisjointPaths.cross_cycle p q hp hq hdisj he₁.symm he₂ hne'
  have hh := hgirth y₁ w hw
  omega

end Paper.HighGirthClusterCross
#print axioms Paper.HighGirthClusterCross.cluster_path
#print axioms Paper.HighGirthClusterCross.unique_cross_edge
