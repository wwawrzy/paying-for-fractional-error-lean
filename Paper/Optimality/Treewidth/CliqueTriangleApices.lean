import Paper.Optimality.Treewidth.CliqueConnectedApex
import Paper.Optimality.Treewidth.SevenCliqueProjection
namespace Paper.CliqueTriangleApices
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem impossible (hG : G.IsKMinorFree 7) (X B : Finset V)
    (hX : X.card = 3) (hB : B.Nonempty) (hdis : Disjoint X B)
    (hcl : G.IsClique (X : Set V))
    (ht : ∀ x ∈ X, ∀ b ∈ B, G.Adj x b)
    (hd : ∀ b : (B : Set V), 3 ≤ (G.induce (B : Set V)).degree b) : False := by
  classical
  obtain ⟨x,y,z,hxy,hxz,hyz,he⟩ := Finset.card_eq_three.mp hX
  have hx : x ∈ X := by rw [he]; simp
  have hy : y ∈ X := by rw [he]; simp
  have hz : z ∈ X := by rw [he]; simp
  let H := G.induce (B : Set V)
  let m := SevenCliqueProjection.induced_model G (B : Set V)
  have ha (w : V) (hw : w ∈ X) : ∀ b, Disjoint ({w} : Set V) (m.branchSet b) := by
    intro b
    rw [Set.disjoint_singleton_left]
    change w ∉ ({b.val} : Set V)
    intro hh
    exact (Finset.disjoint_left.mp hdis) hw ((show w = b.val from hh) ▸ b.property)
  have htouch (w : V) (hw : w ∈ X) : ∀ b, ∃ t ∈ ({w} : Set V), ∃ u ∈ m.branchSet b, G.Adj t u := by
    intro b
    exact ⟨w,rfl,b.val,rfl,ht w hw b.val b.property⟩
  have hf : H.IsKMinorFree 4 := CliqueConnectedApex.three_apices hG m {x} {y} {z}
    (Set.singleton_nonempty x) (Set.singleton_nonempty y) (Set.singleton_nonempty z)
    ((MinorModel.refl G).connected x) ((MinorModel.refl G).connected y) ((MinorModel.refl G).connected z)
    (by simpa only [Set.disjoint_singleton] using hxy)
    (by simpa only [Set.disjoint_singleton] using hxz)
    (by simpa only [Set.disjoint_singleton] using hyz)
    (ha x hx) (ha y hy) (ha z hz) (htouch x hx) (htouch y hy) (htouch z hz)
    ⟨y,rfl,x,rfl,(hcl hx hy hxy).symm⟩
    ⟨z,rfl,x,rfl,(hcl hx hz hxz).symm⟩
    ⟨z,rfl,y,rfl,(hcl hy hz hyz).symm⟩
  letI : Nonempty (B : Set V) := ⟨⟨hB.choose,hB.choose_spec⟩⟩
  obtain ⟨b,hb⟩ := CliqueFourElimination.low_degree H hf
  have hh : 3 ≤ H.degree b := hd b
  omega
end Paper.CliqueTriangleApices
