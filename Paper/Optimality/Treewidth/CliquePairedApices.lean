import Paper.Optimality.Treewidth.CliqueConnectedApex
import Paper.Optimality.Treewidth.SevenCliqueProjection
namespace Paper.CliquePairedApices
open SimpleGraph CliqueRootedProjection
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
theorem impossible (hG : G.IsKMinorFree 7) (T : Finset V) (hne : T.Nonempty)
    (x y v a : V) (hxy : G.Adj x y) (hva : G.Adj v a)
    (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxv : x ≠ v) (hyv : y ≠ v)
    (hxT : x ∉ T) (hyT : y ∉ T) (hvT : v ∉ T) (haT : a ∉ T)
    (hx : ∀ z ∈ T, G.Adj x z) (hy : ∀ z ∈ T, G.Adj y z)
    (hv : ∀ z ∈ T, G.Adj v z)
    (hd : ∀ z : (T : Set V), 3 ≤ (G.induce (T : Set V)).degree z) : False := by
  classical
  let H := G.induce (T : Set V)
  let m := SevenCliqueProjection.induced_model G (T : Set V)
  have hc : (G.induce ({v,a} : Set V)).Connected := by
    simpa only [Set.singleton_union] using
      connected_induce_union ((MinorModel.refl G).connected v).preconnected
        ((MinorModel.refl G).connected a).preconnected
        (Set.mem_singleton v) (Set.mem_singleton a) hva
  have hfree : H.IsKMinorFree 4 := by
    apply CliqueConnectedApex.three_apices hG m {x} {y} {v,a}
      (Set.singleton_nonempty x) (Set.singleton_nonempty y) ⟨v,by simp⟩
      ((MinorModel.refl G).connected x) ((MinorModel.refl G).connected y) hc
    · simp only [Set.disjoint_singleton]; exact hxy.ne
    · simp [Set.disjoint_singleton_left,hxv,hxa.ne]
    · simp [Set.disjoint_singleton_left,hyv,hya.ne]
    · intro z; rw [Set.disjoint_singleton_left]; change x ∉ ({z.val} : Set V)
      intro hh; exact hxT ((show x = z.val from hh) ▸ z.property)
    · intro z; rw [Set.disjoint_singleton_left]; change y ∉ ({z.val} : Set V)
      intro hh; exact hyT ((show y = z.val from hh) ▸ z.property)
    · intro z
      apply Set.disjoint_left.mpr
      intro w hw hwz
      change w = z.val at hwz
      subst w
      rcases hw with hz | hz
      · exact hvT (hz ▸ z.property)
      · exact haT ((show z.val = a from hz) ▸ z.property)
    · intro z; exact ⟨x,rfl,z.val,rfl,hx z.val z.property⟩
    · intro z; exact ⟨y,rfl,z.val,rfl,hy z.val z.property⟩
    · intro z; exact ⟨v,by simp,z.val,rfl,hv z.val z.property⟩
    · exact ⟨y,rfl,x,rfl,hxy.symm⟩
    · exact ⟨a,by simp,x,rfl,hxa.symm⟩
    · exact ⟨a,by simp,y,rfl,hya.symm⟩
  letI : Nonempty (T : Set V) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  obtain ⟨z,hz⟩ := CliqueFourElimination.low_degree H hfree
  have hh : 3 ≤ H.degree z := hd z
  omega
end Paper.CliquePairedApices
