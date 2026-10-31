import Paper.Optimality.Treewidth.CliquePrivateNeighbors
import Paper.Optimality.Treewidth.CliqueContactPigeonhole
import Paper.Optimality.Treewidth.CliquePartitionDegrees

/-! A degree-two graph on eight vertices with no independent four-set
has a triangle, obtained by counting private neighbors of a dominating triple. -/
namespace Paper.CliqueEightComplementTriangle
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (H : SimpleGraph V) [DecidableRel H.Adj]

theorem exists_triangle (hV : Fintype.card V = 8) (hd : ∀ x, H.degree x ≤ 2)
    (hsmall : ∀ I : Finset V, H.IsIndepSet (I : Set V) → I.card ≤ 3) :
    ∃ S : Finset V, S.card = 3 ∧ H.IsClique (S : Set V) := by
  classical
  obtain ⟨D, hD, hdom, hind⟩ := CliqueEightComplement.independent_triple H hV hd hsmall
  let N : V → Finset V := fun x => D.filter (H.Adj x)
  have hU : Dᶜ.card = 5 := by rw [Finset.card_compl, hV, hD]
  have hn : ∀ x ∈ Dᶜ, (N x).Nonempty := by
    intro x hx
    obtain ⟨d, hdD, hxd⟩ := (hdom x).resolve_left (Finset.mem_compl.mp hx)
    exact ⟨d, Finset.mem_filter.mpr ⟨hdD, hxd⟩⟩
  have hs : (∑ x ∈ Dᶜ, (N x).card) ≤ 6 := by
    change (∑ x ∈ Dᶜ, H.inducedDegree x D) ≤ 6
    rw [CliquePartitionDegrees.cross_sum H Dᶜ D]
    calc
      _ ≤ ∑ d ∈ D, H.degree d := Finset.sum_le_sum (fun d _ => by
        have := CliquePartitionDegrees.partition H D d
        omega)
      _ ≤ ∑ _d ∈ D, (2 : ℕ) := Finset.sum_le_sum (fun d _ => hd d)
      _ = 6 := by simp [hD]
  obtain ⟨x, hx, y, hy, hxy, d, hdD, hNx, hNy⟩ :=
    CliqueContactPigeonhole.repeated_singleton Dᶜ D N hU hD hn
      (fun x _ => Finset.filter_subset _ _) hs
  have hxd : H.Adj x d := (Finset.mem_filter.mp
    (show d ∈ N x by rw [hNx]; exact Finset.mem_singleton_self d)).2
  have hyd : H.Adj y d := (Finset.mem_filter.mp
    (show d ∈ N y by rw [hNy]; exact Finset.mem_singleton_self d)).2
  have hadj : H.Adj x y := by
    apply CliquePrivateNeighbors.adjacent H D hD hind hsmall d hdD x y
      (Finset.mem_compl.mp hx) (Finset.mem_compl.mp hy) hxy
    · intro w hw h
      have hm : w ∈ N x := Finset.mem_filter.mpr ⟨hw, h⟩
      rw [hNx] at hm
      exact Finset.mem_singleton.mp hm
    · intro w hw h
      have hm : w ∈ N y := Finset.mem_filter.mpr ⟨hw, h⟩
      rw [hNy] at hm
      exact Finset.mem_singleton.mp hm
  have hdx : d ≠ x := hxd.ne.symm
  have hdy : d ≠ y := hyd.ne.symm
  refine ⟨{d, x, y}, by simp [hdx, hdy, hxy], ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact False.elim (hab rfl) | exact hxd | exact hxd.symm |
      exact hyd | exact hyd.symm | exact hadj | exact hadj.symm

end Paper.CliqueEightComplementTriangle
#print axioms Paper.CliqueEightComplementTriangle.exists_triangle
