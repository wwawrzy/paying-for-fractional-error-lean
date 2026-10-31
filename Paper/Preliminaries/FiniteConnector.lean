import Paper.Preliminaries.ConnectingSets

/-! Connecting-set dichotomy for an arbitrary finite index type, including
zero and one terminal sets. No tree certificate is an input. -/
namespace Paper.FiniteConnector
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem singleton_connected (v : V) : (G.induce (({v} : Finset V) : Set V)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, Finset.mem_singleton_self v⟩, ?_⟩
  intro u
  have he : u = (⟨v, Finset.mem_singleton_self v⟩ : ↥(({v} : Finset V) : Set V)) :=
    Subtype.ext (Finset.mem_singleton.mp u.property)
  subst u
  exact SimpleGraph.Reachable.refl _

theorem dichotomy {I : Type*} [Fintype I] (A : I → Finset V) (r : ℕ) (hr : 1 ≤ r) :
    (∃ T : Finset V, T.card ≤ r ∧ (G.induce (T : Set V)).Connected ∧ ∀ i, (T ∩ A i).Nonempty) ∨
      ∃ Z : Finset V, r * Z.card ≤ (Fintype.card I - 1) * Fintype.card V ∧
        ∀ C : Finset V, (G.induce (C : Set V)).Connected → Disjoint C Z →
          ¬ ∀ i, (C ∩ A i).Nonempty := by
  classical
  by_cases h0 : Fintype.card I = 0
  · haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp h0
    let v : V := Classical.choice inferInstance
    exact Or.inl ⟨{v}, by simp; omega, singleton_connected G v,
      fun i => isEmptyElim i⟩
  by_cases h1 : Fintype.card I = 1
  · obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp h1
    by_cases hA : (A i).Nonempty
    · obtain ⟨v, hv⟩ := hA
      left
      refine ⟨{v}, by simp; omega, singleton_connected G v, ?_⟩
      intro j
      rw [hi j]
      exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, hv⟩⟩
    · right
      refine ⟨∅, by simp, ?_⟩
      intro C _ _ hmeet
      obtain ⟨v, hv⟩ := hmeet i
      exact hA ⟨v, (Finset.mem_inter.mp hv).2⟩
  · let n := Fintype.card I - 2
    have hn : Fintype.card I = n + 2 := by dsimp [n]; omega
    let e : I ≃ Fin (n + 2) := Fintype.equivFinOfCardEq hn
    let A' := fun j => A (e.symm j)
    rcases ConnectingSets.dichotomy G A' r hr with hT | hZ
    · obtain ⟨T, hcard, hconn, hmeet⟩ := hT
      left
      refine ⟨T, hcard, hconn, ?_⟩
      intro i
      simpa only [A', Equiv.symm_apply_apply] using hmeet (e i)
    · obtain ⟨Z, hcard, hcut⟩ := hZ
      right
      refine ⟨Z, ?_, ?_⟩
      · have hh : n + 1 = Fintype.card I - 1 := by omega
        simpa only [hh] using hcard
      · intro C hconn hdis hmeet
        exact hcut C hconn hdis (fun j => hmeet (e.symm j))
end Paper.FiniteConnector
