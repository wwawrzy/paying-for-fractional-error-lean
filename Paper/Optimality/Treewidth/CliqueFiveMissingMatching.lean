import Paper.Optimality.Treewidth.CliqueSixExtremalLocal
namespace Paper.CliqueFiveMissingMatching
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
theorem two_edges (hV : Fintype.card V = 5) (hd : ∀ x, Hᶜ.degree x ≤ 1)
    (hno : ∀ S : Finset V, S.card = 4 → ¬H.IsClique (S : Set V)) :
    Hᶜ.edgeFinset.card = 2 := by
  classical
  have hs := Hᶜ.sum_degrees_eq_twice_card_edges
  have hu : (∑ x : V, Hᶜ.degree x) ≤ 5 := by
    calc
      _ ≤ ∑ _x : V, (1 : ℕ) := Finset.sum_le_sum (fun x _ => hd x)
      _ = _ := by simp [hV]
  have hupper : Hᶜ.edgeFinset.card ≤ 2 := by omega
  by_contra hn
  have hsmall : Hᶜ.edgeFinset.card ≤ 1 := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let z := Classical.arbitrary V
  have hzcard : (Finset.univ.erase z : Finset V).card = 4 := by simp [hV]
  have hncl := hno (Finset.univ.erase z) hzcard
  change ¬(∀ a ∈ ((Finset.univ.erase z : Finset V) : Set V),
    ∀ b ∈ ((Finset.univ.erase z : Finset V) : Set V), a ≠ b → H.Adj a b) at hncl
  push Not at hncl
  obtain ⟨a,ha,b,hb,hab,hnab⟩ := hncl
  have hm : s(a,b) ∈ Hᶜ.edgeFinset := by
    exact mem_edgeFinset.mpr ((H.compl_adj a b).mpr ⟨hab,hnab⟩)
  have he : Hᶜ.edgeFinset = {s(a,b)} := by
    apply Eq.symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hm)
    simpa only [Finset.card_singleton] using hsmall
  have hcard : (Finset.univ.erase a : Finset V).card = 4 := by simp [hV]
  apply hno (Finset.univ.erase a) hcard
  intro x hx y hy hxy
  by_contra hnxy
  have hmem : s(x,y) ∈ Hᶜ.edgeFinset := mem_edgeFinset.mpr ((H.compl_adj x y).mpr ⟨hxy,hnxy⟩)
  rw [he,Finset.mem_singleton] at hmem
  rcases Sym2.eq_iff.mp hmem with ⟨hxa,_⟩ | ⟨_,hya⟩
  · exact (Finset.mem_erase.mp hx).1 hxa
  · exact (Finset.mem_erase.mp hy).1 hya
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem adjacent_unique (hd : ∀ x, G.degree x ≤ 1)
    {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) : b = c := by
  classical
  have hcard : (G.neighborFinset a).card ≤ 1 := by simpa using hd a
  exact Finset.card_le_one.mp hcard b (G.mem_neighborFinset a b |>.mpr hab)
    c (G.mem_neighborFinset a c |>.mpr hac)

theorem matching_endpoints (hd : ∀ x, G.degree x ≤ 1)
    (he : G.edgeFinset.card = 2) :
    ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.edgeFinset = {s(a,b),s(c,d)} := by
  classical
  obtain ⟨e,f,hef,hs⟩ := Finset.card_eq_two.mp he
  induction e using Sym2.ind with | _ a b =>
   induction f using Sym2.ind with | _ c d =>
    have hab : G.Adj a b := (G.mem_edgeFinset).mp (show s(a,b) ∈ G.edgeFinset by rw [hs]; simp)
    have hcd : G.Adj c d := (G.mem_edgeFinset).mp (show s(c,d) ∈ G.edgeFinset by rw [hs]; simp)
    refine ⟨a,b,c,d,G.ne_of_adj hab,?_,?_,?_,?_,G.ne_of_adj hcd,hs⟩
    · intro hac
      subst c
      have hbd := adjacent_unique G hd hab hcd
      subst d
      exact hef rfl
    · intro had
      subst d
      have hbc := adjacent_unique G hd hab hcd.symm
      subst c
      exact hef (Sym2.eq_swap)
    · intro hbc
      subst c
      have had := adjacent_unique G hd hab.symm hcd
      subst d
      exact hef (Sym2.eq_swap)
    · intro hbd
      subst d
      have hac := adjacent_unique G hd hab.symm hcd.symm
      subst c
      exact hef rfl
/-- Actual labels for a two-edge matching on five vertices, including the unused vertex. -/
theorem five_labels (hcard : Fintype.card V = 5)
    (hd : ∀ x, G.degree x ≤ 1) (he : G.edgeFinset.card = 2) :
    ∃ a b c d e : V,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      e ∉ ({a,b,c,d} : Finset V) ∧
      ({a,b,c,d,e} : Finset V) = Finset.univ ∧
      G.edgeFinset = {s(a,b),s(c,d)} := by
  classical
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,hedges⟩ := matching_endpoints G hd he
  have hfour : ({a,b,c,d} : Finset V).card = 4 := by
    simp [hab,hac,had,hbc,hbd,hcd]
  have hleft : (({a,b,c,d} : Finset V)ᶜ).card = 1 := by
    rw [Finset.card_compl,hcard,hfour]
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp hleft
  have heout : e ∉ ({a,b,c,d} : Finset V) := by
    apply Finset.mem_compl.mp
    rw [he]
    simp
  refine ⟨a,b,c,d,e,hab,hac,had,hbc,hbd,hcd,heout,?_,hedges⟩
  apply Finset.eq_univ_of_card
  have heq : ({a,b,c,d,e} : Finset V) = insert e {a,b,c,d} := by
    ext x
    simp only [Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [heq,Finset.card_insert_of_notMem heout,hfour,hcard]
theorem five_equiv (hcard : Fintype.card V = 5)
    (hd : ∀ x, G.degree x ≤ 1) (he : G.edgeFinset.card = 2) :
    ∃ e : Fin 5 ≃ V, G.edgeFinset = {s(e 0,e 1),s(e 2,e 3)} := by
  classical
  obtain ⟨a,b,c,d,z,hab,hac,had,hbc,hbd,hcd,hz,hall,hedges⟩ := five_labels G hcard hd he
  let f : Fin 5 → V := ![a,b,c,d,z]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf,by simpa using hcard.symm⟩
  refine ⟨Equiv.ofBijective f hb,?_⟩
  simpa [f,Equiv.ofBijective] using hedges
/-- Complete adjacency description, transported from actual endpoints. -/
theorem five_normal_form (hcard : Fintype.card V = 5)
    (hd : ∀ x, G.degree x ≤ 1) (he : G.edgeFinset.card = 2) :
    ∃ e : Fin 5 ≃ V, ∀ i j,
      G.Adj (e i) (e j) ↔
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  classical
  obtain ⟨e,he⟩ := five_equiv G hcard hd he
  refine ⟨e,?_⟩
  intro i j
  have hm : s(e i,e j) ∈ G.edgeFinset ↔ G.Adj (e i) (e j) := G.mem_edgeFinset
  rw [← hm,he]
  simp only [Finset.mem_insert,Finset.mem_singleton,Sym2.eq_iff,e.injective.eq_iff]
  tauto
end Paper.CliqueFiveMissingMatching
