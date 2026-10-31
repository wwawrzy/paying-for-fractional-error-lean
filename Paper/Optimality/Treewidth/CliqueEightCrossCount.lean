import Paper.Optimality.Treewidth.CliquePartitionDegrees

/-! The actual crossing counts behind the four-clique case on eight
vertices. If the other four vertices are not a clique, at most three
retained vertices can have exactly two neighbors on that side. This is
the strict count needed to choose among its available perfect matchings. -/
namespace Paper.CliqueEightCrossCount

open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem outside_degree (S : Finset V) (hS : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x) (x : V)
    (hno : ¬∀ y ∈ S, G.Adj x y) : 2 ≤ G.inducedDegree x Sᶜ := by
  classical
  have hsmall : G.inducedDegree x S ≤ 3 := by
    have hle := G.inducedDegree_le_card x S
    by_contra hn
    have heq : S.filter (G.Adj x) = S := Finset.eq_of_subset_of_card_le
      (Finset.filter_subset _ _) (by change S.card ≤ G.inducedDegree x S; omega)
    apply hno
    intro y hy
    have hh : y ∈ S.filter (G.Adj x) := by rw [heq]; exact hy
    exact (Finset.mem_filter.mp hh).2
  have hp := CliquePartitionDegrees.partition G S x
  have hx := hd x
  omega

theorem inside_degree (S : Finset V) (hS : S.card = 4)
    (hd : ∀ x, 5 ≤ G.degree x) (x : V) (hx : x ∈ S) :
    2 ≤ G.inducedDegree x Sᶜ := by
  classical
  have hsub : S.filter (G.Adj x) ⊆ S.erase x := by
    intro y hy
    obtain ⟨hyS, hxy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_erase.mpr ⟨fun heq => G.loopless.irrefl x (heq ▸ hxy), hyS⟩
  have hsmall := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hx, hS] at hsmall
  change G.inducedDegree x S ≤ 4 - 1 at hsmall
  have hp := CliquePartitionDegrees.partition G S x
  have hv := hd x
  omega

theorem noncomplete_support (hV : Fintype.card V = 8)
    (hd : ∀ x, 5 ≤ G.degree x) (S : Finset V) (hS : S.card = 4)
    (hnot : ¬G.IsClique ((Sᶜ : Finset V) : Set V)) :
    (S.filter (fun x => G.inducedDegree x Sᶜ = 2)).card ≤ 3 := by
  classical
  let R := Sᶜ
  have hR : R.card = 4 := by simp only [R, Finset.card_compl, hV, hS]
  have hRtype : Fintype.card (R : Set V) = 4 := by
    simpa only [Fintype.card_eq_nat_card, Finset.coe_sort_coe, Nat.card_eq_finsetCard] using hR
  have htop : (⊤ : SimpleGraph (R : Set V)).edgeFinset.card = 6 := by
    rw [card_edgeFinset_top_eq_card_choose_two, hRtype]
    decide
  change ¬(∀ a ∈ (R : Set V), ∀ b ∈ (R : Set V), a ≠ b → G.Adj a b) at hnot
  push Not at hnot
  obtain ⟨a, ha, b, hb, hab, hnab⟩ := hnot
  have hstrict : G.induce (R : Set V) < ⊤ := lt_of_le_not_ge le_top (by
    intro hle
    apply hnab
    exact hle (show (⊤ : SimpleGraph (R : Set V)).Adj ⟨a, ha⟩ ⟨b, hb⟩ from
      fun hh => hab (congrArg Subtype.val hh)))
  have he := Finset.card_lt_card (edgeFinset_strict_mono hstrict)
  rw [htop] at he
  have hshake := InducedCounting.sum_inducedDegree_eq_two_mul G R
  change (∑ r ∈ R, G.inducedDegree r R) =
    2 * (G.induce (R : Set V)).edgeFinset.card at hshake
  have hall : 20 ≤ ∑ r ∈ R, G.degree r := by
    calc
      20 = ∑ _r ∈ R, (5 : ℕ) := by simp [hR]
      _ ≤ _ := Finset.sum_le_sum (fun r _ => hd r)
  have hdecomp : (∑ r ∈ R, G.degree r) =
      (∑ r ∈ R, G.inducedDegree r S) + ∑ r ∈ R, G.inducedDegree r R := by
    simp_rw [CliquePartitionDegrees.partition G S]
    exact Finset.sum_add_distrib
  have hcross := CliquePartitionDegrees.cross_sum G S R
  have hlarge : 10 ≤ ∑ x ∈ S, G.inducedDegree x R := by omega
  change (S.filter (fun x => G.inducedDegree x R = 2)).card ≤ 3
  by_contra hn
  have hupper := Finset.card_filter_le S (fun x => G.inducedDegree x R = 2)
  have heq : S.filter (fun x => G.inducedDegree x R = 2) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have htwo : ∀ x ∈ S, G.inducedDegree x R = 2 := by
    intro x hx
    have hh : x ∈ S.filter (fun x => G.inducedDegree x R = 2) := by rw [heq]; exact hx
    exact (Finset.mem_filter.mp hh).2
  have hsum : (∑ x ∈ S, G.inducedDegree x R) = 8 := by
    calc
      _ = ∑ _x ∈ S, (2 : ℕ) := Finset.sum_congr rfl (fun x hx => htwo x hx)
      _ = 8 := by simp [hS]
  omega

end Paper.CliqueEightCrossCount

#print axioms Paper.CliqueEightCrossCount.outside_degree
#print axioms Paper.CliqueEightCrossCount.inside_degree
#print axioms Paper.CliqueEightCrossCount.noncomplete_support
