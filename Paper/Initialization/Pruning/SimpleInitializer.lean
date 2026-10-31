import Paper.Initialization.Pruning.InitializerBenchmark
import Paper.Initialization.Lists.MarkedLists
import Paper.Initialization.Lists.DirectListPairs
import Paper.Initialization.Pruning.PruningRun
import Paper.Initialization.Pruning.SuccessorPaths

/-! The actual list initializer used by the first dominating-set phase. -/
namespace Paper.SimpleInitializer
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass InitializerBenchmark
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def selected (h q : ℕ) (R : Finset V) : Finset V :=
  MarkedLists.output (lists G h h R) q h ∪ emptyLists G h R

noncomputable def physicalList (h : ℕ) (R : Finset V) (r : V) : Finset V :=
  if r ∈ listed G h h R then eligibleList G h R r else ∅

theorem physicalList_rank (h : ℕ) (R : Finset V) (r : V) :
    (physicalList G h R r).card ≤ h := by
  classical
  by_cases hr : r ∈ listed G h h R
  · simpa [physicalList, hr] using (Finset.mem_filter.mp hr).2.1
  · simp [physicalList, hr]

theorem physicalList_local (h : ℕ) (R : Finset V) (r v : V)
    (hv : v ∈ physicalList G h R r) : v = r ∨ G.Adj v r := by
  classical
  by_cases hr : r ∈ listed G h h R
  · have hmem : v ∈ closed G r ∩ candidates G h R := by
      simpa [physicalList, hr, eligibleList] using hv
    rcases (mem_closed G v r).mp (Finset.mem_inter.mp hmem).1 with he | ha
    · exact Or.inl he
    · exact Or.inr (G.symm ha)
  · simp [physicalList, hr] at hv

theorem physicalList_cooccurs_iff (h : ℕ) (R : Finset V) (v w : V) :
    (∃ L ∈ lists G h h R, v ∈ L ∧ w ∈ L) ↔
      ∃ r, v ∈ physicalList G h R r ∧ w ∈ physicalList G h R r := by
  classical
  constructor
  · rintro ⟨L, hL, hv, hw⟩
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hL
    refine ⟨r, ?_, ?_⟩
    · simpa [physicalList, hr] using hv
    · simpa [physicalList, hr] using hw
  · rintro ⟨r, hv, hw⟩
    have hr : r ∈ listed G h h R := by
      by_contra hr
      simp [physicalList, hr] at hv
    refine ⟨eligibleList G h R r, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
    · simpa [physicalList, hr] using hv
    · simpa [physicalList, hr] using hw

theorem pair_bound (h : ℕ) (hh : 1 ≤ h) (R : Finset V) (a : ℝ)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G a)
    (X Y : Finset V) (hdis : Disjoint X Y) :
    ((MarkedLists.pairs (lists G h h R) X Y).card : ℝ) ≤
      (h : ℝ) * (a + h) * (X.card + Y.card) := by
  classical
  have hb := DirectListPairs.card_pairs_le G (physicalList G h R) h
    hh (physicalList_rank G h R) (physicalList_local G h R) ha hden X Y hdis
  have heq : DirectListPairs.pairs (physicalList G h R) X Y =
      MarkedLists.pairs (lists G h h R) X Y := by
    ext e
    simp only [DirectListPairs.mem_pairs, MarkedLists.pairs, MarkedLists.Cooccurs,
      Finset.mem_filter, Finset.mem_product]
    have hco := physicalList_cooccurs_iff G h R e.1 e.2
    constructor
    · rintro ⟨hx, hy, hr⟩
      exact ⟨⟨hx, hy⟩, hco.mpr hr⟩
    · rintro ⟨⟨hx, hy⟩, hr⟩
      exact ⟨hx, hy, hco.mp hr⟩
  rw [← heq]
  exact hb

theorem selected_subset (h q : ℕ) (R : Finset V) :
    selected G h q R ⊆ candidates G h R ∪ R := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · obtain ⟨L, hL, hvL⟩ := MarkedLists.output_support (lists G h h R) q h hv
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hL
    exact Finset.mem_union_left _ ((Finset.mem_inter.mp hvL).2)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mp hv).1

theorem small_covered (h q : ℕ) (R : Finset V) {v : V} (hv : v ∈ R)
    (hsmall : (eligibleList G h R v).card ≤ h) :
    v ∈ covered G (selected G h q R) := by
  classical
  by_cases hn : (eligibleList G h R v).Nonempty
  · have hs : eligibleList G h R v ∈ lists G h h R :=
      Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hsmall, hn⟩, rfl⟩
    obtain ⟨u, hu⟩ := MarkedLists.output_covers (lists G h h R) q h
      (lists_rank G h h R) (lists_nonempty G h h R) _ hs
    have hu' := Finset.mem_inter.mp hu
    have huv := (Finset.mem_inter.mp hu'.1).1
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_union_left _ hu'.2,
      (closed_symm G u v).mp huv⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    exact subset_covered G _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨hv, he⟩))

noncomputable def residual (h q : ℕ) (R : Finset V) : Finset V :=
  R \ covered G (selected G h q R)

noncomputable def state (h q : ℕ) (R₀ : Finset V) : ℕ → Finset V
  | 0 => R₀
  | n + 1 => residual G h q (state h q R₀ n)

noncomputable def selection (h q : ℕ) (R₀ : Finset V) (n : ℕ) : Finset V :=
  selected G h q (state G h q R₀ n)

noncomputable def run (h q T : ℕ) (R₀ : Finset V) : PruningRun.Run G h h T where
  residual := state G h q R₀
  selected := selection G h q R₀
  step := by
    intro i hi
    rfl
  support := by
    intro i hi
    exact selected_subset G h q (state G h q R₀ i)
  short_covered := by
    intro i hi v hv hs
    exact small_covered G h q (state G h q R₀ i) hv hs

theorem pass_cost (h q : ℕ) (hh : 1 ≤ h) (a : ℝ) (ha : 1 ≤ a)
    (hden : MinorDensity.Bound G a) (hq : 2 * (h : ℝ) * (a + h) ≤ q)
    (R O : Finset V) (hO : R ⊆ covered G O) :
    (selected G h q R).card ≤
      h * (MarkedLists.factor q h + 1) * O.card := by
  classical
  obtain ⟨D, hD, hDc⟩ := list_benchmark G h h hh R O hO
  have hhit : ∀ L ∈ lists G h h R, (L ∩ D).Nonempty := hD
  have hpair := pair_bound G h hh R a ha hden
  have hq' : 2 * ((h : ℝ) * (a + h)) ≤ q := by nlinarith
  have hhreal : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hq2real : (2 : ℝ) ≤ q := by nlinarith [hhreal, ha, hq]
  have hq2 : 2 ≤ q := by exact_mod_cast hq2real
  have hmarked := MarkedLists.output_card_le (lists G h h R) q h
    hh hq2 (lists_rank G h h R)
    ((h : ℝ) * (a + h)) (by positivity) hq' (pair_bound G h hh R a ha hden)
    D hhit
  have he := empty_count G h R O hO
  have hu := Finset.card_union_le
    (MarkedLists.output (lists G h h R) q h) (emptyLists G h R)
  have hmult := Nat.mul_le_mul_left (MarkedLists.factor q h) hDc
  change (selected G h q R).card ≤ _ at hu
  nlinarith

theorem output_spec (h q T : ℕ) (R₀ O : Finset V)
    (_hO : R₀ ⊆ covered G O) :
    R₀ ⊆ covered G ((PruningRun.union G (run G h q T R₀)) ∪
      state G h q R₀ T) := by
  simpa [run, state] using PruningRun.output_covers G (run G h q T R₀)

theorem assembled_bound (p q : ℕ) (hp : 1 ≤ p) (a : ℝ) (ha : 1 ≤ a)
    (hpa : a ≤ (p : ℝ)) (hden : MinorDensity.Bound G a)
    (hq : 2 * ((3*p : ℕ) : ℝ) * (a + 3*p) ≤ q)
    (R₀ O : Finset V) (hO : R₀ ⊆ covered G O) :
    R₀ ⊆ covered G ((PruningRun.union G (run G (3*p) q (p+1) R₀)) ∪
      (state G (3*p) q R₀ (p+1))) ∧
    ((PruningRun.union G (run G (3*p) q (p+1) R₀) ∪
      state G (3*p) q R₀ (p+1)).card : ℝ) ≤
      ((p+1) * (p+2) * (3*p) * (MarkedLists.factor q (3*p)+1) : ℝ) * O.card := by
  classical
  let P := run G (3*p) q (p+1) R₀
  have hpden : MinorDensity.Bound G (p : ℝ) := by
    intro A _ _ J _ hm
    have hh := hden A J hm
    exact hh.trans (mul_le_mul_of_nonneg_right hpa (by positivity))
  have hres := SuccessorPaths.residual_bound G p hp hpden P
  have hqPass : 2 * ((3*p : ℕ) : ℝ) * (a + ((3*p : ℕ) : ℝ)) ≤ q := by
    simpa [Nat.cast_mul] using hq
  have hper : ∀ i, i < p+1 →
      ((P.selected i).card : ℝ) ≤
        (3*p : ℝ) * (MarkedLists.factor q (3*p)+1) * O.card := by
    intro i hi
    have hRi : P.residual i ⊆ R₀ :=
      PruningRun.antitone G P (Nat.zero_le i) (by omega)
    have hc := pass_cost G (3*p) q (by omega) a ha hden hqPass
      (P.residual i) O (fun v hv => hO (hRi hv))
    exact_mod_cast hc
  have hu : (PruningRun.union G P).card ≤
      (p+1) * ((3*p) * (MarkedLists.factor q (3*p)+1) * O.card) := by
    have hc : (PruningRun.union G P).card ≤
        ∑ i ∈ Finset.range (p+1), (P.selected i).card := Finset.card_biUnion_le
    have hs : (∑ i ∈ Finset.range (p+1), (P.selected i).card) ≤
        ∑ _i ∈ Finset.range (p+1),
          ((3*p) * (MarkedLists.factor q (3*p)+1) * O.card) :=
      Finset.sum_le_sum (fun i hi => by
        exact_mod_cast hper i (Finset.mem_range.mp hi))
    have hsum : (∑ _i ∈ Finset.range (p+1),
        ((3*p) * (MarkedLists.factor q (3*p)+1) * O.card)) =
        (p+1) * ((3*p) * (MarkedLists.factor q (3*p)+1) * O.card) := by simp
    exact hc.trans (hs.trans_eq hsum)
  have hD := Finset.card_union_le (PruningRun.union G P) (P.residual (p+1))
  have hcomb : (PruningRun.union G P ∪ P.residual (p+1)).card ≤
      (p+2) * (PruningRun.union G P).card := by
    calc
      _ ≤ (PruningRun.union G P).card + (P.residual (p+1)).card := hD
      _ ≤ (PruningRun.union G P).card + (p+1) * (PruningRun.union G P).card :=
        Nat.add_le_add_left hres _
      _ = _ := by ring
  have hDnat : (PruningRun.union G P ∪ P.residual (p+1)).card ≤
      (p+2) * ((p+1) * ((3*p) * (MarkedLists.factor q (3*p)+1) * O.card)) :=
    hcomb.trans (Nat.mul_le_mul_left _ hu)
  have hDreal : ((PruningRun.union G P ∪ P.residual (p+1)).card : ℝ) ≤
      ((p+2) : ℝ) * ((p+1) * ((3*p) * (MarkedLists.factor q (3*p)+1) * O.card)) := by
    exact_mod_cast hDnat
  have hfinal : ((p+2) : ℝ) * ((p+1) * ((3*p) *
      (MarkedLists.factor q (3*p)+1) * O.card)) =
      ((p+1) * (p+2) * (3*p) * (MarkedLists.factor q (3*p)+1) : ℝ) * O.card := by
    push_cast
    ring
  constructor
  · exact output_spec G (3*p) q (p+1) R₀ O hO
  · exact hDreal.trans_eq hfinal

end Paper.SimpleInitializer

#print axioms Paper.SimpleInitializer.pair_bound
#print axioms Paper.SimpleInitializer.selected_subset
#print axioms Paper.SimpleInitializer.small_covered
#print axioms Paper.SimpleInitializer.run
#print axioms Paper.SimpleInitializer.pass_cost
#print axioms Paper.SimpleInitializer.assembled_bound
