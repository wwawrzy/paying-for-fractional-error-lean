import Paper.Preliminaries.ListPhase
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Bounded lists marked by the size of an external transversal.
The algorithm uses the original family at every cardinality level. -/
namespace Paper.MarkedLists
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [LinearOrder V]

def Admissible (H : Finset (Finset V)) (C : Finset V) : Prop :=
  C.Nonempty ∧ ∃ L ∈ H, C ⊆ L

def ExternalCover (H : Finset (Finset V)) (C B : Finset V) : Prop :=
  Disjoint B C ∧ ∀ L ∈ H, C ⊆ L → (L ∩ B).Nonempty

def Marked (H : Finset (Finset V)) (q : ℕ) (C : Finset V) : Prop :=
  Admissible H C ∧ ∀ B, ExternalCover H C B → q ≤ B.card

def MinimalMarked (H : Finset (Finset V)) (q : ℕ) (A : Finset V) : Prop :=
  Marked H q A ∧ ∀ C, C ⊂ A → ¬ Marked H q C

theorem original_marked (H : Finset (Finset V)) (q : ℕ)
    {L : Finset V} (hL : L ∈ H) (hne : L.Nonempty) : Marked H q L := by
  refine ⟨⟨hne, L, hL, Finset.Subset.refl _⟩, ?_⟩
  intro B hB
  obtain ⟨v, hv⟩ := hB.2 L hL (Finset.Subset.refl _)
  exact False.elim (Finset.disjoint_left.mp hB.1
    (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hv).1)

theorem small_external_cover_of_not_marked (H : Finset (Finset V)) (q : ℕ)
    {C : Finset V} (hC : Admissible H C) (hn : ¬ Marked H q C) :
    ∃ B, ExternalCover H C B ∧ B.card < q := by
  by_contra hh
  apply hn
  refine ⟨hC, fun B hB => ?_⟩
  by_contra hle
  exact hh ⟨B, hB, lt_of_not_ge hle⟩

/-- A small external cover for C must meet each marked extension of C. -/
theorem marked_superset_meets_external_cover (H : Finset (Finset V)) (q : ℕ)
    {C A B : Finset V} (hCA : C ⊆ A) (hA : Marked H q A)
    (hB : ExternalCover H C B) (hsmall : B.card < q) : (A ∩ B).Nonempty := by
  by_contra hn
  have hd : Disjoint B A := Finset.disjoint_left.mpr
    (fun v hvB hvA => hn ⟨v, Finset.mem_inter.mpr ⟨hvA, hvB⟩⟩)
  have hext : ExternalCover H A B :=
    ⟨hd, fun L hL hAL => hB.2 L hL (hCA.trans hAL)⟩
  exact (not_le_of_gt hsmall) (hA.2 B hext)

/-- The branching bound, with the remaining rank as induction parameter.
The filtered branches may overlap; the union bound needs no disjointness. -/
theorem minimal_marked_extensions_card_le (H : Finset (Finset V))
    (q : ℕ) (hq : 2 ≤ q) (k : ℕ) (F : Finset (Finset V)) (C : Finset V)
    (hC : C.Nonempty) (hmin : ∀ A ∈ F, MinimalMarked H q A)
    (hsub : ∀ A ∈ F, C ⊆ A) (hrank : ∀ A ∈ F, A.card ≤ C.card + k) :
    F.card ≤ (q - 1) ^ k := by
  induction k generalizing F C with
  | zero =>
    have he (A : Finset V) (hA : A ∈ F) : C = A :=
      Finset.eq_of_subset_of_card_le (hsub A hA) (by simpa using hrank A hA)
    simpa using (Finset.card_le_one.mpr (fun A hA B hB => (he A hA).symm.trans (he B hB)))
  | succ k ih =>
    by_cases hF : F.Nonempty
    · by_cases hmarked : Marked H q C
      · have he (A : Finset V) (hA : A ∈ F) : C = A := by
          by_contra hne
          exact (hmin A hA).2 C
            (Finset.ssubset_iff_subset_ne.mpr ⟨hsub A hA, hne⟩) hmarked
        have hcard : F.card ≤ 1 :=
          Finset.card_le_one.mpr (fun A hA B hB => (he A hA).symm.trans (he B hB))
        have hpos : 0 < q - 1 := by omega
        have hp : 0 < (q - 1) ^ (k + 1) := by positivity
        omega
      · obtain ⟨A, hA⟩ := hF
        obtain ⟨L, hL, hAL⟩ := (hmin A hA).1.1.2
        obtain ⟨B, hB, hsmall⟩ := small_external_cover_of_not_marked H q
          ⟨hC, L, hL, (hsub A hA).trans hAL⟩ hmarked
        let branch := fun b : V => F.filter (fun A => b ∈ A)
        have hbranch (b : V) (hb : b ∈ B) : (branch b).card ≤ (q - 1) ^ k := by
          have hbC : b ∉ C := Finset.disjoint_left.mp hB.1 hb
          apply ih (branch b) (insert b C) (Finset.insert_nonempty _ _)
          · intro A hA
            exact hmin A (Finset.mem_filter.mp hA).1
          · intro A hA
            exact Finset.insert_subset_iff.mpr
              ⟨(Finset.mem_filter.mp hA).2, hsub A (Finset.mem_filter.mp hA).1⟩
          · intro A hA
            have hh := hrank A (Finset.mem_filter.mp hA).1
            rw [Finset.card_insert_of_notMem hbC]
            omega
        have hcover : F ⊆ B.biUnion branch := by
          intro A hA
          obtain ⟨b, hb⟩ := marked_superset_meets_external_cover H q
            (hsub A hA) (hmin A hA).1 hB hsmall
          exact Finset.mem_biUnion.mpr ⟨b, (Finset.mem_inter.mp hb).2,
            Finset.mem_filter.mpr ⟨hA, (Finset.mem_inter.mp hb).1⟩⟩
        calc
          F.card ≤ (B.biUnion branch).card := Finset.card_le_card hcover
          _ ≤ B.card * (q - 1) ^ k := Finset.card_biUnion_le_card_mul B branch _ hbranch
          _ ≤ (q - 1) * (q - 1) ^ k := Nat.mul_le_mul_right _ (by omega)
          _ = (q - 1) ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
    · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      simp [he]

noncomputable def candidates (H : Finset (Finset V)) : Finset (Finset V) :=
  H.biUnion Finset.powerset

theorem mem_candidates (H : Finset (Finset V)) (C : Finset V) :
    C ∈ candidates H ↔ ∃ L ∈ H, C ⊆ L := by
  simp only [candidates, Finset.mem_biUnion, Finset.mem_powerset]

noncomputable def level (H : Finset (Finset V)) (q j : ℕ) : Finset (Finset V) :=
  (candidates H).filter (fun C => Marked H q C ∧ C.card = j)

theorem mem_level (H : Finset (Finset V)) (q j : ℕ) (C : Finset V) :
    C ∈ level H q j ↔ Marked H q C ∧ C.card = j := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨(mem_candidates H C).mpr h.1.1.2, h⟩

noncomputable def output (H : Finset (Finset V)) (q : ℕ) : ℕ → Finset V
  | 0 => ∅
  | j + 1 => ListPhase.phase (level H q (j + 1)) (output H q j)

noncomputable def processed (H : Finset (Finset V)) (q f : ℕ) : Finset (Finset V) :=
  (Finset.range f).biUnion (fun j =>
    SunflowerLists.uncovered (level H q (j + 1)) (output H q j))

theorem mem_processed (H : Finset (Finset V)) (q f : ℕ) (A : Finset V) :
    A ∈ processed H q f ↔ ∃ j < f,
      Marked H q A ∧ A.card = j + 1 ∧ Disjoint A (output H q j) := by
  simp only [processed, Finset.mem_biUnion, Finset.mem_range,
    SunflowerLists.uncovered, Finset.mem_filter, mem_level]
  aesop

theorem output_mono (H : Finset (Finset V)) (q : ℕ) {i j : ℕ} (hij : i ≤ j) :
    output H q i ⊆ output H q j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Finset.Subset.refl _
  | succ j ih =>
    by_cases hi : i ≤ j
    · exact (ih hi).trans (Finset.subset_union_left)
    · have he : i = j + 1 := by omega
      subst i
      exact Finset.Subset.refl _

theorem marked_covered (H : Finset (Finset V)) (q : ℕ) {A : Finset V}
    (hA : Marked H q A) : (A ∩ output H q A.card).Nonempty := by
  have hp : 0 < A.card := Finset.card_pos.mpr hA.1.1
  obtain ⟨j, hj⟩ : ∃ j, A.card = j + 1 := ⟨A.card - 1, by omega⟩
  rw [hj]
  exact ListPhase.phase_covers (level H q (j + 1)) (output H q j)
    (fun C hC => ((mem_level H q (j + 1) C).mp hC).1.1.1) A
    ((mem_level H q (j + 1) A).mpr ⟨hA, hj⟩)

theorem output_covers (H : Finset (Finset V)) (q f : ℕ)
    (hrank : ∀ L ∈ H, L.card ≤ f) (hnon : ∀ L ∈ H, L.Nonempty) :
    ∀ L ∈ H, (L ∩ output H q f).Nonempty := by
  intro L hL
  obtain ⟨v, hv⟩ := marked_covered H q (original_marked H q hL (hnon L hL))
  exact ⟨v, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hv).1,
    output_mono H q (hrank L hL) (Finset.mem_inter.mp hv).2⟩⟩

theorem processed_minimal (H : Finset (Finset V)) (q f : ℕ)
    {A : Finset V} (hA : A ∈ processed H q f) : MinimalMarked H q A := by
  obtain ⟨j, hj, hm, hcard, hd⟩ := (mem_processed H q f A).mp hA
  refine ⟨hm, ?_⟩
  intro C hCA hC
  have hlt := Finset.card_lt_card hCA
  have hle : C.card ≤ j := by omega
  obtain ⟨v, hv⟩ := marked_covered H q hC
  exact Finset.disjoint_left.mp hd
    ((Finset.ssubset_iff_subset_ne.mp hCA).1 (Finset.mem_inter.mp hv).1)
    (output_mono H q hle (Finset.mem_inter.mp hv).2)

theorem processed_incident_card_le (H : Finset (Finset V)) (q f : ℕ)
    (hf : 1 ≤ f) (hq : 2 ≤ q) (hrank : ∀ L ∈ H, L.card ≤ f) (v : V) :
    ((processed H q f).filter (fun A => v ∈ A)).card ≤ (q - 1) ^ (f - 1) := by
  apply minimal_marked_extensions_card_le H q hq (f - 1) _ {v} (by simp)
  · intro A hA
    exact processed_minimal H q f (Finset.mem_filter.mp hA).1
  · intro A hA
    simpa only [Finset.singleton_subset_iff] using (Finset.mem_filter.mp hA).2
  · intro A hA
    obtain ⟨L, hL, hAL⟩ :=
      (processed_minimal H q f (Finset.mem_filter.mp hA).1).1.1.2
    have hh := (Finset.card_le_card hAL).trans (hrank L hL)
    simp only [Finset.card_singleton]
    omega

/-- Every selected vertex represents a processed set and is its minimum ID. -/
theorem output_has_witness (H : Finset (Finset V)) (q f : ℕ)
    {v : V} (hv : v ∈ output H q f) :
    ∃ A ∈ processed H q f, v ∈ A ∧ ∀ u ∈ A, v ≤ u := by
  induction f with
  | zero => simpa [output] using hv
  | succ f ih =>
    rcases Finset.mem_union.mp hv with hold | hnew
    · obtain ⟨A, hA, hAv, hmin⟩ := ih hold
      obtain ⟨j, hj, hm, hc, hd⟩ := (mem_processed H q f A).mp hA
      exact ⟨A, (mem_processed H q (f + 1) A).mpr
        ⟨j, by omega, hm, hc, hd⟩, hAv, hmin⟩
    · obtain ⟨A, hA, hAv, hmin⟩ := ListPhase.picks_minimum _ hnew
      have hh := Finset.mem_filter.mp hA
      have hm := (mem_level H q (f + 1) A).mp hh.1
      exact ⟨A, (mem_processed H q (f + 1) A).mpr
        ⟨f, by omega, hm.1, hm.2, hh.2⟩, hAv, hmin⟩

theorem output_support (H : Finset (Finset V)) (q f : ℕ)
    {v : V} (hv : v ∈ output H q f) : ∃ L ∈ H, v ∈ L := by
  obtain ⟨A, hA, hvA, _⟩ := output_has_witness H q f hv
  obtain ⟨L, hL, hAL⟩ := (processed_minimal H q f hA).1.1.2
  exact ⟨L, hL, hAL hvA⟩

noncomputable def witness (H : Finset (Finset V)) (q f : ℕ) (v : V) : Finset V :=
  if hv : v ∈ output H q f then (output_has_witness H q f hv).choose else ∅

theorem witness_spec (H : Finset (Finset V)) (q f : ℕ) {v : V}
    (hv : v ∈ output H q f) :
    witness H q f v ∈ processed H q f ∧ v ∈ witness H q f v ∧
      ∀ u ∈ witness H q f v, v ≤ u := by
  simpa only [witness, dif_pos hv] using (output_has_witness H q f hv).choose_spec

theorem witness_injective (H : Finset (Finset V)) (q f : ℕ) :
    Set.InjOn (witness H q f) (output H q f) := by
  intro u hu v hv he
  have hU := witness_spec H q f hu
  have hV := witness_spec H q f hv
  apply le_antisymm
  · exact hU.2.2 v (he.symm ▸ hV.2.1)
  · exact hV.2.2 u (he ▸ hU.2.1)

def Cooccurs (H : Finset (Finset V)) (v w : V) : Prop :=
  ∃ L ∈ H, v ∈ L ∧ w ∈ L

noncomputable def pairs (H : Finset (Finset V)) (X Y : Finset V) : Finset (V × V) :=
  (X ×ˢ Y).filter (fun e => Cooccurs H e.1 e.2)

theorem pairs_card (H : Finset (Finset V)) (X Y : Finset V) :
    (pairs H X Y).card = ∑ v ∈ X, (Y.filter (Cooccurs H v)).card := by
  simp only [pairs, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

/-- The vertices represented by a processed set meeting O are charged using
the proved incident-family bound. -/
theorem paid_card_le (H : Finset (Finset V)) (q f : ℕ)
    (hf : 1 ≤ f) (hq : 2 ≤ q) (hrank : ∀ L ∈ H, L.card ≤ f) (O : Finset V) :
    ((output H q f).filter (fun v => ¬ Disjoint (witness H q f v) O)).card ≤
      (q - 1) ^ (f - 1) * O.card := by
  let paid := (processed H q f).filter (fun A => ¬ Disjoint A O)
  have hinj : ((output H q f).filter (fun v => ¬ Disjoint (witness H q f v) O)).card
      ≤ paid.card := by
    apply Finset.card_le_card_of_injOn (witness H q f)
    · intro v hv
      exact Finset.mem_filter.mpr
        ⟨(witness_spec H q f (Finset.mem_filter.mp hv).1).1, (Finset.mem_filter.mp hv).2⟩
    · intro u hu v hv he
      exact witness_injective H q f (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hv).1 he
  have hcover : paid ⊆ O.biUnion (fun v => (processed H q f).filter (fun A => v ∈ A)) := by
    intro A hA
    obtain ⟨v, hvA, hvO⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hA).2
    exact Finset.mem_biUnion.mpr
      ⟨v, hvO, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1, hvA⟩⟩
  calc
    _ ≤ paid.card := hinj
    _ ≤ (O.biUnion (fun v => (processed H q f).filter (fun A => v ∈ A))).card :=
      Finset.card_le_card hcover
    _ ≤ O.card * (q - 1) ^ (f - 1) :=
      Finset.card_biUnion_le_card_mul O _ _ (fun v _ => processed_incident_card_le H q f hf hq hrank v)
    _ = _ := Nat.mul_comm _ _

/-- A representative whose witness misses O has at least q distinct partners
in O in the original-list cooccurrence relation. -/
theorem unpaid_degree (H : Finset (Finset V)) (q f : ℕ) (O : Finset V)
    (hO : ∀ L ∈ H, (L ∩ O).Nonempty) {v : V}
    (hv : v ∈ output H q f) (hd : Disjoint (witness H q f v) O) :
    q ≤ (O.filter (Cooccurs H v)).card := by
  have hw := witness_spec H q f hv
  have hm := (processed_minimal H q f hw.1).1
  apply hm.2
  refine ⟨?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro w hwB hwA
    exact Finset.disjoint_left.mp hd hwA (Finset.mem_filter.mp hwB).1
  · intro L hL hAL
    obtain ⟨w, hwLO⟩ := hO L hL
    have hwL := (Finset.mem_inter.mp hwLO).1
    have hwO := (Finset.mem_inter.mp hwLO).2
    exact ⟨w, Finset.mem_inter.mpr ⟨hwL,
      Finset.mem_filter.mpr ⟨hwO, L, hL, hAL hw.2.1, hwL⟩⟩⟩

def factor (q f : ℕ) : ℕ := (q - 1) ^ (f - 1) + 1

/-- The complete combinatorial cost bound. The only geometric hypothesis is
an upper bound on the number of distinct cooccurring pairs across disjoint sets. -/
theorem output_card_le (H : Finset (Finset V)) (q f : ℕ)
    (hf : 1 ≤ f) (hq : 2 ≤ q) (hrank : ∀ L ∈ H, L.card ≤ f)
    (β : ℝ) (hβ : 0 < β) (hparam : 2 * β ≤ q)
    (hpairs : ∀ X Y : Finset V, Disjoint X Y →
      ((pairs H X Y).card : ℝ) ≤ β * ((X.card : ℝ) + Y.card))
    (O : Finset V) (hO : ∀ L ∈ H, (L ∩ O).Nonempty) :
    (output H q f).card ≤ factor q f * O.card := by
  let D := output H q f
  let X := D.filter (fun v => Disjoint (witness H q f v) O)
  let P := D.filter (fun v => ¬ Disjoint (witness H q f v) O)
  have hXO : Disjoint X O := by
    apply Finset.disjoint_left.mpr
    intro v hv hvO
    have hh := Finset.mem_filter.mp hv
    exact Finset.disjoint_left.mp hh.2 (witness_spec H q f hh.1).2.1 hvO
  have hlow : q * X.card ≤ (pairs H X O).card := by
    rw [pairs_card]
    calc
      _ = ∑ _v ∈ X, q := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun v hv =>
        unpaid_degree H q f O hO (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2)
  have hlow' : (q : ℝ) * X.card ≤ (pairs H X O).card := by exact_mod_cast hlow
  have hupper := hpairs X O hXO
  have hscale := mul_le_mul_of_nonneg_right hparam (Nat.cast_nonneg X.card : (0 : ℝ) ≤ X.card)
  have hXreal : (X.card : ℝ) ≤ O.card := by nlinarith
  have hX : X.card ≤ O.card := by exact_mod_cast hXreal
  have hP : P.card ≤ (q - 1) ^ (f - 1) * O.card := paid_card_le H q f hf hq hrank O
  have hcover : D ⊆ P ∪ X := by
    intro v hv
    by_cases hd : Disjoint (witness H q f v) O
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hv, hd⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hd⟩)
  calc
    D.card ≤ (P ∪ X).card := Finset.card_le_card hcover
    _ ≤ P.card + X.card := Finset.card_union_le _ _
    _ ≤ (q - 1) ^ (f - 1) * O.card + O.card := Nat.add_le_add hP hX
    _ = factor q f * O.card := by rw [factor]; ring

end Paper.MarkedLists

#print axioms Paper.MarkedLists.output_covers
#print axioms Paper.MarkedLists.processed_minimal
#print axioms Paper.MarkedLists.processed_incident_card_le
#print axioms Paper.MarkedLists.output_card_le
