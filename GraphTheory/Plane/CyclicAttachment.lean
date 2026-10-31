import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The finite cyclic attachment lemma in position coordinates

Distinct positions around a finite cycle are represented by natural numbers
in increasing circular order. If two attachment sets do not alternate and
have at most two common positions, one whole attachment set lies in a closed
gap between consecutive positions of the other. This is the order-theoretic
part of the vertex-splitting argument, independent of graph and map APIs.
-/

namespace PlaneTopology.CyclicAttachment

/-- Strict cyclic interval from `a` to `b`, with wrap-around. -/
def openArc (a b x : ℕ) : Prop :=
  if a < b then a < x ∧ x < b else a < x ∨ x < b

/-- The closed cyclic interval includes its two endpoints. -/
def closedArc (a b x : ℕ) : Prop := x = a ∨ x = b ∨ openArc a b x

/-- Consecutive distinct positions of a finite attachment set. -/
def Consecutive (X : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ X ∧ b ∈ X ∧ a ≠ b ∧ ∀ x ∈ X, ¬openArc a b x

/-- No four distinct cyclic positions alternate between the two sets. -/
def Nonalternating (X Y : Finset ℕ) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ Y, ∀ d ∈ Y,
    a ≠ b → ¬(openArc a b c ∧ openArc b a d)

/-- A position outside a closed arc belongs to the complementary open arc. -/
theorem openArc_reverse_of_not_closed {a b x : ℕ} (_hab : a ≠ b)
    (h : ¬closedArc a b x) : openArc b a x := by
  unfold closedArc openArc at *
  split_ifs at * <;> omega

/-- Rotating an alternating quadruple preserves its cyclic alternation. -/
theorem openArc_alternate_rotate {a b x y : ℕ} (hab : a ≠ b)
    (hx : openArc a b x) (hy : openArc b a y) :
    x ≠ y ∧ openArc x y b ∧ openArc y x a := by
  unfold openArc at *
  split_ifs at * <;> omega

/-- Once a Y-position lies strictly between two X-positions, absence of
alternation puts all Y-positions in the corresponding closed arc. -/
theorem subset_closedArc_of_nonalt {X Y : Finset ℕ}
    (hno : Nonalternating X Y) {a b c : ℕ}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (hc : c ∈ Y) (hacb : openArc a b c) :
    ∀ d ∈ Y, closedArc a b d := by
  intro d hd
  by_contra hbad
  exact hno a ha b hb c hc d hd hab
    ⟨hacb, openArc_reverse_of_not_closed hab hbad⟩

/-- Every nonattachment position lies strictly in a gap between consecutive
attachments. Both ordinary and wrap-around gaps are constructed by extrema. -/
theorem exists_gap_around {X : Finset ℕ} (hX : 2 ≤ X.card) {y : ℕ} (hy : y ∉ X) :
    ∃ a b, Consecutive X a b ∧ openArc a b y := by
  have hne : X.Nonempty := Finset.card_pos.mp (by omega)
  let lo := X.min' hne
  let hi := X.max' hne
  have hlo : lo ∈ X := X.min'_mem hne
  have hhi : hi ∈ X := X.max'_mem hne
  have hlt : lo < hi := X.min'_lt_max'_of_card (by omega)
  have hmin : ∀ x ∈ X, lo ≤ x := fun x hx ↦ X.min'_le x hx
  have hmax : ∀ x ∈ X, x ≤ hi := fun x hx ↦ X.le_max' x hx
  have hwrap : Consecutive X hi lo := by
    refine ⟨hhi, hlo, by omega, ?_⟩
    intro x hx
    have hl := hmin x hx
    have hh := hmax x hx
    unfold openArc
    split_ifs <;> omega
  by_cases hbelow : y < lo
  · refine ⟨hi, lo, hwrap, ?_⟩
    unfold openArc
    split_ifs <;> omega
  by_cases habove : hi < y
  · refine ⟨hi, lo, hwrap, ?_⟩
    unfold openArc
    split_ifs <;> omega
  have hylo : y ≠ lo := by rintro rfl; exact hy hlo
  have hyhi : y ≠ hi := by rintro rfl; exact hy hhi
  let L := X.filter (fun x ↦ x < y)
  let R := X.filter (fun x ↦ y < x)
  have hL : L.Nonempty := ⟨lo, Finset.mem_filter.mpr ⟨hlo, by omega⟩⟩
  have hR : R.Nonempty := ⟨hi, Finset.mem_filter.mpr ⟨hhi, by omega⟩⟩
  let a := L.max' hL
  let b := R.min' hR
  have ha := Finset.mem_filter.mp (L.max'_mem hL)
  have hb := Finset.mem_filter.mp (R.min'_mem hR)
  have hab : a < b := by dsimp [a, b]; omega
  refine ⟨a, b, ⟨ha.1, hb.1, by omega, ?_⟩, ?_⟩
  · intro x hx hax
    have hxy : x ≠ y := by rintro rfl; exact hy hx
    have hax' : a < x ∧ x < b := by simpa [openArc, hab] using hax
    by_cases hleft : x < y
    · have hxa : x ≤ a := L.le_max' x (Finset.mem_filter.mpr ⟨hx, hleft⟩)
      omega
    · have hbx : b ≤ x := R.min'_le x (Finset.mem_filter.mpr ⟨hx, by omega⟩)
      omega
  · simp only [openArc, if_pos hab]
    exact ⟨ha.2, hb.2⟩

/-- The cyclic attachment conclusion when Y has a position outside X. -/
theorem exists_gap_of_nonalt_of_not_subset {X Y : Finset ℕ}
    (hX : 2 ≤ X.card) (hno : Nonalternating X Y) (hnot : ¬Y ⊆ X) :
    ∃ a b, Consecutive X a b ∧ ∀ y ∈ Y, closedArc a b y := by
  obtain ⟨c, hcY, hcX⟩ := Finset.not_subset.mp hnot
  obtain ⟨a, b, hgap, hc⟩ := exists_gap_around hX hcX
  exact ⟨a, b, hgap, subset_closedArc_of_nonalt hno hgap.1 hgap.2.1 hgap.2.2.1 hcY hc⟩

/-- The complete finite-order core of the Wagner vertex-splitting argument:
the absence of alternating attachments and of three common attachments
forces one whole attachment set into one closed consecutive gap. -/
theorem exists_gap_of_nonalt {X Y : Finset ℕ}
    (hX : 2 ≤ X.card) (hY : 2 ≤ Y.card)
    (hcommon : (X ∩ Y).card ≤ 2) (hno : Nonalternating X Y) :
    ∃ a b, Consecutive X a b ∧ ∀ y ∈ Y, closedArc a b y := by
  by_cases hsub : Y ⊆ X
  · have heq : Y.card = 2 := by
      rw [Finset.inter_eq_right.mpr hsub] at hcommon
      omega
    obtain ⟨c, d, hcd, hpair⟩ := Finset.card_eq_two.mp heq
    have hcY : c ∈ Y := by simp [hpair]
    have hdY : d ∈ Y := by simp [hpair]
    have hcX := hsub hcY
    have hdX := hsub hdY
    by_cases hforward : ∀ x ∈ X, ¬openArc c d x
    · refine ⟨c, d, ⟨hcX, hdX, hcd, hforward⟩, ?_⟩
      intro y hy
      have hy' : y = c ∨ y = d := by simpa [hpair] using hy
      exact hy'.elim (fun h ↦ Or.inl h) (fun h ↦ Or.inr (Or.inl h))
    by_cases hbackward : ∀ x ∈ X, ¬openArc d c x
    · refine ⟨d, c, ⟨hdX, hcX, hcd.symm, hbackward⟩, ?_⟩
      intro y hy
      have hy' : y = c ∨ y = d := by simpa [hpair] using hy
      exact hy'.elim (fun h ↦ Or.inr (Or.inl h)) (fun h ↦ Or.inl h)
    push Not at hforward hbackward
    obtain ⟨x, hxX, hx⟩ := hforward
    obtain ⟨z, hzX, hz⟩ := hbackward
    obtain ⟨hxz, hd, hc⟩ := openArc_alternate_rotate hcd hx hz
    exact False.elim (hno x hxX z hzX d hdY c hcY hxz ⟨hd, hc⟩)
  · exact exists_gap_of_nonalt_of_not_subset hX hno hsub

#print axioms exists_gap_around
#print axioms exists_gap_of_nonalt

/-- Excluding all increasing triples bounds a finite set of positions by two. -/
theorem card_le_two_of_no_increasing_triple (S : Finset ℕ)
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ¬(a < b ∧ b < c)) : S.card ≤ 2 := by
  by_contra hn
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < S.card)
  have h1 := h a ha b hb c hc
  have h2 := h a ha c hc b hb
  have h3 := h b hb a ha c hc
  have h4 := h b hb c hc a ha
  have h5 := h c hc a ha b hb
  have h6 := h c hc b hb a ha
  omega

end PlaneTopology.CyclicAttachment
