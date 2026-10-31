import Paper.Optimality.LowerBounds.CycleForcedDomination

/-! The actual middle intervals of packed 4T-word blocks on a cycle.
Their union has 2Ts vertices and at most 2s outside neighbors. -/
namespace Paper.CycleForcedSegments

open SimpleGraph SevenFoundation
open scoped BigOperators

def segment (N a len : ℕ) (hfit : a + len ≤ N) : Finset (Fin N) :=
  Finset.univ.image (fun i : Fin len => (⟨a + i.val, by omega⟩ : Fin N))

theorem mem_segment (N a len : ℕ) (hfit : a + len ≤ N) (v : Fin N) :
    v ∈ segment N a len hfit ↔ a ≤ v.val ∧ v.val < a + len := by
  constructor
  · intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    have he := congrArg Fin.val hi
    dsimp only at he
    have hh := i.isLt
    omega
  · intro hv
    refine Finset.mem_image.mpr ⟨⟨v.val - a, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp only
    omega

theorem segment_card (N a len : ℕ) (hfit : a + len ≤ N) :
    (segment N a len hfit).card = len := by
  have hinj : Function.Injective (fun i : Fin len => (⟨a + i.val, by omega⟩ : Fin N)) := by
    intro i j h
    have he := congrArg (fun z : Fin N => z.val) h
    apply Fin.ext
    dsimp only at he
    omega
  rw [segment, Finset.card_image_of_injective _ hinj]
  simp

theorem segment_boundary (n a len : ℕ) (ha : 0 < a) (hend : a + len < n + 3) :
    (covered (cycleGraph (n + 3)) (segment (n + 3) a len hend.le) \
      segment (n + 3) a len hend.le).card ≤ 2 := by
  let left : Fin (n + 3) := ⟨a - 1, by omega⟩
  let right : Fin (n + 3) := ⟨a + len, hend⟩
  have hsub : covered (cycleGraph (n + 3)) (segment (n + 3) a len hend.le) \
      segment (n + 3) a len hend.le ⊆ {left, right} := by
    intro v hv
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
    have hub := (mem_segment _ _ _ _ u).mp hu
    have hvnot := (mem_segment _ _ _ _ v).not.mp (Finset.mem_sdiff.mp hv).2
    rcases (mem_closed _ _ _).mp hvu with hself | hadj
    · exact False.elim ((Finset.mem_sdiff.mp hv).2 (by simpa only [hself] using hu))
    · have hn : v ∈ (cycleGraph (n + 3)).neighborFinset u :=
        ((cycleGraph (n + 3)).mem_neighborFinset u v).mpr hadj
      rw [cycleGraph_neighborFinset] at hn
      rcases Finset.mem_insert.mp hn with hprev | hnext
      · have hu0 : u ≠ 0 := by
          intro h
          have hz := congrArg (fun z : Fin (n + 3) => z.val) h
          simp only [Fin.val_zero] at hz
          omega
        have hp := Fin.val_sub_one_of_ne_zero hu0
        have he : v.val = a - 1 := by
          rw [hprev, hp] at hvnot ⊢
          omega
        exact Finset.mem_insert.mpr (Or.inl (Fin.ext he))
      · have heq : v = u + 1 := Finset.mem_singleton.mp hnext
        have hp := Fin.val_add_one_of_lt' (show u.val + 1 < n + 3 by omega)
        have he : v.val = a + len := by
          rw [heq, hp] at hvnot ⊢
          omega
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Fin.ext he)))
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem union_boundary {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset I) (S : I → Finset V)
    (hS : ∀ i ∈ P, (covered G (S i) \ S i).card ≤ 2) :
    (covered G (P.biUnion S) \ P.biUnion S).card ≤ 2 * P.card := by
  have hsub : covered G (P.biUnion S) \ P.biUnion S ⊆
      P.biUnion (fun i => covered G (S i) \ S i) := by
    intro v hv
    obtain ⟨u, hu, hvu⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hv).1
    obtain ⟨i, hi, hui⟩ := Finset.mem_biUnion.mp hu
    refine Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨u, hui, hvu⟩
    · exact fun hvi => (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)
  calc
    _ ≤ (P.biUnion (fun i => covered G (S i) \ S i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ P, (covered G (S i) \ S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ P, (2 : ℕ) := Finset.sum_le_sum hS
    _ = _ := by simp [Nat.mul_comm]

theorem middle_fits (N T s : ℕ) (hfit : 4 * T * s ≤ N) (b : Fin s) :
    4 * T * b.val + T + 2 * T ≤ N := by
  have hb := b.isLt
  have hm := Nat.mul_le_mul_left (4 * T) (show b.val + 1 ≤ s by omega)
  nlinarith only [hfit, hm]

def middle (N T s : ℕ) (hfit : 4 * T * s ≤ N) (b : Fin s) : Finset (Fin N) :=
  segment N (4 * T * b.val + T) (2 * T) (middle_fits N T s hfit b)

theorem middle_disjoint (N T s : ℕ) (hfit : 4 * T * s ≤ N) :
    ((Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint (middle N T s hfit) := by
  intro b _ c _ hbc
  apply Finset.disjoint_left.mpr
  intro v hvb hvc
  have hb := (mem_segment _ _ _ _ v).mp hvb
  have hc := (mem_segment _ _ _ _ v).mp hvc
  have hne : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hbc | hcb
  · have hm := Nat.mul_le_mul_left (4 * T) (show b.val + 1 ≤ c.val by omega)
    nlinarith only [hb.2, hc.1, hm]
  · have hm := Nat.mul_le_mul_left (4 * T) (show c.val + 1 ≤ b.val by omega)
    nlinarith only [hc.2, hb.1, hm]

theorem middle_union_card (N T s : ℕ) (hfit : 4 * T * s ≤ N) :
    ((Finset.univ : Finset (Fin s)).biUnion (middle N T s hfit)).card = 2 * T * s := by
  rw [Finset.card_biUnion (middle_disjoint N T s hfit)]
  simp only [middle, segment_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ac_rfl

theorem middle_union_boundary (n T s : ℕ) (hT : 1 ≤ T) (hfit : 4 * T * s ≤ n + 3) :
    (covered (cycleGraph (n + 3)) ((Finset.univ : Finset (Fin s)).biUnion (middle (n + 3) T s hfit)) \
      (Finset.univ : Finset (Fin s)).biUnion (middle (n + 3) T s hfit)).card ≤ 2 * s := by
  have hs (b : Fin s) : (covered (cycleGraph (n + 3)) (middle (n + 3) T s hfit b) \
      middle (n + 3) T s hfit b).card ≤ 2 := by
    have hb := b.isLt
    have ha : 0 < 4 * T * b.val + T := by omega
    have hm := Nat.mul_le_mul_left (4 * T) (show b.val + 1 ≤ s by omega)
    have hend : 4 * T * b.val + T + 2 * T < n + 3 := by nlinarith only [hfit, hm, hT]
    exact segment_boundary n _ _ ha hend
  simpa only [Finset.card_univ, Fintype.card_fin] using
    union_boundary (cycleGraph (n + 3)) Finset.univ (middle (n + 3) T s hfit) (fun b _ => hs b)

end Paper.CycleForcedSegments

#print axioms Paper.CycleForcedSegments.segment_boundary
#print axioms Paper.CycleForcedSegments.union_boundary
#print axioms Paper.CycleForcedSegments.middle_disjoint
#print axioms Paper.CycleForcedSegments.middle_union_card
#print axioms Paper.CycleForcedSegments.middle_union_boundary
