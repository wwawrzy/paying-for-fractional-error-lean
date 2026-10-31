import Paper.Optimality.Treewidth.CliqueMinimalSeparation

/-! Clique separators in globally minimal affine minor counterexamples.
The numerical condition concerns only the size of a complete separator;
the two smaller graphs used in the proof are actual induced minors. -/
namespace Paper.CliqueAffineSeparation

open SimpleGraph PlaneTopology.WagnerSeparation
variable {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem left_floor {S : Finset V} (s : Separation G S) [Fintype s.left]
    (B : ℕ) (hd : ∀ v, B ≤ G.degree v) : B ≤ Fintype.card s.left := by
  classical
  obtain ⟨v, hvL, hvR⟩ := s.left_private
  have hvS : v ∉ S := by
    intro h
    have hh : v ∈ s.left ∩ s.right := by rw [s.overlap]; exact h
    exact hvR hh.2
  let w : s.left := ⟨v, hvL⟩
  have he := CliqueFourSeparation.degree_preserved G s w hvS
  have hh := (CliqueFourSeparation.fill G s.left S).degree_lt_card_verts w
  have hvd := hd v
  dsimp only [w] at he hh
  omega

theorem no_clique_separator (k b B : ℕ)
    (he : G.edgeFinset.card + b = k * Fintype.card V)
    (hd : ∀ v, B ≤ G.degree v)
    (hminimal : CliqueMinorMinimal.BelowThreshold G k b B)
    (hchoose : ∀ s : ℕ, k * s ≤ s.choose 2 + b + 1)
    (S : Finset V) (hS : G.IsClique (S : Set V)) :
    IsEmpty (Separation G S) := by
  classical
  refine ⟨fun s => ?_⟩
  letI : Fintype s.left := Fintype.ofFinite _
  letI : Fintype s.right := Fintype.ofFinite _
  letI : Fintype (S : Set V) := Fintype.ofFinite _
  have hL := hminimal s.left (G.induce s.left) (IsMinor.of_induce G _)
    (left_floor G s B hd) (by
      simpa only [Nat.card_eq_fintype_card] using Separation.card_left_lt G s)
  have hRfloor : B ≤ Fintype.card s.right := by
    have hh := left_floor G (CliqueFourSeparation.flip G s) B hd
    simpa only [Fintype.card_eq_nat_card] using hh
  have hR := hminimal s.right (G.induce s.right) (IsMinor.of_induce G _)
    hRfloor (by
      simpa only [Nat.card_eq_fintype_card] using Separation.card_right_lt G s)
  have hsum := CliqueSeparationCount.edge_sum G s
  have hvertices := CliqueSeparationCount.vertex_sum G s
  have hscaled := congrArg (fun n => k * n) hvertices
  simp only [Nat.mul_add] at hscaled
  rw [CliqueMinimalSeparation.clique_edges G S hS] at hsum
  have hb := hchoose S.card
  omega

theorem five_choose_bound (s : ℕ) : 5 * s ≤ s.choose 2 + 14 + 1 := by
  have hlarge : ∀ m : ℕ, 5 * (m + 5) ≤ (m + 5).choose 2 + 14 + 1 := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      have hc : (m + 5 + 1).choose 2 = m + 5 + (m + 5).choose 2 := by
        simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (m + 5) 1
      have he : m + 1 + 5 = m + 5 + 1 := by omega
      rw [he, hc]
      omega
  by_cases hs : s < 5
  · interval_cases s <;> decide
  · have he : s - 5 + 5 = s := by omega
    simpa only [he] using hlarge (s - 5)

end Paper.CliqueAffineSeparation

#print axioms Paper.CliqueAffineSeparation.left_floor
#print axioms Paper.CliqueAffineSeparation.no_clique_separator
#print axioms Paper.CliqueAffineSeparation.five_choose_bound
