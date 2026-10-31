import Paper.Preliminaries.SmallParts

/-! Finite, choice-free part labels and their exact size/consistency laws. -/
namespace Paper.DisjointPartLabels
variable {V : Type} [DecidableEq V]

def label (F : Finset (Finset V)) (v : V) : Finset V :=
  F.biUnion (fun U => if v ∈ U then U else ∅)

theorem eq_of_mem (F : Finset (Finset V)) (hd : (F : Set (Finset V)).Pairwise Disjoint)
    (U : Finset V) (hU : U ∈ F) (v : V) (hv : v ∈ U) : label F v = U := by
  ext u
  constructor
  · intro hu
    obtain ⟨T, hT, hu⟩ := Finset.mem_biUnion.mp hu
    split_ifs at hu with hvt
    · have he : T = U := by
        by_contra hne
        exact Finset.disjoint_left.mp (hd hT hU hne) hvt hv
      exact he ▸ hu
    · exact False.elim (Finset.notMem_empty u hu)
  · intro hu
    exact Finset.mem_biUnion.mpr ⟨U, hU, by simpa only [if_pos hv] using hu⟩

variable [Fintype V] (G : SimpleGraph V) (S : Finset V) (k : ℕ) (P : SmallParts.Data G S k)

theorem outside (v : V) (hv : v ∉ S) : label P.parts v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨U, hU, hu⟩ := Finset.mem_biUnion.mp hu
  split_ifs at hu with hvU
  · exact hv (P.subset U hU hvU)
  · exact Finset.notMem_empty u hu

theorem exists_part (v : V) (hv : v ∈ S) :
    ∃ U ∈ P.parts, v ∈ U ∧ label P.parts v = U := by
  obtain ⟨U, hU, hvU⟩ := P.covers v hv
  exact ⟨U, hU, hvU, eq_of_mem P.parts P.disjoint U hU v hvU⟩

theorem self_mem (v : V) (hv : v ∈ S) : v ∈ label P.parts v := by
  obtain ⟨U, _, hvU, he⟩ := exists_part G S k P v hv
  exact he ▸ hvU

theorem nonempty_iff (v : V) : (label P.parts v).Nonempty ↔ v ∈ S := by
  constructor
  · intro hn
    by_contra hv
    rw [outside G S k P v hv] at hn
    exact Finset.not_nonempty_empty hn
  · intro hv
    exact ⟨v, self_mem G S k P v hv⟩

theorem size (v : V) : (label P.parts v).card ≤ k := by
  by_cases hv : v ∈ S
  · obtain ⟨U, hU, _, he⟩ := exists_part G S k P v hv
    rw [he]
    exact P.size U hU
  · rw [outside G S k P v hv, Finset.card_empty]
    exact Nat.zero_le k

theorem same_iff (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
    label P.parts u = label P.parts v ↔ ∃ U ∈ P.parts, u ∈ U ∧ v ∈ U := by
  constructor
  · intro he
    obtain ⟨U, hU, huU, hlabel⟩ := exists_part G S k P u hu
    refine ⟨U, hU, huU, ?_⟩
    rw [← hlabel, he]
    exact self_mem G S k P v hv
  · rintro ⟨U, hU, huU, hvU⟩
    exact (eq_of_mem P.parts P.disjoint U hU u huU).trans
      (eq_of_mem P.parts P.disjoint U hU v hvU).symm
end Paper.DisjointPartLabels
