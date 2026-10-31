import Paper.Preliminaries.ComponentMap
import Paper.Preliminaries.RecursiveDeletion
import Paper.Preliminaries.FiniteConnector

/-! A true finite partition into connected small parts: recursive deletion
components and one singleton for every deleted vertex. -/
namespace Paper.SmallParts
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Data (S : Finset V) (k : ℕ) where
  parts : Finset (Finset V)
  nonempty : ∀ U ∈ parts, U.Nonempty
  subset : ∀ U ∈ parts, U ⊆ S
  connected : ∀ U ∈ parts, (G.induce (U : Set V)).Connected
  size : ∀ U ∈ parts, U.card ≤ k
  disjoint : (parts : Set (Finset V)).Pairwise Disjoint
  covers : ∀ v ∈ S, ∃ U ∈ parts, v ∈ U

noncomputable def label (S D : Finset V) (v : V) : Finset V :=
  if v ∈ D then {v} else ComponentMap.part G (S \ D) v

theorem label_self (S D : Finset V) (v : V) (hv : v ∈ S) : v ∈ label G S D v := by
  by_cases hd : v ∈ D
  · simp only [label, if_pos hd, Finset.mem_singleton]
  · rw [label, if_neg hd]
    exact ComponentMap.mem_self G (S \ D) v (Finset.mem_sdiff.mpr ⟨hv, hd⟩)

theorem label_subset (S D : Finset V) (hD : D ⊆ S) (v : V) : label G S D v ⊆ S := by
  by_cases hd : v ∈ D
  · simpa only [label, if_pos hd, Finset.singleton_subset_iff] using hD hd
  · rw [label, if_neg hd]
    exact (ComponentMap.subset G (S \ D) v).trans Finset.sdiff_subset

theorem label_consistent (S D : Finset V) (u v : V) (hu : u ∈ label G S D v) :
    label G S D u = label G S D v := by
  by_cases hvD : v ∈ D
  · have he : u = v := by simpa only [label, if_pos hvD, Finset.mem_singleton] using hu
    exact he ▸ rfl
  · have hu' : u ∈ ComponentMap.part G (S \ D) v := by simpa only [label, if_neg hvD] using hu
    have huD := (Finset.mem_sdiff.mp (ComponentMap.subset G (S \ D) v hu')).2
    simp only [label, if_neg hvD, if_neg huD]
    exact ComponentMap.eq_of_mem G (S \ D) u v hu'

theorem label_adj (S D : Finset V) (u v : V) (hu : u ∈ S \ D) (hv : v ∈ S \ D)
    (ha : G.Adj u v) : label G S D u = label G S D v := by
  simp only [label, if_neg (Finset.mem_sdiff.mp hu).2, if_neg (Finset.mem_sdiff.mp hv).2]
  exact ComponentMap.eq_of_adj G (S \ D) u v hu hv ha

noncomputable def of_cut (S D : Finset V) (k : ℕ) (hk : 0 < k) (hgood : RecursiveDeletion.Good G S D k) :
    Data G S k := by
  classical
  let p := label G S D
  let P := S.image p
  have hsubset : ∀ U ∈ P, U ⊆ S := by
    intro U hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hU
    exact label_subset G S D hgood.1 v
  refine {
    parts := P
    nonempty := ?_
    subset := hsubset
    connected := ?_
    size := ?_
    disjoint := ?_
    covers := ?_ }
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    exact ⟨v, label_self G S D v hv⟩
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    by_cases hd : v ∈ D
    · have he : p v = {v} := if_pos hd
      rw [he]
      letI : Nonempty V := ⟨v⟩
      exact FiniteConnector.singleton_connected G v
    · have he : p v = ComponentMap.part G (S \ D) v := if_neg hd
      rw [he]
      exact ComponentMap.connected G (S \ D) v (Finset.mem_sdiff.mpr ⟨hv, hd⟩)
  · intro U hU
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hU
    by_cases hd : v ∈ D
    · have he : p v = {v} := if_pos hd
      simpa only [he, Finset.card_singleton] using hk
    · have he : p v = ComponentMap.part G (S \ D) v := if_neg hd
      rw [he]
      exact hgood.2 _ (ComponentMap.subset G (S \ D) v)
        (ComponentMap.connected G (S \ D) v (Finset.mem_sdiff.mpr ⟨hv, hd⟩))
  · intro U hU W hW hne
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hW
    apply Finset.disjoint_left.mpr
    intro w hwu hwv
    exact hne ((label_consistent G S D w u hwu).symm.trans (label_consistent G S D w v hwv))
  · intro v hv
    exact ⟨p v, Finset.mem_image.mpr ⟨v, hv, rfl⟩, label_self G S D v hv⟩

theorem sum_card {S : Finset V} {k : ℕ} (P : Data G S k) : ∑ U ∈ P.parts, U.card = S.card := by
  have hcover : P.parts.biUnion id = S := by
    ext v
    constructor
    · intro hv
      obtain ⟨U, hU, hv⟩ := Finset.mem_biUnion.mp hv
      exact P.subset U hU hv
    · intro hv
      obtain ⟨U, hU, hv⟩ := P.covers v hv
      exact Finset.mem_biUnion.mpr ⟨U, hU, hv⟩
  rw [← Finset.card_biUnion P.disjoint]
  change (P.parts.biUnion id).card = S.card
  rw [hcover]
end Paper.SmallParts
