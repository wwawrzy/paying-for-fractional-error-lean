import Paper.Initialization.Pruning.InitializerPass

/-! Iterate the concrete initialization pass. Later selections are disjoint
from earlier selections as a consequence of the actual residual updates. -/
namespace Paper.InitializerRun
attribute [local instance] Classical.propDecidable Classical.decEq
open SevenFoundation InitializerPass
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def state (a h f : ℕ) (R₀ : Finset V) : ℕ → Finset V
  | 0 => R₀
  | n + 1 => residual G a h f (state a h f R₀ n)

noncomputable def selection (a h f : ℕ) (R₀ : Finset V) (n : ℕ) : Finset V :=
  selected G a h f (state G a h f R₀ n)

noncomputable def past (a h f : ℕ) (R₀ : Finset V) (n : ℕ) : Finset V :=
  (Finset.range n).biUnion (selection G a h f R₀)

theorem antitone (a h f : ℕ) (R₀ : Finset V) : Antitone (state G a h f R₀) :=
  antitone_nat_of_succ_le (fun _ => Finset.sdiff_subset)

theorem removed_covered (a h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    state G a h f R₀ n \ state G a h f R₀ (n + 1) ⊆ covered G (selection G a h f R₀ n) := by
  intro v hv
  have hm := Finset.mem_sdiff.mp hv
  by_contra hn
  exact hm.2 (Finset.mem_sdiff.mpr ⟨hm.1, hn⟩)

theorem earlier_neighborhood_disjoint (a h f : ℕ) (R₀ : Finset V) {i j : ℕ} (hij : i < j)
    {v : V} (hv : v ∈ selection G a h f R₀ i) : Disjoint (closed G v) (state G a h f R₀ j) := by
  apply Finset.disjoint_left.mpr
  intro u hu huR
  have hu' := antitone G a h f R₀ (show i + 1 ≤ j by omega) huR
  exact (Finset.mem_sdiff.mp hu').2 (Finset.mem_biUnion.mpr ⟨v, hv, hu⟩)

theorem selections_disjoint (a h f : ℕ) (ha : 1 ≤ a) (R₀ : Finset V) {i j : ℕ} (hne : i ≠ j) :
    Disjoint (selection G a h f R₀ i) (selection G a h f R₀ j) := by
  have forward : ∀ {i j : ℕ}, i < j → Disjoint (selection G a h f R₀ i) (selection G a h f R₀ j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    have hdis := earlier_neighborhood_disjoint G a h f R₀ hij hvi
    have hz : ((closed G v) ∩ state G a h f R₀ j).card = 0 := by
      rw [Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.card_empty]
    rcases Finset.mem_union.mp (selected_subset G a h f ha _ hvj) with hvC | hvR
    · have hc := (Finset.mem_filter.mp hvC).2
      omega
    · exact Finset.disjoint_left.mp hdis (self_mem_closed G v) hvR
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact forward hij
  · exact (forward hji).symm

theorem past_succ (a h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    past G a h f R₀ (n + 1) = past G a h f R₀ n ∪ selection G a h f R₀ n := by
  simp only [past, Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

theorem remaining (a h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    state G a h f R₀ n = R₀ \ covered G (past G a h f R₀ n) := by
  induction n with
  | zero => simp [state, past, covered]
  | succ n ih =>
    change state G a h f R₀ n \ covered G (selection G a h f R₀ n) = _
    rw [ih, past_succ]
    ext v
    simp only [Finset.mem_sdiff, covered, Finset.union_biUnion, Finset.mem_union]
    tauto

theorem output_covers (a h f : ℕ) (R₀ : Finset V) (n : ℕ) :
    R₀ ⊆ covered G (past G a h f R₀ n ∪ state G a h f R₀ n) := by
  intro v hv
  by_cases hc : v ∈ covered G (past G a h f R₀ n)
  · exact covered_mono G Finset.subset_union_left hc
  · have hr : v ∈ state G a h f R₀ n := by rw [remaining]; exact Finset.mem_sdiff.mpr ⟨hv, hc⟩
    exact subset_covered G _ (Finset.mem_union_right _ hr)
end Paper.InitializerRun
