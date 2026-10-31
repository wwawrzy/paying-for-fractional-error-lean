import Paper.Preliminaries.SuccessfulRegions
import Paper.Preliminaries.RegionMinor

/-! The actual forest/region minor argument gives |X| ≤ 4|S|.
Residual updates and pass selections are explicit inputs; success regions
and the minor are constructed inside the proof. -/
namespace Paper.InitializerResidual
attribute [local instance] Classical.propDecidable
open SevenFoundation
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem discard_intersecting (own : V → Option V) (Q S : Finset V) :
    ∃ P : Finset V, P ⊆ Q ∧ Q.card ≤ P.card + S.card ∧
      ∀ x ∈ P, ∀ s ∈ S, own s ≠ some x := by
  classical
  let P := Q.filter (fun x => ∀ s ∈ S, own s ≠ some x)
  let B := Q \ P
  have hw : ∀ x : B, ∃ s ∈ S, own s = some x.val := by
    intro x
    have hx := Finset.mem_sdiff.mp x.property
    by_contra hn
    push_neg at hn
    exact hx.2 (Finset.mem_filter.mpr ⟨hx.1, hn⟩)
  let f := fun x : B => (hw x).choose
  have hf : ∀ x : B, f x ∈ S ∧ own (f x) = some x.val := fun x => (hw x).choose_spec
  have hinj : Function.Injective f := by
    intro x y he
    have ho := (hf x).2.symm.trans ((congrArg own he).trans (hf y).2)
    exact Subtype.ext (Option.some.inj ho)
  have hc : B.card ≤ S.card := by
    have hs : Finset.univ.image f ⊆ S := by
      intro s hs
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hs
      exact (hf x).1
    have hh := Finset.card_le_card hs
    simpa [Finset.card_image_of_injective _ hinj] using hh
  refine ⟨P, Finset.filter_subset .., ?_, ?_⟩
  · have hp := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (s := Q) (p := fun x => ∀ s ∈ S, own s ≠ some x))
    change B.card + P.card = Q.card at hp
    omega
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

theorem touched_count {T : ℕ} (own : V → Option V) (S : Fin T → Finset V)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (P : Finset V)
    (havoid : ∀ x ∈ P, ∀ s ∈ Finset.univ.biUnion S, own s ≠ some x)
    (htouch : ∀ x ∈ P, ∀ i, ∃ v, own v = some x ∧ v ∈ covered G (S i)) {x : V} (hx : x ∈ P) :
    T ≤ ((Finset.univ.biUnion S).filter (fun s => ∃ v, own v = some x ∧ G.Adj v s)).card := by
  classical
  have hw : ∀ i : Fin T, ∃ s ∈ S i, ∃ v, own v = some x ∧ G.Adj v s := by
    intro i
    obtain ⟨v, hv, hc⟩ := htouch x hx i
    obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hc
    rcases (mem_closed G v s).mp hvs with he | ha
    · have hsU := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩
      exact False.elim (havoid x hx s hsU (he ▸ hv))
    · exact ⟨s, hs, v, hv, ha.symm⟩
  let f := fun i : Fin T => (hw i).choose
  have hf : ∀ i, f i ∈ S i ∧ ∃ v, own v = some x ∧ G.Adj v (f i) := fun i => (hw i).choose_spec
  have hinj : Function.Injective f := by
    intro i j he
    by_contra hn
    exact Finset.disjoint_left.mp (hdis i j hn) (hf i).1 (he.symm ▸ (hf j).1)
  have hs : Finset.univ.image f ⊆ (Finset.univ.biUnion S).filter
      (fun s => ∃ v, own v = some x ∧ G.Adj v s) := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, (hf i).1⟩, (hf i).2⟩
  have hc := Finset.card_le_card hs
  simpa [Finset.card_image_of_injective _ hinj] using hc

set_option maxHeartbeats 2000000 in
theorem residual_bound {T μ : ℕ} (hT : 1 ≤ T) (hμ : 1 ≤ μ)
    {a : ℝ} (ha : 0 ≤ a) (hTa : 2 * a ≤ T) (hden : MinorDensity.Bound G a)
    {R : Fin (T + 1) → Finset V} {C : Fin T → Finset V}
    (M : InitialForest.Model G T (2 * T) μ R C)
    (X : Finset V) (hX : ∀ i : Fin T, X ⊆ R i.succ)
    (S : Fin T → Finset V) (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hremoved : ∀ i, R i.castSucc \ R i.succ ⊆ covered G (S i)) :
    X.card ≤ 4 * (Finset.univ.biUnion S).card := by
  classical
  obtain ⟨Q, hQX, hQcard, hsuccess⟩ := SuccessfulRegions.many_successful G hT M hμ X hX
  let own := ForestRegions.owner M.parent M.rank M.decrease X
  obtain ⟨P, hPQ, hPcard, havoid⟩ := discard_intersecting own Q (Finset.univ.biUnion S)
  have htouch : ∀ x ∈ P, ∀ i, ∃ v, own v = some x ∧ v ∈ covered G (S i) := by
    intro x hx i
    obtain ⟨v, hv, ho⟩ := hsuccess x (hPQ hx) i
    exact ⟨v, ho, hremoved i hv⟩
  have hcount := RegionMinor.count G M.parent M.rank M.decrease hden X P
    (Finset.univ.biUnion S) (hPQ.trans hQX) M.subgraph havoid T
    (fun _ hx => touched_count G own S hdis P havoid htouch hx)
  have hTp : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hSp : (0 : ℝ) ≤ (Finset.univ.biUnion S).card := Nat.cast_nonneg _
  have hcoef : a ≤ (T : ℝ) - a := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hSp
  have hP : (P.card : ℝ) ≤ (Finset.univ.biUnion S).card := by
    by_contra! hn
    have hp := mul_pos (by linarith : 0 < (T : ℝ) - a) (sub_pos.mpr hn)
    nlinarith
  have hPn : P.card ≤ (Finset.univ.biUnion S).card := by exact_mod_cast hP
  omega
end Paper.InitializerResidual
