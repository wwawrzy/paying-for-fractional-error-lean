import Paper.Preliminaries.SimultaneousForest

/-! The initializer's simultaneous forest, with actual children in C_i and R_i.
The density, neighbor counts and number of passes are the only inputs. -/
namespace Paper.InitialForest
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

structure Model (T κ μ : ℕ) (R : Fin (T + 1) → Finset V) (C : Fin T → Finset V) where
  rank : V → ℕ
  parent : V → Option V
  decrease : ∀ u v, parent u = some v → rank v < rank u
  subgraph : ParentForest.graph parent rank decrease ≤ G
  demand_children : ∀ i v, v ∈ R i.succ →
    κ ≤ (((G.neighborFinset v) ∩ C i).filter (fun u => parent u = some v)).card
  candidate_children : ∀ i v, v ∈ C i →
    μ ≤ (((G.neighborFinset v) ∩ R i.castSucc).filter (fun u => parent u = some v)).card

theorem Model.isAcyclic {T κ μ : ℕ} {R : Fin (T + 1) → Finset V} {C : Fin T → Finset V}
    (M : Model G T κ μ R C) : (ParentForest.graph M.parent M.rank M.decrease).IsAcyclic :=
  ParentForest.isAcyclic M.parent M.rank M.decrease

/-- This is the forest lemma for all T passes, obtained by Hall's theorem.
The order and the forest are constructed, rather than supplied as certificates. -/
theorem exists_model {T d κ μ : ℕ} (hT : 1 ≤ T) (hd : 1 ≤ d)
    {a : ℝ} (hden : Incidence.InducedDensityBound G a) (hda : 2 * a ≤ d)
    (R : Fin (T + 1) → Finset V) (C : Fin T → Finset V)
    (hf : ∀ i v, v ∈ R i.succ → d + (T + T) * d * κ ≤ ((G.neighborFinset v) ∩ C i).card)
    (hh : ∀ i v, v ∈ C i → d + (T + T) * d * μ ≤ ((G.neighborFinset v) ∩ R i.castSucc).card) :
    Nonempty (Model G T κ μ R C) := by
  classical
  let A : Fin (T + T) → V → Finset V := Fin.append
    (fun i v => (G.neighborFinset v) ∩ C i)
    (fun i v => (G.neighborFinset v) ∩ R i.castSucc)
  let k : Fin (T + T) → V → ℕ := Fin.append
    (fun i v => if v ∈ R i.succ then κ else 0)
    (fun i v => if v ∈ C i then μ else 0)
  have hedge : ∀ j v u, u ∈ A j v → G.Adj v u := by
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro i v u hu
    · exact (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp (by simpa only [A, Fin.append_left, Fin.append_right] using hu)).1
    · exact (G.mem_neighborFinset v u).mp (Finset.mem_inter.mp (by simpa only [A, Fin.append_left, Fin.append_right] using hu)).1
  have hrow : ∀ j v, 0 < k j v → d + ((T + T) * d) * k j v ≤ (A j v).card := by
    intro j
    refine Fin.addCases ?_ ?_ j <;> intro i v hk
    · by_cases hv : v ∈ R i.succ
      · simpa only [A, k, Fin.append_left, Fin.append_right, if_pos hv] using hf i v hv
      · simp only [k, Fin.append_left, Fin.append_right, if_neg hv, lt_self_iff_false] at hk
    · by_cases hv : v ∈ C i
      · simpa only [A, k, Fin.append_left, Fin.append_right, if_pos hv] using hh i v hv
      · simp only [k, Fin.append_left, Fin.append_right, if_neg hv, lt_self_iff_false] at hk
  obtain ⟨O, ⟨M⟩⟩ := SimultaneousForest.exists_from_density G hd (by omega) hden hda A k hedge hrow
  refine ⟨{
    rank := O.rank
    parent := M.parent
    decrease := M.decrease
    subgraph := M.subgraph
    demand_children := ?_
    candidate_children := ?_ }⟩
  · intro i v hv
    have hc := M.requirement_card (i.castAdd T, v)
    have hs : ((SimultaneousForest.eligible G O A (i.castAdd T) v).filter
        (fun u => M.parent u = some v)) ⊆
        (((G.neighborFinset v) ∩ C i).filter (fun u => M.parent u = some v)) := by
      intro u hu
      have hm := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨by simpa only [A, Fin.append_left, Fin.append_right] using (Finset.mem_filter.mp hm.1).1, hm.2⟩
    have hc' : κ ≤ ((SimultaneousForest.eligible G O A (i.castAdd T) v).filter
        (fun u => M.parent u = some v)).card := by
      simpa only [k, Fin.append_left, if_pos hv] using hc
    exact hc'.trans (Finset.card_le_card hs)
  · intro i v hv
    have hc := M.requirement_card (i.natAdd T, v)
    have hs : ((SimultaneousForest.eligible G O A (i.natAdd T) v).filter
        (fun u => M.parent u = some v)) ⊆
        (((G.neighborFinset v) ∩ R i.castSucc).filter (fun u => M.parent u = some v)) := by
      intro u hu
      have hm := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨by simpa only [A, Fin.append_left, Fin.append_right] using (Finset.mem_filter.mp hm.1).1, hm.2⟩
    have hc' : μ ≤ ((SimultaneousForest.eligible G O A (i.natAdd T) v).filter
        (fun u => M.parent u = some v)).card := by
      simpa only [k, Fin.append_right, if_pos hv] using hc
    exact hc'.trans (Finset.card_le_card hs)
end Paper.InitialForest
