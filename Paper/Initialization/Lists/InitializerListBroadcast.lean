import Paper.Preliminaries.FlagNeighborhood
import Paper.Endpoints.Rounding.CoreSelectionCorrect
import Paper.Initialization.Pruning.InitializerPass

/-! Two real one-bit broadcasts compute useful candidates, exact eligible
lists, bounded hosted lists and empty-list self-selection flags. -/
namespace Paper.InitializerListBroadcast
open BroadcastModel SevenFoundation
variable {V : Type} [LinearOrder V]

def candidateRound (h : ℕ) : Round V Bool (Bool × Bool) Bool where
  send _ _ s := s
  update v N s msg := (decide (h < (FlagNeighborhood.selected v N s msg).card), s)

def listRound (f : ℕ) : Round V (Bool × Bool) (Finset V × Bool) Bool where
  send _ _ s := s.1
  update v N s msg :=
    let eligible := FlagNeighborhood.selected v N s.1 msg
    (if s.2 && decide (eligible.card ≤ f) then eligible else ∅, s.2 && decide (eligible = ∅))

def program (h f : ℕ) : Program V Bool (Finset V × Bool) :=
  .seq (.broadcast 1 BitCode.bool (candidateRound h)) (.broadcast 1 BitCode.bool (listRound f))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def hosted (h f : ℕ) (R : Finset V) (v : V) : Finset V :=
  if v ∈ R ∧ (InitializerPass.eligibleList G h R v).card ≤ f then InitializerPass.eligibleList G h R v else ∅

theorem hosted_bound (h f : ℕ) (R : Finset V) : ∀ v, (hosted G h f R v).card ≤ f := by
  intro v
  unfold hosted
  split_ifs with hv
  · exact hv.2
  · simp

theorem hosted_local (h f : ℕ) (R : Finset V) : ∀ v, hosted G h f R v ⊆ closed G v := by
  intro v
  unfold hosted
  split_ifs
  · have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
    rw [InitializerPass.eligibleList, hinst]
    exact Finset.inter_subset_left
  · exact Finset.empty_subset _

theorem family_eq (h f : ℕ) (R : Finset V) :
    ListIncidenceBroadcast.family (hosted G h f R) = InitializerPass.lists G h f R := by
  ext t
  rw [ListIncidenceBroadcast.mem_family]
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [InitializerPass.lists, hinst]
  constructor
  · rintro ⟨hne, v, he⟩
    have hv : v ∈ R ∧ (InitializerPass.eligibleList G h R v).card ≤ f := by
      by_contra hn
      have hh : hosted G h f R v = ∅ := if_neg hn
      exact hne (he.symm.trans hh)
    have hlist : hosted G h f R v = InitializerPass.eligibleList G h R v := if_pos hv
    have hn : (InitializerPass.eligibleList G h R v).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rw [← hlist, he]; exact hne)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv.1, hv.2, hn⟩, hlist.symm.trans he⟩
  · intro ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hvR, hvlen, hvnon⟩ := Finset.mem_filter.mp hv
    exact ⟨Finset.nonempty_iff_ne_empty.mp hvnon, v, if_pos ⟨hvR, hvlen⟩⟩

theorem candidate_correct (h : ℕ) (R : Finset V) :
    eval G (candidateRound h) (fun v => decide (v ∈ R)) =
      fun v => (decide (v ∈ InitializerPass.candidates G h R), decide (v ∈ R)) := by
  funext v
  have he := FlagNeighborhood.correct G R v
  change FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ R))
    (fun u => decide (u.val ∈ R)) = _ at he
  change (decide (h < (FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ R))
    (fun u => decide (u.val ∈ R))).card), decide (v ∈ R)) = _
  rw [he]
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  simp only [InitializerPass.candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinst]

theorem correct (h f : ℕ) (R : Finset V) :
    (program (V := V) h f).run G (fun v => decide (v ∈ R)) =
      fun v => (hosted G h f R v, decide (v ∈ InitializerPass.emptyLists G h R)) := by
  change eval G (listRound f) (eval G (candidateRound h) (fun v => decide (v ∈ R))) = _
  rw [candidate_correct]
  funext v
  have hs := FlagNeighborhood.correct G (InitializerPass.candidates G h R) v
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  have he : FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ InitializerPass.candidates G h R))
      (fun u => decide (u.val ∈ InitializerPass.candidates G h R)) = InitializerPass.eligibleList G h R v := by
    rw [InitializerPass.eligibleList, hinst]
    exact hs
  change FlagNeighborhood.selected v (G.neighborFinset v) (decide (v ∈ InitializerPass.candidates G h R))
    (fun u => decide (u.val ∈ InitializerPass.candidates G h R)) = _ at hs
  let eligible := FlagNeighborhood.selected v (G.neighborFinset v)
    (decide (v ∈ InitializerPass.candidates G h R)) (fun u => decide (u.val ∈ InitializerPass.candidates G h R))
  change (if decide (v ∈ R) && decide (eligible.card ≤ f) then eligible else ∅,
      decide (v ∈ R) && decide (eligible = ∅)) = _
  dsimp only [eligible]
  simp only [he]
  simp only [hosted, InitializerPass.emptyLists, Finset.mem_filter, ← Bool.decide_and, decide_eq_true_eq]

theorem rounds (h f : ℕ) : (program (V := V) h f).rounds = 2 := rfl

theorem maxBits (h f : ℕ) : (program (V := V) h f).maxBits = 1 := rfl
end Paper.InitializerListBroadcast
