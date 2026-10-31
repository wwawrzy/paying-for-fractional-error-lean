import Paper.Preliminaries.SelectProtocol

/-! One executed minimum query appends exactly the smallest remaining
eligible identifier at every active vertex, preserving private state. -/
namespace Paper.SelectStep
open BroadcastModel SelectProtocol
variable {V : Type} [Fintype V] [LinearOrder V]

def candidates (active eligible : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => active v = true ∧ eligible v = true)

theorem input_eq (active eligible : V → Bool) (l : List V) (s : V → State V)
    (ha : ∀ v, (s v).active = active v) (he : ∀ v, (s v).eligible = eligible v)
    (hl : ∀ v, active v = true → (s v).chosen = l) :
    (fun v => localInput v (s v)) = fun v => (active v,
      if v ∈ candidates active eligible \ l.toFinset then MinimumPayload.singleton v else 0) := by
  funext v
  dsimp only [localInput]
  rw [ha v, he v]
  cases hv : active v with
  | false => simp [hv, candidates]
  | true => rw [hl v hv]; simp [hv, candidates]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {b : ℕ} (C : BitCode V b) (D : ℕ) (active eligible : V → Bool) (root : V)
    (h : LeaderTreeCorrect.Spec G active D root ((LeaderTree.program C D).run G active))
    (har : active root = true) (l : List V) (s : V → State V)
    (ha : ∀ v, (s v).active = active v) (he : ∀ v, (s v).eligible = eligible v)
    (hl : ∀ v, active v = true → (s v).chosen = l) :
    ∀ v, active v = true → ((step C D).run G s v).chosen =
      MinimumList.next (candidates active eligible) l := by
  let T := candidates active eligible \ l.toFinset
  let weights : V → MinimumPayload.Data V := fun v =>
    if v ∈ T then MinimumPayload.singleton v else 0
  have hz : ∀ v, active v = false → weights v = 0 := by
    intro v hv
    have ht : v ∉ T := by simp [T, candidates, hv]
    simp [weights, ht]
  have hi := input_eq active eligible l s ha he hl
  intro v hv
  have hres := TaskAllReduce.correct G C (MinimumPayload.code C) D active root h har weights hz v hv
  rw [run_step, hi]
  change (match ((TaskAllReduce.program C (MinimumPayload.code C) D).run G
    (fun u => (active u, weights u)) v).2 with
    | none => (s v).chosen
    | some a => match a.value with
      | none => (s v).chosen
      | some u => (s v).chosen ++ [u]) = _
  rw [hres]
  change (match (∑ u, weights u).value with
    | none => (s v).chosen
    | some u => (s v).chosen ++ [u]) = _
  rw [show (∑ u, weights u).value = MaskedMinimum.minimum T from TaskMinimum.sum_selected T]
  rw [hl v hv]
  rfl
end Paper.SelectStep
