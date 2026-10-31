import Paper.Preliminaries.TreeAggregateRound
import Paper.Preliminaries.LeaderTreeCorrect

/-! After transferring a rank, mass remains only at strictly smaller
ranks. This statement concerns actual evaluated broadcasts. -/
namespace Paper.TreeAggregateQuiet
open BroadcastModel BroadcastRouting TreeAggregateRound
variable {V A : Type} [Fintype V] [LinearOrder V] [AddCommMonoid A]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable {D : ℕ} {active : V → Bool} {root : V} {nodes : V → ParentElection.Node V D}

def Quiet (active : V → Bool) (nodes : V → ParentElection.Node V D)
    (r : ℕ) (s : V → State V A D) : Prop :=
  ∀ v, active v = false ∨ r < (nodes v).rank.val → (s v).2 = 0

theorem step (h : LeaderTreeCorrect.Spec G active D root nodes)
    (r : ℕ) (s : V → State V A D) (hs : ∀ v, (s v).1 = nodes v)
    (hq : Quiet active nodes (r + 1) s) :
    Quiet active nodes r (eval G (round D (r + 1)) s) := by
  intro v hv
  have hrzero : received G (fun w => packet (r + 1) (s w)) v = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    cases hp : packet (r + 1) (s w) with
    | none => simp [hp, payload]
    | some p =>
      obtain ⟨u, a⟩ := p
      by_cases hu : u = v
      · subst u
        obtain ⟨hr, hpar, _⟩ := packet_some hp
        rw [hs w] at hr hpar
        have hlow := h.parent_rank w v hpar
        have hav := (h.parent_active w v hpar).2
        rcases hv with hv | hv
        · exact False.elim (Bool.noConfusion (hav.symm.trans hv))
        · omega
      · simp [hp, payload, hu]
  rw [eval_mass, hrzero, add_zero]
  have hz_or_parent : (s v).2 = 0 ∨
      ((s v).1.rank.val = r + 1 ∧ (s v).1.parent.isSome) := by
    rcases hv with hi | hr
    · exact Or.inl (hq v (Or.inl hi))
    · by_cases hb : r + 1 < (nodes v).rank.val
      · exact Or.inl (hq v (Or.inr hb))
      · have heq : (nodes v).rank.val = r + 1 := by omega
        cases ha : active v with
        | false => exact Or.inl (hq v (Or.inl ha))
        | true =>
          have hvroot : v ≠ root := by
            intro he; subst v
            have := h.root_rank
            omega
          obtain ⟨u, hu⟩ := h.parent_exists v ha hvroot
          exact Or.inr ⟨by rw [hs v]; exact heq, by rw [hs v, hu]; rfl⟩
  unfold keep
  rcases hz_or_parent with hz | hp
  · split <;> simp [hz]
  · simp [hp]
end Paper.TreeAggregateQuiet
