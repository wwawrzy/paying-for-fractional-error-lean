import Paper.Preliminaries.BranchChoice

/-! Correctness composition for the actual parent constructor. All proof
contracts here are instantiated by concrete terminal/control programs and
the strictly smaller budget in RecursiveSearchCorrect. -/
namespace Paper.SearchParentCorrect
open BroadcastModel
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem correct {B q m : ℕ} (H : Finset V) (c : V → Fin (B + 1))
    (b : V → Fin (q + 1)) (s : V → TerminalProtocol.Input V B q)
    (ha : ∀ r, (s r).active = decide (r ∈ H)) (hc : ∀ r, (s r).cost = c r)
    (hb : ∀ r, (s r).value = b r) (hz : ∀ r, r ∉ H → (b r).val = 0)
    (leaf : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (control : Program V (TerminalProtocol.Input V B q) (SearchControl.Output V B))
    (child : Program V (TerminalProtocol.Input V B q) (Option (SolutionWord.Word V B)))
    (ih : ∀ (b' : V → Fin (q + 1)) (s' : V → TerminalProtocol.Input V B q),
      (∀ r, (s' r).active = decide (r ∈ H)) → (∀ r, (s' r).cost = c r) →
      (∀ r, (s' r).value = b' r) → (∀ r, r ∉ H → (b' r).val = 0) →
        SearchSpec.Spec G child H c b' m s')
    (K : ℕ) (large : Prop) [Decidable large]
    (hleaf : ¬large → SearchSpec.Spec G leaf H c b (m + 1) s)
    (hflag : ∀ v ∈ H, (control.run G s v).large = decide large)
    (hinfo : ∀ v w, v ∈ H → w ∈ H → control.run G s v = control.run G s w)
    (hsupport : ∀ v ∈ H, ∀ t ∈ (control.run G s v).candidates, SolutionWord.id t ∈ H)
    (hcost : ∀ v ∈ H, SolutionWord.Consistent c (control.run G s v).candidates)
    (hlen : ∀ v ∈ H, (control.run G s v).candidates.length ≤ K)
    (hbranch : large → ∀ p : V → ℕ, (∑ u, p u) ≤ m + 1 →
      (∀ u, u ∉ H → p u = 0) → (∀ r, (b r).val ≤ ∑ u ∈ SevenFoundation.closed G r, p u) →
      ∀ v ∈ H, ∃ t ∈ (control.run G s v).candidates, 0 < p (SolutionWord.id t)) :
    SearchSpec.Spec G (BranchParent.program leaf control child K) H c b (m + 1) s := by
  let st := BranchParent.initialState G control s
  have hsa : ∀ r, (st r).input.active = decide (r ∈ H) := ha
  have hsc : ∀ r, (st r).input.cost = c r := hc
  have hsb : ∀ r, (st r).input.value = b r := hb
  have hsi : ∀ v w, v ∈ H → w ∈ H → (st v).info = (st w).info := hinfo
  have hss : ∀ v ∈ H, ∀ t ∈ (st v).info.candidates, SolutionWord.id t ∈ H := hsupport
  have hstc : ∀ v ∈ H, SolutionWord.Consistent c (st v).info.candidates := hcost
  have hrun (v : V) (hv : v ∈ H) :
      (BranchParent.program leaf control child K).run G s v =
        if large then BestWord.fold none ((List.range K).map (fun j => BranchLoop.choice G child j st v))
        else leaf.run G s v := by
    rw [BranchParent.run_program]
    dsimp only
    rw [hflag v hv]
    by_cases hl : large <;> simp [hl, st]
  constructor
  · intro v hv w hw
    rw [hrun v hv] at hw
    by_cases hl : large
    · rw [if_pos hl] at hw
      apply BestWord.fold_sound (SearchSpec.Valid G H c b (m + 1)) none _
        (by intro x hx; contradiction) ?_ w hw
      intro x hx y hy
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact BranchChoice.sound G H c child ih st b hsa hsc hsb hz hsi hss hstc j v hv y hy
    · rw [if_neg hl] at hw
      exact (hleaf hl).sound v hv w hw
  · intro p hp hps hpc v hv
    by_cases hl : large
    · obtain ⟨t, ht, htpos⟩ := hbranch hl p hp hps hpc v hv
      obtain ⟨w, hw, hcw⟩ := BranchChoice.complete_tag G H c child ih st b hsa hsc hsb hz hsi
        K v hv t ht (hlen v hv) (hcost v hv t ht) p hp hps hpc htpos
      obtain ⟨r, hr, hcr⟩ := BestWord.fold_le_member none _ hw
      refine ⟨r, ?_, hcr.trans hcw⟩
      rw [hrun v hv, if_pos hl]
      exact hr
    · obtain ⟨w, hw, hcw⟩ := (hleaf hl).complete p hp hps hpc v hv
      refine ⟨w, ?_, hcw⟩
      rw [hrun v hv, if_neg hl]
      exact hw
  · intro v w hv hw
    rw [hrun v hv, hrun w hw]
    by_cases hl : large
    · rw [if_pos hl, if_pos hl]
      congr 1
      apply List.map_congr_left
      intro j _
      exact BranchChoice.uniform G H c child ih st b hsa hsc hsb hz hsi j v w hv hw
    · rw [if_neg hl, if_neg hl]
      exact (hleaf hl).uniform v w hv hw
end Paper.SearchParentCorrect
