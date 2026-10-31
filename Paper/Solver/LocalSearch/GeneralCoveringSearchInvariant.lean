import Paper.Solver.LocalSearch.GeneralCoveringSearch

/-! Exact execution depends only on the active induced graph. Inactive
vertices may retain private incidence lists; their zero residual value makes
every branch update identical there. This compares the literal programs,
including their deterministic tie breaking, rather than their guarantees. -/
namespace Paper.GeneralCoveringSearchInvariant
open BroadcastModel
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G J : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel J.Adj]

theorem initialList (H A : Finset V) (hA : A ⊆ H)
    (hgraph : ∀ u ∈ H, ∀ v ∈ H, G.Adj u v ↔ J.Adj u v) (a m : ℕ) :
    HeavyListShape.initialList G H A a m = HeavyListShape.initialList J H A a m := by
  classical
  have hc (u : V) (hu : u ∈ H) :
      SevenFoundation.closed G u ∩ A = SevenFoundation.closed J u ∩ A := by
    ext v
    by_cases hv : v ∈ A
    · simp only [Finset.mem_inter, hv, and_true, SevenFoundation.mem_closed]
      rw [hgraph u hu v (hA hv)]
    · simp only [Finset.mem_inter, hv, and_false]
  have hh : H ∩ LocalSearchBounds.heavy G A m = H ∩ LocalSearchBounds.heavy J A m := by
    ext u
    by_cases hu : u ∈ H
    · simp only [Finset.mem_inter, hu, true_and, LocalSearchBounds.heavy,
        Finset.mem_filter, Finset.mem_univ, true_and, hc u hu]
    · simp only [Finset.mem_inter, hu, false_and]
  exact congrArg (fun S => MinimumList.run S (2 * a * m)) hh

/-- The terminal's representative alphabet is determined by the active set
and private incidence data, independently of physical edges outside it. -/
theorem terminal (K : ActiveTask.Context G) {b : ℕ} (ids : BitCode V b)
    (B q T m : ℕ) (s : V → GeneralCoveringResidual.Input V B q)
    (ha : ∀ u, (s u).base.active = decide (u ∈ K.vertices)) (v : V) (hv : v ∈ K.vertices) :
    (GeneralCoveringTerminal.program ids K.diameter B q T m).run G s v =
      (TabularSearch.choose
        (TerminalAlphabet.alphabet (GeneralCoveringRepresentatives.patterns T)
          ((GeneralCoveringRepresentatives.patterns T).map (fun z =>
            MaskedMinimum.minimum ((GeneralCoveringQuery.fiber K.vertices T
              (TerminalProtocolCorrect.demandList K.vertices (fun u => (s u).base.value) T)
              (fun u => (s u).targets) z).image (CostTag.tag (fun u => (s u).base.cost))))))
        m (DemandValues.values T
          (TerminalProtocolCorrect.demandList K.vertices (fun u => (s u).base.value) T)
          (fun u => (s u).base.value))).map (SolutionWord.fromEntries B) := by
  rw [GeneralCoveringTerminal.run_program,
    GeneralCoveringTerminal.data_run G K B q T (fun u => (s u).targets)
      (fun u => (s u).base.cost) (fun u => (s u).base.value) ids s ha
      (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) m v hv]
  have ht := GeneralCoveringTable.alphabet_correct G K ids B T
    (TerminalProtocolCorrect.demandList K.vertices (fun u => (s u).base.value) T)
    (fun u => (s u).targets) (fun u => (s u).base.cost)
    (fun u => GeneralCoveringTerminalData.maskInput
      (GeneralCoveringTerminal.dataState G ids K.diameter B q T s u))
    ha (fun _ => rfl)
    (GeneralCoveringTerminal.chosen G K B q T (fun u => (s u).targets)
      (fun u => (s u).base.cost) (fun u => (s u).base.value) ids s ha
      (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)) (fun _ _ => rfl) v hv
  rw [show GeneralCoveringTable.table G ids K.diameter B T
    (fun u => GeneralCoveringTerminalData.maskInput
      (GeneralCoveringTerminal.dataState G ids K.diameter B q T s u)) v = _ from ht]
  rfl

omit [Fintype V] in
theorem localUpdate_zero {B q : ℕ} (s : GeneralCoveringResidual.Input V B q)
    (hz : s.base.value.val = 0) (u : V) : GeneralCoveringResidual.localUpdate u s = s := by
  cases s with
  | mk base candidates targets =>
    cases base with
    | mk active cost value =>
      have he : (⟨value.val - if u ∈ candidates then 1 else 0,
          lt_of_le_of_lt (Nat.sub_le _ _) value.isLt⟩ : Fin (q + 1)) = value := by
        apply Fin.ext
        change value.val - _ = value.val
        change value.val = 0 at hz
        simp only [hz, Nat.zero_sub]
      change GeneralCoveringResidual.Input.mk ⟨active, cost, _⟩ candidates targets = _
      rw [he]

theorem run (K : ActiveTask.Context G) (L : ActiveTask.Context J)
    (hvertices : K.vertices = L.vertices)
    (hgraph : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, G.Adj u v ↔ J.Adj u v)
    {b : ℕ} (ids : BitCode V b) (a B q m : ℕ)
    (s : V → GeneralCoveringResidual.Input V B q)
    (ha : ∀ u, (s u).base.active = decide (u ∈ K.vertices))
    (hz : ∀ u, u ∉ K.vertices → (s u).base.value.val = 0) :
    ∀ v ∈ K.vertices,
      (GeneralCoveringSearch.program ids K.diameter a B q m).run G s v =
        (GeneralCoveringSearch.program ids L.diameter a B q m).run J s v := by
  induction m generalizing s with
  | zero =>
    intro v hv
    have haL : ∀ u, (s u).base.active = decide (u ∈ L.vertices) := by
      simpa only [← hvertices] using ha
    simp only [GeneralCoveringSearch.program, GeneralCoveringSearch.zero_run]
    rw [ActiveSearchCount.zero_correct G K B q (fun u => (s u).base.value) ids
      (fun u => (s u).base) ha (fun _ => rfl) v hv,
      ActiveSearchCount.zero_correct J L B q (fun u => (s u).base.value) ids
      (fun u => (s u).base) haL (fun _ => rfl) v (hvertices ▸ hv), ← hvertices]
  | succ m ih =>
    have haL : ∀ u, (s u).base.active = decide (u ∈ L.vertices) := by
      simpa only [← hvertices] using ha
    let ctrlG := GeneralCoveringSearch.control ids K.diameter a B q (m + 1)
    let ctrlJ := GeneralCoveringSearch.control ids L.diameter a B q (m + 1)
    have hc (v : V) (hv : v ∈ K.vertices) : ctrlG.run G s v = ctrlJ.run J s v := by
      dsimp only [ctrlG, ctrlJ]
      rw [GeneralCoveringSearch.control_run, GeneralCoveringSearch.control_run,
        ActiveSearchControl.result G K a B q (m + 1)
          (fun u => (s u).base.cost) (fun u => (s u).base.value) ids
          (fun u => (s u).base) ha (fun _ => rfl) (fun _ => rfl) v hv,
        ActiveSearchControl.result J L a B q (m + 1)
          (fun u => (s u).base.cost) (fun u => (s u).base.value) ids
          (fun u => (s u).base) haL (fun _ => rfl) (fun _ => rfl) v (hvertices ▸ hv),
        ← hvertices, initialList G J K.vertices
          (TerminalProtocolCorrect.demands K.vertices (fun u => (s u).base.value))
          (Finset.filter_subset _ _) hgraph a (m + 1)]
    have hs (j : ℕ) :
        GeneralCoveringLoop.childState G j (GeneralCoveringParent.initialState G ctrlG s) =
          GeneralCoveringLoop.childState J j (GeneralCoveringParent.initialState J ctrlJ s) := by
      funext u
      dsimp only [GeneralCoveringLoop.childState, GeneralCoveringLoop.childInput,
        GeneralCoveringParent.initialState]
      by_cases hu : u ∈ K.vertices
      · rw [hc u hu]
      · split <;> split <;> simp_all only [localUpdate_zero (s u) (hz u hu)]
    have hchild (j : ℕ) : ∀ v ∈ K.vertices,
        (GeneralCoveringSearch.program ids K.diameter a B q m).run G
          (GeneralCoveringLoop.childState G j (GeneralCoveringParent.initialState G ctrlG s)) v =
        (GeneralCoveringSearch.program ids L.diameter a B q m).run J
          (GeneralCoveringLoop.childState J j (GeneralCoveringParent.initialState J ctrlJ s)) v := by
      rw [← hs j]
      apply ih
      · intro u
        dsimp only [GeneralCoveringLoop.childState, GeneralCoveringLoop.childInput,
          GeneralCoveringParent.initialState]
        split <;> exact ha u
      · intro u hu
        dsimp only [GeneralCoveringLoop.childState, GeneralCoveringLoop.childInput,
          GeneralCoveringParent.initialState]
        split
        · exact hz u hu
        · change (s u).base.value.val - _ = 0
          simp only [hz u hu, Nat.zero_sub]
    intro v hv
    change (GeneralCoveringParent.program _ ctrlG _ _).run G s v =
      (GeneralCoveringParent.program _ ctrlJ _ _).run J s v
    rw [GeneralCoveringParent.run_program, GeneralCoveringParent.run_program]
    dsimp only
    rw [hc v hv]
    split
    · apply congrArg (BestWord.fold none)
      apply List.map_congr_left
      intro j _
      dsimp only [GeneralCoveringLoop.choice, GeneralCoveringParent.initialState]
      rw [hc v hv]
      exact congrArg (GeneralCoveringLoop.proposal _) (hchild j v hv)
    · rw [terminal G K ids B q _ (m + 1) s ha v hv,
        terminal J L ids B q _ (m + 1) s haL v (hvertices ▸ hv), ← hvertices]

end Paper.GeneralCoveringSearchInvariant

#print axioms Paper.GeneralCoveringSearchInvariant.initialList
#print axioms Paper.GeneralCoveringSearchInvariant.terminal
#print axioms Paper.GeneralCoveringSearchInvariant.localUpdate_zero
#print axioms Paper.GeneralCoveringSearchInvariant.run
