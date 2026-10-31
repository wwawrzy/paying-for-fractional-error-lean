import Paper.Endpoints.Components.SmallComponentProgram

/-! Correctness of both output flags of the actual small-component decoder.
These local facts alone do not establish exact-search or covering correctness. -/
namespace Paper.SmallComponentDecode

theorem decode_solved_iff
    {V : Type} [LinearOrder V] {B : Nat} (K : Nat) (v : V)
    (s : Option (Paper.SolutionWord.Word V B) × Bool) :
    (Paper.SmallComponentProgram.decode K v s).1 = true ↔
      s.2 = true ∧ ∃ w : Paper.SolutionWord.Word V B,
        s.1 = some w ∧ Paper.SolutionWord.cost w ≤ K := by
  rcases s with ⟨wo, accept⟩
  cases accept
  · simp [Paper.SmallComponentProgram.decode]
  · cases wo with
    | none => simp [Paper.SmallComponentProgram.decode]
    | some w =>
      by_cases h : Paper.SolutionWord.cost w ≤ K <;>
        simp [Paper.SmallComponentProgram.decode, h]

theorem decode_selected_iff
    {V : Type} [LinearOrder V] {B : Nat} (K : Nat) (v : V)
    (s : Option (Paper.SolutionWord.Word V B) × Bool) :
    (Paper.SmallComponentProgram.decode K v s).2 = true ↔
      s.2 = true ∧ ∃ w : Paper.SolutionWord.Word V B,
        s.1 = some w ∧ Paper.SolutionWord.cost w ≤ K ∧
          0 < Paper.SolutionWord.copies w v := by
  rcases s with ⟨wo, accept⟩
  cases accept
  · simp [Paper.SmallComponentProgram.decode]
  · cases wo with
    | none => simp [Paper.SmallComponentProgram.decode]
    | some w =>
      by_cases h : Paper.SolutionWord.cost w ≤ K <;>
        simp [Paper.SmallComponentProgram.decode, h]

theorem selected_implies_solved
    {V : Type} [LinearOrder V] {B : Nat} (K : Nat) (v : V)
    (s : Option (Paper.SolutionWord.Word V B) × Bool)
    (h : (Paper.SmallComponentProgram.decode K v s).2 = true) :
    (Paper.SmallComponentProgram.decode K v s).1 = true := by
  obtain ⟨ha, w, hw, hc, _⟩ := (decode_selected_iff K v s).mp h
  exact (decode_solved_iff K v s).mpr ⟨ha, w, hw, hc⟩

end Paper.SmallComponentDecode

#print axioms Paper.SmallComponentDecode.decode_solved_iff
#print axioms Paper.SmallComponentDecode.decode_selected_iff
#print axioms Paper.SmallComponentDecode.selected_implies_solved
