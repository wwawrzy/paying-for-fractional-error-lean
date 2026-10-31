import Paper.Averaging.Tasks.IntegralTaskSolver
import Paper.Solver.LocalSearch.ActiveRecursiveSearch

/-! Exact integral task compiler on arbitrary nonempty active connected
regions with a proved induced diameter. Geometry is proof-side data only;
the program takes a public diameter, active/demand bits and bounded costs. -/
namespace Paper.ActiveIntegralSolver
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def program {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) :
    Program V (FractionalSearch.Input V B) Bool :=
  .seq (FractionalSearch.program C diam a B 1 M)
    (.local fun _ _ n => decide (0 < n.val))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ)
    (s : V → FractionalSearch.Input V B) : Finset V :=
  Finset.univ.filter (fun v => (program C diam a B M).runEncoded G s v)

set_option maxHeartbeats 1000000 in
theorem against_cover (K : ActiveTask.Context G) (T : Finset V) (hT : T ⊆ K.vertices)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (c : V → Fin (B+1)) {bits : ℕ} (C : BitCode V bits)
    (s : V → FractionalSearch.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ T))
    (O : Finset V) (hOsub : O ⊆ K.vertices) (hO : T ⊆ covered G O) (hsizeO : O.card ≤ M) :
    output G C K.diameter a B M s ⊆ K.vertices ∧
      T ⊆ covered G (output G C K.diameter a B M s) ∧
      (∑ v ∈ output G C K.diameter a B M s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  let H := K.vertices
  let q : ℕ := 1
  let b := TaskBenchmark.demand (q := q) T
  let input := fun v => FractionalSearch.searchInput q (s v)
  let solver := RecursiveSearch.program C K.diameter a B q M
  have hai : ∀ v, (input v).active = decide (v ∈ H) := ha
  have hci : ∀ v, (input v).cost = c v := hc
  have hbi : ∀ v, (input v).value = b v := by
    intro v
    apply Fin.ext
    change (if (s v).demand then q else 0) = if v ∈ T then q else 0
    rw [hd v]
    change (if decide (v ∈ T) then q else 0) = if v ∈ T then q else 0
    by_cases hv : v ∈ T <;> simp [hv]
  have hz : ∀ v, v ∉ H → (b v).val = 0 :=
    TaskBenchmark.demand_outside H T hT
  have hspec := ActiveRecursiveSearch.correct G K a ha'
    hden B q c C M b input hai hci hbi hz
  let benchmark : V → ℕ := fun v => if v ∈ O then 1 else 0
  have hbenchsize : (∑ v, benchmark v) ≤ M := by simpa [benchmark] using hsizeO
  have hbenchsupport : ∀ v, v ∉ H → benchmark v = 0 := by
    intro v hv
    exact if_neg (fun ho => hv (hOsub ho))
  have hbenchcover : ∀ r, (b r).val ≤ ∑ v ∈ closed G r, benchmark v := by
    intro r
    change (if r ∈ T then 1 else 0) ≤ ∑ v ∈ closed G r, benchmark v
    by_cases hr : r ∈ T
    · obtain ⟨v,hv,hrv⟩ := Finset.mem_biUnion.mp (hO hr)
      have hh := Finset.single_le_sum (fun u _ => Nat.zero_le (benchmark u)) ((closed_symm G r v).mp hrv)
      simpa only [if_pos hr, benchmark, if_pos hv] using hh
    · simp only [if_neg hr, Nat.zero_le]
  obtain ⟨v0,hv0⟩ := K.nonempty
  obtain ⟨w, hw, hcostw⟩ := hspec.complete benchmark hbenchsize hbenchsupport hbenchcover v0 hv0
  have hvalid := hspec.sound v0 hv0 w hw
  have hrun : ∀ v ∈ H, solver.run G input v = some w :=
    fun v hv => (hspec.uniform v v0 hv hv0).trans hw
  have hcopies : ∀ v, ((FractionalSearch.program C K.diameter a B q M).run G s v).val = SolutionWord.copies w v := by
    intro v
    rw [FractionalSearch.run_program, ha v]
    by_cases hv : v ∈ H
    · simp only [show decide (v ∈ K.vertices) = true from decide_eq_true hv,
        ↓reduceIte]
      rw [hrun v hv]
      exact FractionalSearch.count_some w hvalid.1 v
    · have hzero := SearchSpec.copies_support G H c b M w hvalid v hv
      simp only [show decide (v ∈ K.vertices) = false from decide_eq_false hv,
        Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
      exact hzero.symm
  dsimp only [q] at hcopies
  have hout : output G C K.diameter a B M s = Finset.univ.filter (fun v => 0 < SolutionWord.copies w v) := by
    ext v
    simp only [output, Program.runEncoded_eq_run, program, Program.run, hcopies,
      Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  have hsupport : output G C K.diameter a B M s ⊆ H := by
    intro v hv
    have hp : 0 < SolutionWord.copies w v := by simpa only [hout,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    by_contra hn
    have hz := SearchSpec.copies_support G H c b M w hvalid v hn
    omega
  refine ⟨hsupport, ?_, ?_⟩
  · intro r hr
    have hh := hvalid.2.2.2 r
    change (if r ∈ T then 1 else 0) ≤ ∑ v ∈ closed G r, SolutionWord.copies w v at hh
    rw [if_pos hr] at hh
    obtain ⟨v,hv,hpos⟩ := Finset.sum_pos_iff.mp (show 0 < ∑ v ∈ closed G r, SolutionWord.copies w v by omega)
    exact Finset.mem_biUnion.mpr ⟨v, by rw [hout];exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos⟩,
      (closed_symm G v r).mp hv⟩
  · calc
      _ ≤ ∑ v ∈ output G C K.diameter a B M s, (c v).val * SolutionWord.copies w v := by
        apply Finset.sum_le_sum
        intro v hv
        have hp : 1 ≤ SolutionWord.copies w v := by
          have hh : 0 < SolutionWord.copies w v := by simpa only [hout,Finset.mem_filter,Finset.mem_univ,true_and] using hv
          omega
        exact Nat.le_mul_of_pos_right _ hp
      _ ≤ ∑ v, (c v).val * SolutionWord.copies w v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
      _ = SolutionWord.cost w := SolutionWord.cost_eq c w hvalid.2.2.1
      _ ≤ IntegralTable.cost (fun v => (c v).val) benchmark := hcostw
      _ = _ := by simp [IntegralTable.cost,benchmark,Finset.sum_filter]

/-- A bounded-cost feasible witness is used only in the proof. The same
program is optimal against every competing integral cover, without a
promise on the size of that competitor. -/
theorem optimal (K : ActiveTask.Context G) (T : Finset V) (hT : T ⊆ K.vertices)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (c : V → Fin (B+1)) (hpositive : ∀ v, 1 ≤ (c v).val)
    {bits : ℕ} (C : BitCode V bits) (s : V → FractionalSearch.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ T))
    (Z : Finset V) (hZsub : Z ⊆ K.vertices) (hZ : T ⊆ covered G Z)
    (hZcost : (∑ v ∈ Z, (c v).val) ≤ M)
    (O : Finset V) (hOsub : O ⊆ K.vertices) (hO : T ⊆ covered G O) :
    output G C K.diameter a B M s ⊆ K.vertices ∧
      T ⊆ covered G (output G C K.diameter a B M s) ∧
      (∑ v ∈ output G C K.diameter a B M s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  have card_le_cost (A : Finset V) : A.card ≤ ∑ v ∈ A, (c v).val := by
    calc
      _ = ∑ _v ∈ A, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hpositive v)
  by_cases hsmall : O.card ≤ M
  · exact against_cover G K T hT a ha' hden B M c C s ha hc hd O hOsub hO hsmall
  · have hs := against_cover G K T hT a ha' hden B M c C s ha hc hd Z hZsub hZ
      ((card_le_cost Z).trans hZcost)
    refine ⟨hs.1,hs.2.1,hs.2.2.trans ?_⟩
    have ho := card_le_cost O
    omega

theorem rounds {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) :
    (program C diam a B M).rounds = RecursiveSearch.roundBound diam a M := by
  simp only [program,Program.rounds,FractionalSearch.rounds,Nat.add_zero]

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (diam a B M n c : ℕ)
    (hids : bits ≤ c*Nat.clog 2 (n+2)) :
    (program C diam a B M).maxBits ≤
      (3*c+RecursiveSearch.extraBits diam a B 1 M)*Nat.clog 2 (n+2) := by
  have hl : 1 ≤ Nat.clog 2 (n+2) := Nat.clog_pos (by omega) (by omega)
  have hh := FractionalSearch.maxBits C diam a B 1 M
  have hc := Nat.mul_le_mul_left (RecursiveSearch.extraBits diam a B 1 M) hl
  simp only [program,Program.maxBits,Nat.max_zero]
  nlinarith

end Paper.ActiveIntegralSolver
