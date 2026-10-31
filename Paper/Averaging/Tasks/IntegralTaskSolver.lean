import Paper.Solver.LocalSearch.FractionalSearchCorrect
import Paper.Communication.EncodedProgram

/-! Exact weighted integral solution of every connected physical owner task.
Only active/demand bits and own bounded cost are private inputs. Integer
certificates and competing covers occur solely in the correctness proof. -/
namespace Paper.IntegralTaskSolver
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

def program {bits : ℕ} (C : BitCode V bits) (k a B M : ℕ) :
    Program V (FractionalSearch.Input V B) Bool :=
  .seq (FractionalSearch.program C (4*k) a B 1 M)
    (.local fun _ _ n => decide (0 < n.val))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {bits : ℕ} (C : BitCode V bits) (k a B M : ℕ)
    (s : V → FractionalSearch.Input V B) : Finset V :=
  Finset.univ.filter (fun v => (program C k a B M).runEncoded G s v)

set_option maxHeartbeats 1000000 in
theorem against_cover (D R : Finset V) (L : ℕ) (Q : Finset D) (I J : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (a : ℕ) (ha' : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G (a : ℝ)) (B M : ℕ) (c : V → Fin (B+1))
    {bits : ℕ} (C : BitCode V bits) (s : V → FractionalSearch.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v).cost = c v)
    (hd : ∀ v, (s v).demand = decide (v ∈ OwnerTasks.demands G D R L Q I J))
    (O : Finset V) (hOsub : O ⊆ PhysicalTasks.vertices G D R L Q I)
    (hO : OwnerTasks.demands G D R L Q I J ⊆ covered G O) (hsizeO : O.card ≤ M) :
    output G C k a B M s ⊆ PhysicalTasks.vertices G D R L Q I ∧
      OwnerTasks.demands G D R L Q I J ⊆ covered G (output G C k a B M s) ∧
      (∑ v ∈ output G C k a B M s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  let H := PhysicalTasks.vertices G D R L Q I
  let T := OwnerTasks.demands G D R L Q I J
  let q : ℕ := 1
  let b := TaskBenchmark.demand (q := q) T
  let input := fun v => FractionalSearch.searchInput q (s v)
  let solver := RecursiveSearch.program C (4 * k) a B q M
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
    TaskBenchmark.demand_outside H T (PhysicalTasks.demands_subset G D R L Q I J)
  have hspec := RecursiveSearchCorrect.correct G D R L Q I hI k hsize a ha'
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
  obtain ⟨i⟩ := hI.nonempty
  let v0 := i.val.val.val
  have hv0 : v0 ∈ H := PhysicalTasks.root_mem G D R L Q I i.val i.property
  obtain ⟨w, hw, hcostw⟩ := hspec.complete benchmark hbenchsize hbenchsupport hbenchcover v0 hv0
  have hvalid := hspec.sound v0 hv0 w hw
  have hrun : ∀ v ∈ H, solver.run G input v = some w :=
    fun v hv => (hspec.uniform v v0 hv hv0).trans hw
  have hcopies : ∀ v, ((FractionalSearch.program C (4 * k) a B q M).run G s v).val = SolutionWord.copies w v := by
    intro v
    rw [FractionalSearch.run_program, ha v]
    by_cases hv : v ∈ H
    · simp only [show decide (v ∈ PhysicalTasks.vertices G D R L Q I) = true from decide_eq_true hv,
        ↓reduceIte]
      rw [hrun v hv]
      exact FractionalSearch.count_some w hvalid.1 v
    · have hzero := SearchSpec.copies_support G H c b M w hvalid v hv
      simp only [show decide (v ∈ PhysicalTasks.vertices G D R L Q I) = false from decide_eq_false hv,
        Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
      exact hzero.symm
  dsimp only [q] at hcopies
  have hout : output G C k a B M s = Finset.univ.filter (fun v => 0 < SolutionWord.copies w v) := by
    ext v
    simp only [output, Program.runEncoded_eq_run, program, Program.run, hcopies,
      Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  have hsupport : output G C k a B M s ⊆ H := by
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
      _ ≤ ∑ v ∈ output G C k a B M s, (c v).val * SolutionWord.copies w v := by
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

/-- Public budget B*k suffices for exact integral optimization, even when a
competing cover contains arbitrarily many candidates. -/
theorem optimal (D R : Finset V) (L : ℕ) (Q : Finset D) (I J : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (a : ℕ) (ha' : 1 ≤ a)
    (hden : Incidence.InducedDensityBound G (a : ℝ)) (B : ℕ) (hB : 1 ≤ B)
    (c : V → Fin (B+1)) (hpositive : ∀ v, 1 ≤ (c v).val)
    {bits : ℕ} (C : BitCode V bits) (s : V → FractionalSearch.Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ PhysicalTasks.vertices G D R L Q I))
    (hc : ∀ v, (s v).cost = c v)
    (hd : ∀ v, (s v).demand = decide (v ∈ OwnerTasks.demands G D R L Q I J))
    (O : Finset V) (hOsub : O ⊆ PhysicalTasks.vertices G D R L Q I)
    (hO : OwnerTasks.demands G D R L Q I J ⊆ covered G O) :
    output G C k a B (B*k) s ⊆ PhysicalTasks.vertices G D R L Q I ∧
      OwnerTasks.demands G D R L Q I J ⊆ covered G (output G C k a B (B*k) s) ∧
      (∑ v ∈ output G C k a B (B*k) s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  have hoc := @PhysicalTasks.owner_cover V (inferInstance : Fintype V) (inferInstance : LinearOrder V)
  have hinst : Classical.decEq V = (inferInstance : DecidableEq V) := Subsingleton.elim _ _
  rw [hinst] at hoc
  by_cases hsmall : O.card ≤ B*k
  · exact against_cover G D R L Q I J hI k hsize a ha' hden B (B*k) c C s ha hc hd O hOsub hO hsmall
  · let Z := PhysicalTasks.centers D Q I
    have hZsub : Z ⊆ PhysicalTasks.vertices G D R L Q I := by
      intro v hv
      have hv' : ∃ i ∈ I, i.val.val = v := by
        simpa only [Z,PhysicalTasks.centers,Finset.mem_image] using hv
      obtain ⟨i,hi,rfl⟩ := hv'
      exact PhysicalTasks.root_mem G D R L Q I i hi
    have hZsize : Z.card ≤ B*k := by
      have he : Z.card = I.card := PhysicalTasks.centers_card D Q I
      have hh := Nat.mul_le_mul_right k hB
      omega
    have hs := against_cover G D R L Q I J hI k hsize a ha' hden B (B*k) c C s ha hc hd Z hZsub
      (hoc G D R L Q I J) hZsize
    refine ⟨hs.1,hs.2.1,hs.2.2.trans ?_⟩
    have hb : (∑ v ∈ Z, (c v).val) ≤ B*k := by
      calc
        _ ≤ ∑ _v ∈ Z, B := Finset.sum_le_sum (fun v _ => by have hh := (c v).isLt;omega)
        _ = Z.card*B := by simp
        _ ≤ B*k := by rw [PhysicalTasks.centers_card D Q I];nlinarith
    have ho : O.card ≤ ∑ v ∈ O, (c v).val := by
      calc
        _ = ∑ _v ∈ O, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun v _ => hpositive v)
    omega

theorem rounds {bits : ℕ} (C : BitCode V bits) (k a B M : ℕ) :
    (program C k a B M).rounds = RecursiveSearch.roundBound (4*k) a M := by
  simp only [program,Program.rounds,FractionalSearch.rounds,Nat.add_zero]

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (k a B M n c : ℕ)
    (hids : bits ≤ c*Nat.clog 2 (n+2)) :
    (program C k a B M).maxBits ≤
      (3*c+RecursiveSearch.extraBits (4*k) a B 1 M)*Nat.clog 2 (n+2) := by
  simpa only [program,Program.maxBits,Nat.max_zero] using
    FractionalSearch.logarithmic_bits C k a B 1 M n c hids

end Paper.IntegralTaskSolver
