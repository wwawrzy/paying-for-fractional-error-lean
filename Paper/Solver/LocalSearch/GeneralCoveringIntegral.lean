import Paper.Solver.LocalSearch.GeneralCoveringFractional
import Paper.Communication.EncodedProgram
import Paper.Certificates.Counting.CoveringSupport
import Paper.Preliminaries.NeighborLocality

/-! Exact integral arbitrary-C search on an explicit active task.
The runtime uses public diam,a,B,M and private active/demand bits, bounded
costs and the two true incidence lists. It runs the received fractional
program with q=1 and returns only the sender's own positive-copy Bool.
Geometry and a feasible cost-budget witness occur only in correctness proofs.
The inherited interface is explicit: all active rows are physically local,
both incidence lists agree everywhere, and all bounded vertex costs are >=1.
No admissible-only cost extension or dummy-cost invariance is asserted. -/
namespace Paper.GeneralCoveringIntegral
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input

def Covers (cover : V → Finset V) (R O : Finset V) : Prop :=
  ∀ r ∈ R, ∃ v ∈ O, v ∈ cover r

def program {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) : Program V (Input V B) Bool :=
  .seq (GeneralCoveringFractional.program C diam a B 1 M)
    (.local fun _ _ n => decide (0 < n.val))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def output {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => (program C diam a B M).runEncoded G s v)

theorem mem_output {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (s : V → Input V B) (v : V) :
    v ∈ output G C diam a B M s ↔ (program C diam a B M).runEncoded G s v = true := by
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and]

theorem admissible_subset (cover : V → Finset V) (R H : Finset V)
    (h : ∀ r ∈ R, cover r ⊆ H) : CoveringSupport.admissible cover R ⊆ H := by
  intro v hv
  obtain ⟨r, hr, hvr⟩ := Finset.mem_biUnion.mp hv
  exact h r hr hvr

/-- A bounded integral competitor supplies an actual search completion.
Positive global bounded costs additionally force the returned support to be C-admissible. -/
theorem against_cover (K : ActiveTask.Context G) (R : Finset V) (hR : R ⊆ K.vertices)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ K.vertices, cover r ⊆ closed G r)
    (htask : ∀ r ∈ R, cover r ⊆ K.vertices)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (c : V → Fin (B + 1)) (hpositive : ∀ v, 1 ≤ (c v).val)
    {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (htarget : ∀ v, (s v).targets = targets v)
    (O : Finset V) (hOadm : O ⊆ CoveringSupport.admissible cover R)
    (hO : Covers cover R O) (hsizeO : O.card ≤ M) :
    output G C K.diameter a B M s ⊆ K.vertices ∧
      output G C K.diameter a B M s ⊆ CoveringSupport.admissible cover R ∧
      Covers cover R (output G C K.diameter a B M s) ∧
      (∑ v ∈ output G C K.diameter a B M s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  let H := K.vertices
  let q : ℕ := 1
  let b := TaskBenchmark.demand (q := q) R
  let input := fun v => GeneralCoveringFractional.searchInput q (s v)
  let solver := GeneralCoveringSearch.program C K.diameter a B q M
  have hai : ∀ v, (input v).base.active = decide (v ∈ H) := ha
  have hci : ∀ v, (input v).base.cost = c v := hc
  have hbi : ∀ v, (input v).base.value = b v := by
    intro v
    apply Fin.ext
    change (if (s v).demand then q else 0) = if v ∈ R then q else 0
    rw [hd v]
    by_cases hv : v ∈ R <;> simp [hv]
  have hz : ∀ v, v ∉ H → (b v).val = 0 := TaskBenchmark.demand_outside H R hR
  have hspec := GeneralCoveringSearch.correct G K cover targets hinc hlocal a ha' hden B q c C M b input
    hai hci hbi hz hC htarget
  have hOsub : O ⊆ H := hOadm.trans (admissible_subset cover R H htask)
  let benchmark : V → ℕ := fun v => if v ∈ O then 1 else 0
  have hbenchsize : (∑ v, benchmark v) ≤ M := by simpa [benchmark] using hsizeO
  have hbenchsupport : ∀ v, v ∉ H → benchmark v = 0 := by
    intro v hv
    exact if_neg (fun ho => hv (hOsub ho))
  have hbenchcover : ∀ r, (b r).val ≤ ∑ v ∈ cover r, benchmark v := by
    intro r
    change (if r ∈ R then 1 else 0) ≤ ∑ v ∈ cover r, benchmark v
    by_cases hr : r ∈ R
    · obtain ⟨v, hvO, hvr⟩ := hO r hr
      have hh := Finset.single_le_sum (fun u _ => Nat.zero_le (benchmark u)) hvr
      simpa only [if_pos hr, benchmark, if_pos hvO] using hh
    · simp only [if_neg hr, Nat.zero_le]
  obtain ⟨v0, hv0⟩ := K.nonempty
  obtain ⟨w, hw, hcostw⟩ := hspec.complete benchmark hbenchsize hbenchsupport hbenchcover v0 hv0
  have hvalid := hspec.sound v0 hv0 w hw
  have hrun : ∀ v ∈ H, solver.run G input v = some w :=
    fun v hv => (hspec.uniform v v0 hv hv0).trans hw
  have hcopies : ∀ v, ((GeneralCoveringFractional.program C K.diameter a B q M).run G s v).val =
      SolutionWord.copies w v := by
    intro v
    rw [GeneralCoveringFractional.run_program, ha v]
    by_cases hv : v ∈ H
    · simp only [show decide (v ∈ K.vertices) = true from decide_eq_true hv,
        ↓reduceIte]
      rw [hrun v hv]
      exact GeneralCoveringFractional.count_some w hvalid.1 v
    · have hzero := GeneralCoveringSpec.copies_support cover H c b M w hvalid v hv
      simp only [show decide (v ∈ K.vertices) = false from decide_eq_false hv,
        Bool.false_eq_true, ↓reduceIte, Fin.val_zero]
      exact hzero.symm
  dsimp only [q] at hcopies
  have hout : output G C K.diameter a B M s = Finset.univ.filter (fun v => 0 < SolutionWord.copies w v) := by
    ext v
    simp only [output, Program.runEncoded_eq_run, program, Program.run, hcopies,
      Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  have hpos (v : V) (hv : v ∈ output G C K.diameter a B M s) : 0 < SolutionWord.copies w v := by
    simpa only [hout, Finset.mem_filter, Finset.mem_univ, true_and] using hv
  have hsupport : output G C K.diameter a B M s ⊆ H := by
    intro v hv
    by_contra hn
    have hzero := GeneralCoveringSpec.copies_support cover H c b M w hvalid v hn
    have hp := hpos v hv
    omega
  have hadmissible : output G C K.diameter a B M s ⊆ CoveringSupport.admissible cover R := by
    intro v hv
    obtain ⟨r, hr, hvr⟩ := GeneralCoveringSpec.used_is_admissible cover G solver H c b M input hspec
      (fun u => lt_of_lt_of_le Nat.zero_lt_one (hpositive u)) v0 hv0 w hw v (hpos v hv)
    have hrR : r ∈ R := by
      by_contra hn
      change 0 < (if r ∈ R then 1 else 0) at hr
      rw [if_neg hn] at hr
      omega
    exact Finset.mem_biUnion.mpr ⟨r, hrR, hvr⟩
  refine ⟨hsupport, hadmissible, ?_, ?_⟩
  · intro r hr
    have hh := hvalid.2.2.2 r
    change (if r ∈ R then 1 else 0) ≤ ∑ v ∈ cover r, SolutionWord.copies w v at hh
    rw [if_pos hr] at hh
    obtain ⟨v, hvr, hp⟩ := Finset.sum_pos_iff.mp
      (show 0 < ∑ v ∈ cover r, SolutionWord.copies w v by omega)
    exact ⟨v, by rw [hout]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hp⟩, hvr⟩
  · calc
      _ ≤ ∑ v ∈ output G C K.diameter a B M s, (c v).val * SolutionWord.copies w v := by
        apply Finset.sum_le_sum
        intro v hv
        exact Nat.le_mul_of_pos_right _ (by have hp := hpos v hv; omega)
      _ ≤ ∑ v, (c v).val * SolutionWord.copies w v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; exact Nat.zero_le _)
      _ = SolutionWord.cost w := SolutionWord.cost_eq c w hvalid.2.2.1
      _ ≤ IntegralTable.cost (fun v => (c v).val) benchmark := hcostw
      _ = _ := by simp [IntegralTable.cost, benchmark, Finset.sum_filter]

/-- One feasible admissible cost-budget witness suffices for comparison with
every admissible integral C-cover, with no cardinality bound on that competitor. -/
theorem optimal (K : ActiveTask.Context G) (R : Finset V) (hR : R ⊆ K.vertices)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ K.vertices, cover r ⊆ closed G r)
    (htask : ∀ r ∈ R, cover r ⊆ K.vertices)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (c : V → Fin (B + 1)) (hpositive : ∀ v, 1 ≤ (c v).val)
    {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (htarget : ∀ v, (s v).targets = targets v)
    (Z : Finset V) (hZadm : Z ⊆ CoveringSupport.admissible cover R) (hZ : Covers cover R Z)
    (hZcost : (∑ v ∈ Z, (c v).val) ≤ M)
    (O : Finset V) (hOadm : O ⊆ CoveringSupport.admissible cover R) (hO : Covers cover R O) :
    output G C K.diameter a B M s ⊆ K.vertices ∧
      output G C K.diameter a B M s ⊆ CoveringSupport.admissible cover R ∧
      Covers cover R (output G C K.diameter a B M s) ∧
      (∑ v ∈ output G C K.diameter a B M s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  have card_le_cost (A : Finset V) : A.card ≤ ∑ v ∈ A, (c v).val := by
    calc
      _ = ∑ _v ∈ A, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hpositive v)
  by_cases hsmall : O.card ≤ M
  · exact against_cover G K R hR cover targets hinc hlocal htask a ha' hden B M c hpositive C s
      ha hc hd hC htarget O hOadm hO hsmall
  · have hs := against_cover G K R hR cover targets hinc hlocal htask a ha' hden B M c hpositive C s
      ha hc hd hC htarget Z hZadm hZ ((card_le_cost Z).trans hZcost)
    refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.trans ?_⟩
    have ho := card_le_cost O
    omega

theorem empty_demand (K : ActiveTask.Context G)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ K.vertices, cover r ⊆ closed G r)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (c : V → Fin (B + 1)) (hpositive : ∀ v, 1 ≤ (c v).val)
    {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = false)
    (hC : ∀ v, (s v).candidates = cover v) (htarget : ∀ v, (s v).targets = targets v) :
    output G C K.diameter a B M s = ∅ ∧
      ∀ v, (program C K.diameter a B M).runEncoded G s v = false := by
  have h := against_cover G K ∅ (by simp) cover targets hinc hlocal (by simp) a ha' hden B M c hpositive C s
    ha hc (by intro v; simpa using hd v) hC htarget ∅ (by simp)
    (by intro r hr; exact False.elim (Finset.notMem_empty r hr)) (by simp)
  have hs : output G C K.diameter a B M s ⊆ (∅ : Finset V) := by
    simpa only [CoveringSupport.admissible, Finset.biUnion_empty] using h.2.1
  have hout : output G C K.diameter a B M s = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (hs hv))
  refine ⟨hout, ?_⟩
  intro v
  cases hflag : (program C K.diameter a B M).runEncoded G s v with
  | false => rfl
  | true =>
    exfalso
    have hm := (mem_output G C K.diameter a B M s v).mpr hflag
    exact Finset.notMem_empty v (hout ▸ hm)

theorem rounds {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) :
    (program C diam a B M).rounds = RecursiveSearch.roundBound diam a M := by
  simp only [program, Program.rounds, GeneralCoveringFractional.rounds, Nat.add_zero]

theorem maxBits {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) :
    (program C diam a B M).maxBits ≤ 3 * bits + RecursiveSearch.extraBits diam a B 1 M := by
  simpa only [program, Program.maxBits, Nat.max_zero] using
    GeneralCoveringFractional.maxBits C diam a B 1 M

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (diam a B M n c : ℕ)
    (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C diam a B M).maxBits ≤
      (3 * c + RecursiveSearch.extraBits diam a B 1 M) * Nat.clog 2 (n + 2) := by
  simpa only [program, Program.maxBits, Nat.max_zero] using
    GeneralCoveringFractional.logarithmic_bits C diam a B 1 M n c hids

/-- Exact dependency-ball locality of the literal program, with the proved round radius. -/
theorem locality {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ)
    (N N' : V → Finset V) (s s' : V → Input V B) (v : V)
    (hn : ∀ u ∈ NeighborBalls.ball N v (RecursiveSearch.roundBound diam a M), N u = N' u)
    (hs : ∀ u ∈ NeighborBalls.ball N v (RecursiveSearch.roundBound diam a M), s u = s' u) :
    NeighborInterpreter.run N (program C diam a B M) s v =
      NeighborInterpreter.run N' (program C diam a B M) s' v := by
  apply NeighborLocality.locality (program C diam a B M) N N' s s' v
  · simpa only [rounds C diam a B M] using hn
  · simpa only [rounds C diam a B M] using hs

end Paper.GeneralCoveringIntegral

#print axioms Paper.GeneralCoveringIntegral.against_cover
#print axioms Paper.GeneralCoveringIntegral.optimal
#print axioms Paper.GeneralCoveringIntegral.empty_demand
#print axioms Paper.GeneralCoveringIntegral.rounds
#print axioms Paper.GeneralCoveringIntegral.logarithmic_bits
#print axioms Paper.GeneralCoveringIntegral.locality
