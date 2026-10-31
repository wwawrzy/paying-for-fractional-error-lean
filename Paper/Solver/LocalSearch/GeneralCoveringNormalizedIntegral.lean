import Paper.Solver.LocalSearch.GeneralCoveringInputNormalization
import Paper.Solver.LocalSearch.GeneralCoveringIntegral

/-! Literal demand-bit normalization followed by the accepted q=1 search.
The executable has only public natural parameters, an identifier codec and
private original inputs. An active context and one feasible cost-budget
witness certify correctness. Original positivity is needed only on original
admissible candidates and original row locality only on demanded rows.
Actual owner-task geometry and parallel task execution are separate. -/
namespace Paper.GeneralCoveringNormalizedIntegral
open BroadcastModel SevenFoundation
open scoped BigOperators
variable {V : Type} [LinearOrder V]

abbrev Input := GeneralCoveringFractional.Input
abbrev Covers (cover : V → Finset V) (R O : Finset V) : Prop :=
  GeneralCoveringIntegral.Covers cover R O

def program {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B) :
    Program V (Input V B) Bool :=
  .seq (GeneralCoveringInputNormalization.program B hB)
    (GeneralCoveringIntegral.program C diam a B M)

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_program {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    (program C diam a B M hB).runEncoded G s =
      (GeneralCoveringIntegral.program C diam a B M).runEncoded G
        ((GeneralCoveringInputNormalization.program B hB).runEncoded G s) := rfl

def output {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) : Finset V :=
  Finset.univ.filter (fun v => (program C diam a B M hB).runEncoded G s v)

theorem output_eq {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) :
    output G C diam a B M hB s =
      GeneralCoveringIntegral.output G C diam a B M
        ((GeneralCoveringInputNormalization.program B hB).runEncoded G s) := rfl

theorem mem_output {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B)
    (s : V → Input V B) (v : V) :
    v ∈ output G C diam a B M hB s ↔ (program C diam a B M hB).runEncoded G s v = true := by
  simp only [output, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Exact optimality for every original admissible integral cover. The only
budget witness is an actual feasible original cover Z of original cost <= M. -/
theorem optimal (K : ActiveTask.Context G) (R : Finset V) (hR : R ⊆ K.vertices)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (hlocal : ∀ r ∈ R, cover r ⊆ closed G r)
    (htask : ∀ r ∈ R, cover r ⊆ K.vertices)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (hB : 1 ≤ B) (c : V → Fin (B + 1))
    (hpositive : ∀ v ∈ CoveringSupport.admissible cover R, 1 ≤ (c v).val)
    {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hc : ∀ v, (s v).cost = c v) (hd : ∀ v, (s v).demand = decide (v ∈ R))
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v)
    (Z : Finset V) (hZadm : Z ⊆ CoveringSupport.admissible cover R) (hZ : Covers cover R Z)
    (hZcost : (∑ v ∈ Z, (c v).val) ≤ M) :
    output G C K.diameter a B M hB s ⊆ K.vertices ∧
      output G C K.diameter a B M hB s ⊆ CoveringSupport.admissible cover R ∧
      Covers cover R (output G C K.diameter a B M hB s) ∧
      ∀ O : Finset V, O ⊆ CoveringSupport.admissible cover R → Covers cover R O →
        (∑ v ∈ output G C K.diameter a B M hB s, (c v).val) ≤ ∑ v ∈ O, (c v).val := by
  let ns := (GeneralCoveringInputNormalization.program B hB).runEncoded G s
  let nc : V → Fin (B + 1) := fun v => (ns v).cost
  let rows : V → Finset V := fun r => (ns r).candidates
  let inverse : V → Finset V := fun v => (ns v).targets
  let out := GeneralCoveringIntegral.output G C K.diameter a B M ns
  have hninc : ∀ v r, r ∈ inverse v ↔ v ∈ rows r := by
    intro v r
    exact GeneralCoveringInputNormalization.agreement G cover targets R hinc hlocal hB s hd hC ht v r
  have hnlocal : ∀ r ∈ K.vertices, rows r ⊆ closed G r := by
    intro r _
    exact GeneralCoveringInputNormalization.locality G cover R hlocal hB s hd hC r
  have hnrows : ∀ r ∈ R, rows r = cover r := by
    intro r hr
    calc
      rows r = GeneralCoveringInputNormalization.trimmed cover R r :=
        GeneralCoveringInputNormalization.candidates_eq G cover R hB s hd hC r
      _ = cover r := if_pos hr
  have hntask : ∀ r ∈ R, rows r ⊆ K.vertices := by
    intro r hr
    rw [hnrows r hr]
    exact htask r hr
  have hnpositive : ∀ v, 1 ≤ (nc v).val := by
    intro v
    exact GeneralCoveringInputNormalization.positive G cover targets R hinc hlocal s hd ht hB
      (fun u hu => by rw [hc u]; exact hpositive u hu) v
  have hnactive : ∀ v, (ns v).active = decide (v ∈ K.vertices) := by
    intro v
    exact (GeneralCoveringInputNormalization.metadata G B hB s v).1.trans (ha v)
  have hndemand : ∀ v, (ns v).demand = decide (v ∈ R) := by
    intro v
    exact (GeneralCoveringInputNormalization.metadata G B hB s v).2.trans (hd v)
  have hnadm : CoveringSupport.admissible rows R = CoveringSupport.admissible cover R :=
    GeneralCoveringInputNormalization.admissibility G cover R hB s hd hC
  have hncovers (O : Finset V) : Covers rows R O ↔ Covers cover R O :=
    GeneralCoveringInputNormalization.integral_covers G cover R hB s hd hC O
  have hncost (A : Finset V) (hA : A ⊆ CoveringSupport.admissible cover R) :
      (∑ v ∈ A, (nc v).val) = ∑ v ∈ A, (c v).val := by
    calc
      _ = ∑ v ∈ A, (s v).cost.val :=
        GeneralCoveringInputNormalization.supported_cost G cover targets R hinc hlocal s hd ht hB A hA
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _
        rw [hc v]
  have hnZadm : Z ⊆ CoveringSupport.admissible rows R := by
    rw [hnadm]
    exact hZadm
  have hnZcost : (∑ v ∈ Z, (nc v).val) ≤ M := by
    rw [hncost Z hZadm]
    exact hZcost
  have hs (O : Finset V) (hOadm : O ⊆ CoveringSupport.admissible cover R) (hO : Covers cover R O) :=
    GeneralCoveringIntegral.optimal G K R hR rows inverse hninc hnlocal hntask a ha' hden B M nc hnpositive
      C ns hnactive (fun _ => rfl) hndemand (fun _ => rfl) (fun _ => rfl)
      Z hnZadm ((hncovers Z).mpr hZ) hnZcost O (by rw [hnadm]; exact hOadm) ((hncovers O).mpr hO)
  have hbase := hs Z hZadm hZ
  have hadm : out ⊆ CoveringSupport.admissible cover R := by
    rw [← hnadm]
    exact hbase.2.1
  have hcover : Covers cover R out := (hncovers out).mp hbase.2.2.1
  rw [output_eq]
  refine ⟨hbase.1, hadm, hcover, ?_⟩
  intro O hOadm hO
  calc
    (∑ v ∈ out, (c v).val) = ∑ v ∈ out, (nc v).val := (hncost out hadm).symm
    _ ≤ ∑ v ∈ O, (nc v).val := (hs O hOadm hO).2.2.2
    _ = ∑ v ∈ O, (c v).val := hncost O hOadm

/-- Empty demand needs neither original positive costs nor original row locality. -/
theorem empty_demand (K : ActiveTask.Context G)
    (cover targets : V → Finset V) (hinc : ∀ v r, r ∈ targets v ↔ v ∈ cover r)
    (a : ℕ) (ha' : 1 ≤ a) (hden : Incidence.InducedDensityBound G (a : ℝ))
    (B M : ℕ) (hB : 1 ≤ B) {bits : ℕ} (C : BitCode V bits) (s : V → Input V B)
    (ha : ∀ v, (s v).active = decide (v ∈ K.vertices))
    (hd : ∀ v, (s v).demand = false)
    (hC : ∀ v, (s v).candidates = cover v) (ht : ∀ v, (s v).targets = targets v) :
    output G C K.diameter a B M hB s = ∅ ∧
      ∀ v, (program C K.diameter a B M hB).runEncoded G s v = false := by
  have h := optimal G K ∅ (by simp) cover targets hinc (by simp) (by simp) a ha' hden
    B M hB (fun v => (s v).cost) (by simp [CoveringSupport.admissible]) C s ha (fun _ => rfl)
    (by intro v; simpa using hd v) hC ht ∅ (by simp) (by simp [Covers, GeneralCoveringIntegral.Covers]) (by simp)
  have hs : output G C K.diameter a B M hB s ⊆ (∅ : Finset V) := by
    simpa only [CoveringSupport.admissible, Finset.biUnion_empty] using h.2.1
  have hout : output G C K.diameter a B M hB s = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (hs hv))
  refine ⟨hout, ?_⟩
  intro v
  cases hflag : (program C K.diameter a B M hB).runEncoded G s v with
  | false => rfl
  | true =>
    exfalso
    have hm := (mem_output G C K.diameter a B M hB s v).mpr hflag
    exact Finset.notMem_empty v (hout ▸ hm)

theorem rounds_eq {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B) :
    (program C diam a B M hB).rounds = (GeneralCoveringIntegral.program C diam a B M).rounds + 1 := by
  change 1 + (GeneralCoveringIntegral.program C diam a B M).rounds = _
  exact Nat.add_comm _ _

theorem rounds {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B) :
    (program C diam a B M hB).rounds = RecursiveSearch.roundBound diam a M + 1 := by
  rw [rounds_eq, GeneralCoveringIntegral.rounds]

theorem maxBits_eq {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B) :
    (program C diam a B M hB).maxBits = max 1 (GeneralCoveringIntegral.program C diam a B M).maxBits := rfl

theorem maxBits {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B) :
    (program C diam a B M hB).maxBits ≤ max 1 (3 * bits + RecursiveSearch.extraBits diam a B 1 M) := by
  rw [maxBits_eq]
  exact max_le_max (le_refl 1) (GeneralCoveringIntegral.maxBits C diam a B M)

theorem logarithmic_bits {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B)
    (n c : ℕ) (hids : bits ≤ c * Nat.clog 2 (n + 2)) :
    (program C diam a B M hB).maxBits ≤
      (3 * c + RecursiveSearch.extraBits diam a B 1 M + 1) * Nat.clog 2 (n + 2) := by
  have hlog : 1 ≤ Nat.clog 2 (n + 2) := Nat.clog_pos (by omega) (by omega)
  have hcoef : 1 ≤ 3 * c + RecursiveSearch.extraBits diam a B 1 M + 1 := by omega
  have hold := GeneralCoveringIntegral.logarithmic_bits C diam a B M n c hids
  rw [maxBits_eq]
  apply max_le
  · exact Nat.mul_le_mul hcoef hlog
  · exact hold.trans (Nat.mul_le_mul (Nat.le_succ _) (le_refl _))

theorem locality {bits : ℕ} (C : BitCode V bits) (diam a B M : ℕ) (hB : 1 ≤ B)
    (N N' : V → Finset V) (s s' : V → Input V B) (v : V)
    (hn : ∀ u ∈ NeighborBalls.ball N v (RecursiveSearch.roundBound diam a M + 1), N u = N' u)
    (hs : ∀ u ∈ NeighborBalls.ball N v (RecursiveSearch.roundBound diam a M + 1), s u = s' u) :
    NeighborInterpreter.run N (program C diam a B M hB) s v =
      NeighborInterpreter.run N' (program C diam a B M hB) s' v := by
  apply NeighborLocality.locality (program C diam a B M hB) N N' s s' v
  · simpa only [rounds C diam a B M hB] using hn
  · simpa only [rounds C diam a B M hB] using hs
end Paper.GeneralCoveringNormalizedIntegral

#print axioms Paper.GeneralCoveringNormalizedIntegral.run_program
#print axioms Paper.GeneralCoveringNormalizedIntegral.optimal
#print axioms Paper.GeneralCoveringNormalizedIntegral.empty_demand
#print axioms Paper.GeneralCoveringNormalizedIntegral.rounds_eq
#print axioms Paper.GeneralCoveringNormalizedIntegral.rounds
#print axioms Paper.GeneralCoveringNormalizedIntegral.maxBits_eq
#print axioms Paper.GeneralCoveringNormalizedIntegral.maxBits
#print axioms Paper.GeneralCoveringNormalizedIntegral.logarithmic_bits
#print axioms Paper.GeneralCoveringNormalizedIntegral.locality
