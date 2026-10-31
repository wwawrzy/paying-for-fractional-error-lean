import Paper.Solver.LocalSearch.GeneralCoveringInitializedRandomIntegral
import Paper.Solver.LocalSearch.GeneralCoveringDeterministicApproximation

/-! Finite uniform expected approximation by the UNCHANGED actual initialized
random integral program. Only numeric initializer/scalar lemmas are reused
from deterministic approximation. All coins stay on PUBLIC vertices; the
prepared centers/owner graph are independent of beta. No desired mean,
private-Low law, benchmark cardinal bound or computed field is an input. -/
namespace Paper.GeneralCoveringRandomIntegralApproximation
open BroadcastModel SevenFoundation
open scoped BigOperators
open GeneralCoveringDeterministicApproximation
  (Initialization initialization_exists error_budgets count_budget additive_to_approximation)

structure Parameters (a : ℕ) where
  init : Initialization a
  L : ℕ
  Δ : ℕ
  η : ℝ
  t : ℕ
  k : ℕ
  b : ℕ
  n : ℕ
  ht : 0 < t
  hk : 0 < k
  hη : 0 < η

abbrev Coins := GeneralCoveringInitializedRandomIntegral.Coins
abbrev Private (V : Type) (B : ℕ) := GeneralCoveringInitializerRun.Input V × Fin (B + 1)
abbrev Source (V : Type) {a : ℕ} (q : Parameters a) := V → Coins q.Δ q.k q.b q.n

def input {V : Type} {B Δ k b n : ℕ} (x : V → Private V B) (β : V → Coins Δ k b n) :
    V → GeneralCoveringInitializedRandomIntegral.Input V B Δ k b n :=
  fun v => ((x v).1, ((x v).2, β v))

abbrev program {V : Type} [LinearOrder V] {bits : ℕ} (ids : BitCode V bits)
    (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B) :=
  GeneralCoveringInitializedRandomIntegral.program ids q.init.b q.init.h q.init.f q.init.U
    q.L q.Δ a q.k q.t q.b q.n B hB

/-- Exactly all independent Boolean coordinates, with no sampling conversion. -/
def sourceEquiv (V : Type) {a : ℕ} (q : Parameters a) :
    Source V q ≃ ((V × (CurrentFiniteBitPartition.Index q.Δ q.k q.n × Fin q.b)) → Bool) where
  toFun β p := β p.1 p.2.1 p.2.2
  invFun ω v i j := ω (v, (i, j))
  left_inv β := by funext v i j; rfl
  right_inv ω := by funext p; rcases p with ⟨v, i, j⟩; rfl

theorem source_card (V : Type) [Fintype V] [DecidableEq V] {a : ℕ} (q : Parameters a) :
    Fintype.card (Source V q) = 2 ^ (Fintype.card V * (q.n * 2 ^ ((q.Δ + 1) ^ q.k) * q.b)) := by
  calc
    _ = Fintype.card ((V × (CurrentFiniteBitPartition.Index q.Δ q.k q.n × Fin q.b)) → Bool) :=
      Fintype.card_congr (sourceEquiv V q)
    _ = _ := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
        CurrentFiniteBitPartition.bits_per_vertex]

theorem source_pos (V : Type) [Fintype V] [DecidableEq V] {a : ℕ} (q : Parameters a) :
    0 < Fintype.card (Source V q) := Fintype.card_pos_iff.mpr ⟨fun _ _ _ => false⟩

/-- Pure finite averaging, with opaque functions and a positive source size. -/
private theorem mean_additive {A : Type} [Fintype A] (f z : A → ℝ) (m B p q : ℝ)
    (hA : 0 < Fintype.card A) (h : ∀ v, f v ≤ m + B * p + 2 * B * (q + z v)) :
    (∑ v : A, f v) / Fintype.card A ≤
      m + B * p + 2 * B * (q + (∑ v : A, z v) / Fintype.card A) := by
  have hpos : (0 : ℝ) < Fintype.card A := by exact_mod_cast hA
  have hs : (∑ v : A, f v) ≤
      (Fintype.card A : ℝ) * (m + B * p + 2 * B * q) + 2 * B * ∑ v : A, z v := by
    calc
      _ ≤ ∑ v : A, ((m + B * p + 2 * B * q) + 2 * B * z v) :=
        Finset.sum_le_sum (fun v _ => by nlinarith [h v])
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, nsmul_eq_mul] <;> ring
  calc
    _ ≤ ((Fintype.card A : ℝ) * (m + B * p + 2 * B * q) + 2 * B * ∑ v : A, z v) /
        Fintype.card A := div_le_div_of_nonneg_right hs (le_of_lt hpos)
    _ = _ := by field_simp [ne_of_gt hpos]; ring

section Graph
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Interpretation independent of every random coordinate; no centers supplied. -/
structure Original (k t B : ℕ) (x : V → Private V B) where
  cover : V → Finset V
  targets : V → Finset V
  R : Finset V
  hk : 0 < k
  ht : 0 < t
  incidence : ∀ v r, r ∈ targets v ↔ v ∈ cover r
  local_rows : ∀ r ∈ R, cover r ⊆ closed G r
  nonempty_rows : ∀ r ∈ R, (cover r).Nonempty
  demand : ∀ v, (x v).1.residual = decide (v ∈ R)
  candidates : ∀ v, (x v).1.candidates = cover v
  inverse : ∀ v, (x v).1.targets = targets v

def original {k t B : ℕ} {x : V → Private V B} (d : Original G k t B x)
    (Δ b n : ℕ) (β : V → Coins Δ k b n) :
    GeneralCoveringInitializedRandomIntegral.Original G B Δ k t b n (input x β) where
  cover := d.cover
  targets := d.targets
  R := d.R
  hk := d.hk
  ht := d.ht
  incidence := d.incidence
  local_rows := d.local_rows
  nonempty_rows := d.nonempty_rows
  demand := d.demand
  candidates := d.candidates
  inverse := d.inverse

abbrev output {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B)
    (x : V → Private V B) (β : Source V q) :=
  GeneralCoveringInitializedRandomIntegral.output G ids q.init.b q.init.h q.init.f q.init.U
    q.L q.Δ a q.k q.t q.b q.n B hB (input x β)

def centers {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a) (x : V → Private V B) :=
  GeneralCoveringInitializedRandomIntegral.centers G ids q.init.b q.init.h q.init.f q.init.U B q.Δ q.k q.b q.n
    (input x (fun _ _ _ => false))

theorem centers_eq {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a)
    (x : V → Private V B) (β : Source V q) :
    GeneralCoveringInitializedRandomIntegral.centers G ids q.init.b q.init.h q.init.f q.init.U B q.Δ q.k q.b q.n
      (input x β) = centers G ids a B q x :=
  GeneralCoveringInitializedRandomIntegral.centers_coin_independent G ids q.init.b q.init.h q.init.f q.init.U
    B q.Δ q.k q.b q.n (fun v => (x v).1) (fun v => (x v).2) β (fun _ _ _ => false)

noncomputable def meanCost {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B)
    (x : V → Private V B) : ℝ :=
  (∑ β : Source V q, ((∑ v ∈ output G ids a B q hB x β, (x v).2.val : ℕ) : ℝ)) /
    Fintype.card (Source V q)

structure Specification {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B)
    (ε : ℝ) (x : V → Private V B) (d : Original G q.k q.t B x) : Prop where
  admissible : ∀ β : Source V q, output G ids a B q hB x β ⊆ CoveringSupport.admissible d.cover d.R
  covers : ∀ β : Source V q, GeneralCoveringNormalizedIntegral.Covers d.cover d.R (output G ids a B q hB x β)
  competitive : ∀ W : Finset V, W ⊆ CoveringSupport.admissible d.cover d.R →
    GeneralCoveringNormalizedIntegral.Covers d.cover d.R W →
    meanCost G ids a B q hB x ≤ (1 + ε) * ((∑ v ∈ W, (x v).2.val : ℕ) : ℝ)

/-- Actual numeric initializer bound against EVERY integral benchmark. -/
theorem centers_cost {a B bits : ℕ} (ids : BitCode V bits) (q : Parameters a)
    {x : V → Private V B} (d : Original G q.k q.t B x)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val)
    (W : Finset V) (hWad : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) :
    (centers G ids a B q x).card ≤ q.init.factor * (∑ v ∈ W, (x v).2.val) := by
  have ha0 : (0 : ℝ) ≤ a := by exact_mod_cast (show 0 ≤ a by omega)
  have hn := GeneralCoveringInitializerRunBounds.selected_card G d.cover q.init.b q.init.h q.init.f q.init.U q.init.U
    q.init.hb q.init.hU q.init.hU q.init.candidate_threshold q.init.list_threshold ha0
    q.init.twice_density q.init.twice_density hden q.init.capacity d.R W hW d.local_rows
  have hs := GeneralCoveringInitializedRandomIntegral.centers_selected
    (j := q.init.b) (h := q.init.h) (f := q.init.f) (U := q.init.U) G ids q.init.hb
    (original G d q.Δ q.b q.n (fun _ _ _ => false))
  dsimp only [original] at hs
  rw [← hs] at hn
  have hf : GeneralCoveringInitializerRunBounds.constant q.init.b q.init.h q.init.f q.init.U ≤ q.init.factor := Nat.le_succ _
  have hWcost : W.card ≤ ∑ v ∈ W, (x v).2.val := by
    calc
      W.card = ∑ _v ∈ W, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv => hc v (hWad hv))
  exact hn.trans ((Nat.mul_le_mul_right W.card hf).trans (Nat.mul_le_mul_left q.init.factor hWcost))

/-- Scalar charges refer to the fixed actual centers and SAME public beta. -/
theorem pointwise_cost {bits a B : ℕ} (ids : BitCode V bits) (q : Parameters a) (hB : 1 ≤ B)
    {x : V → Private V B} (d : Original G q.k q.t B x)
    (ha : 1 ≤ a) (hden : MinorDensity.Bound G (a : ℝ))
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val)
    (W : Finset V) (hWad : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) (β : Source V q) :
    ((∑ v ∈ output G ids a B q hB x β, (x v).2.val : ℕ) : ℝ) ≤
      ((∑ v ∈ W, (x v).2.val : ℕ) : ℝ) +
      (B : ℝ) * (GeneralCoveringOwnerSupport.heavy G d.cover (centers G ids a B q x) d.R q.L).card +
      2 * B * ((GeneralCoveringOwnerVirtualPrepare.high G d.cover (centers G ids a B q x) d.R q.L q.Δ).card +
        ((GeneralCoveringRandomBoundaryBound.boundary G d.cover (centers G ids a B q x)
          d.R q.L q.Δ q.k q.hk q.t q.b q.n β).card : ℝ)) := by
  let dβ := original G d q.Δ q.b q.n β
  have hn := GeneralCoveringInitializedRandomIntegral.cost (j := q.init.b) (h := q.init.h) (f := q.init.f)
    (U := q.init.U) (L := q.L) (Δ := q.Δ) (a := a) G ids q.init.hb hB dβ ha hden hc W hWad hW
  have hD := centers_eq G ids a B q x β
  have hP := congrArg (fun D : Finset V => (GeneralCoveringOwnerSupport.heavy G d.cover D d.R q.L).card) hD
  have hQ := congrArg (fun D : Finset V => (GeneralCoveringOwnerVirtualPrepare.high G d.cover D d.R q.L q.Δ).card) hD
  have hb := congrArg Finset.card (GeneralCoveringInitializedRandomIntegral.boundary_eq
    (j := q.init.b) (h := q.init.h) (f := q.init.f) (U := q.init.U) (L := q.L) G ids dβ)
  have hZ := hb.trans (congrArg (fun D : Finset V =>
    (GeneralCoveringRandomBoundaryBound.boundary G d.cover D d.R q.L q.Δ q.k q.hk q.t q.b q.n β).card) hD)
  dsimp only [dβ, original] at hn hZ
  dsimp only at hP hQ hZ
  rw [hP, hQ, hZ] at hn
  exact_mod_cast hn

theorem empty_demands {bits a B : ℕ} {ids : BitCode V bits} {q : Parameters a} {hB : 1 ≤ B}
    {ε : ℝ} {x : V → Private V B} {d : Original G q.k q.t B x}
    (hs : Specification G ids a B q hB ε x d) (hR : d.R = ∅) :
    (∀ β : Source V q, output G ids a B q hB x β = ∅) ∧ meanCost G ids a B q hB x = 0 := by
  have he (β : Source V q) : output G ids a B q hB x β = ∅ := by
    have hh : output G ids a B q hB x β ⊆ ∅ := by
      simpa only [hR, CoveringSupport.admissible, Finset.biUnion_empty] using hs.admissible β
    exact Finset.eq_empty_iff_forall_notMem.mpr (fun v hv => Finset.notMem_empty v (hh hv))
  exact ⟨he, by simp only [meanCost, he, Finset.sum_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div]⟩

theorem zero_benchmark {bits a B : ℕ} {ids : BitCode V bits} {q : Parameters a} {hB : 1 ≤ B}
    {ε : ℝ} {x : V → Private V B} {d : Original G q.k q.t B x}
    (hs : Specification G ids a B q hB ε x d)
    (hc : ∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val)
    (W : Finset V) (hWad : W ⊆ CoveringSupport.admissible d.cover d.R)
    (hW : GeneralCoveringNormalizedIntegral.Covers d.cover d.R W) (hz : ∑ v ∈ W, (x v).2.val = 0) :
    d.R = ∅ ∧ (∀ β : Source V q, output G ids a B q hB x β = ∅) ∧ meanCost G ids a B q hB x = 0 := by
  have he : W = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hvCost := Finset.single_le_sum (fun u _ => Nat.zero_le ((x u).2.val)) hv
    have hp := hc v (hWad hv)
    omega
  have hR : d.R = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨v, hv, _⟩ := hW r hr
    rw [he] at hv
    exact Finset.notMem_empty v hv
  exact ⟨hR, empty_demands G hs hR⟩

theorem empty_physical [IsEmpty V] {bits : ℕ} (ids : BitCode V bits) (a B : ℕ) (q : Parameters a)
    (hB : 1 ≤ B) (x : V → Private V B) :
    (∀ β : Source V q, output G ids a B q hB x β = ∅) ∧ meanCost G ids a B q hB x = 0 := by
  have he (β : Source V q) : output G ids a B q hB x β = ∅ :=
    GeneralCoveringInitializedRandomIntegral.empty_physical G ids q.init.b q.init.h q.init.f q.init.U
      q.L q.Δ a q.k q.t q.b q.n B hB (input x β)
  exact ⟨he, by simp only [meanCost, he, Finset.sum_empty, Nat.cast_zero, Finset.sum_const_zero, zero_div]⟩
end Graph

/-- All numeric choices, including eta and the finite-bit space, precede
every graph, identifier code, private instance and integral benchmark. -/
theorem uniform_approximation (a B : ℕ) (ha : 1 ≤ a) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Parameters a,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ {bits : ℕ} (ids : BitCode V bits)
        (x : V → Private V B) (d : Original G q.k q.t B x),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val) →
        Specification G ids a B q hB ε x d := by
  obtain ⟨i⟩ := initialization_exists a ha
  obtain ⟨L, Δ, η, hL, hLa, hΔ, hη, hheavy, hhigh, hboundary⟩ :=
    error_budgets a B i.factor hB i.factor_pos ε hε
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := zero_le_one.trans ha'
  obtain ⟨t, k, b, n, ht, hk, hbdy⟩ := GeneralCoveringRandomBoundaryBound.parameters
    (a : ℝ) ha0 L hL Δ η hη
  let q : Parameters a := {
    init := i
    L := L
    Δ := Δ
    η := η
    t := t
    k := k
    b := b
    n := n
    ht := ht
    hk := hk
    hη := hη
  }
  refine ⟨q, ?_⟩
  intro V _ _ G _ hden bits ids x d hc
  refine ⟨?_, ?_, ?_⟩
  · intro β
    exact (GeneralCoveringInitializedRandomIntegral.covers (j := i.b) (h := i.h) (f := i.f) (U := i.U)
      (L := L) (Δ := Δ) (a := a) G ids i.hb hB (original G d Δ b n β) ha hden hc).1
  · intro β
    exact (GeneralCoveringInitializedRandomIntegral.covers (j := i.b) (h := i.h) (f := i.f) (U := i.U)
      (L := L) (Δ := Δ) (a := a) G ids i.hb hB (original G d Δ b n β) ha hden hc).2
  · intro W hWad hW
    let D := centers G ids a B q x
    let P := GeneralCoveringOwnerSupport.heavy G d.cover D d.R L
    let Q := GeneralCoveringOwnerVirtualPrepare.high G d.cover D d.R L Δ
    let m := ∑ v ∈ W, (x v).2.val
    let Z := GeneralCoveringRandomBoundaryBound.meanBoundary G d.cover D d.R L Δ k hk t b n
    have hN : (D.card : ℝ) ≤ (i.factor : ℝ) * m := by
      exact_mod_cast centers_cost G ids q d ha hden hc W hWad hW
    have hP : (L : ℝ) * P.card ≤ 2 * (a : ℝ) * D.card :=
      GeneralCoveringHeavyCount.count G d.cover D d.R L d.local_rows ha' hLa hden
    have hQ : (Δ : ℝ) * Q.card ≤ (2 * (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) * D.card := by
      simpa only [mul_assoc] using GeneralCoveringOwnerHighCount.count G d.cover D d.R L Δ hL d.local_rows ha0 hden
    have hZ : Z ≤ 2 * η * D.card := (hbdy G hden d.cover D d.R d.local_rows ids).2.2.2
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hΔ0 : (0 : ℝ) < Δ := by exact_mod_cast hΔ
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hp : (B : ℝ) * P.card ≤ (ε / 3) * m :=
      count_budget (c := 2 * (a : ℝ)) (den := (L : ℝ)) hm (Nat.cast_nonneg B) (by positivity) hL0 hN hP hheavy
    have hq : (2 * (B : ℝ)) * Q.card ≤ (ε / 3) * m :=
      count_budget (c := 2 * (a : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 4) (den := (Δ : ℝ))
        hm (by positivity) (by positivity) hΔ0 hN hQ hhigh
    have hz : (2 * (B : ℝ)) * Z ≤ (ε / 3) * m :=
      count_budget (c := 2 * η) (den := 1) hm (by positivity) (by positivity) (by norm_num) hN
        (by simpa only [one_mul] using hZ) (by simpa only [div_one] using hboundary)
    have hy : meanCost G ids a B q hB x ≤ (m : ℝ) + (B : ℝ) * P.card + 2 * B * ((Q.card : ℝ) + Z) := by
      simpa only [meanCost, GeneralCoveringRandomBoundaryBound.meanBoundary] using
        mean_additive
          (fun β : Source V q => ((∑ v ∈ output G ids a B q hB x β, (x v).2.val : ℕ) : ℝ))
          (fun β : Source V q => ((GeneralCoveringRandomBoundaryBound.boundary G d.cover D d.R L Δ k hk t b n β).card : ℝ))
          (m : ℝ) (B : ℝ) (P.card : ℝ) (Q.card : ℝ) (source_pos V q)
          (fun β => pointwise_cost G ids q hB d ha hden hc W hWad hW β)
    exact additive_to_approximation hy hp hq hz

def roundBound (a B : ℕ) (q : Parameters a) : ℕ :=
  q.init.U * (5 + 2 * q.init.f) + 2 +
    ((10 + 4 * (q.n * (3 * q.k + 1) + 1) + (RecursiveSearch.roundBound (4 * q.k) a (2 * B * q.k) + 4)) + 2)

def bitCoefficient {a : ℕ} (B c p e : ℕ) (q : Parameters a) : ℕ :=
  GeneralCoveringInitializedRandomIntegral.bitCoefficient q.init.f q.L q.Δ a q.k q.b q.n B
    (DeterministicColorReductionIdentifiers.bitFactor c p e)

/-- Exact constant physical rounds and actual public-card logarithmic bits. -/
theorem resources {V : Type} [Fintype V] [LinearOrder V] {bits : ℕ} (ids : BitCode V bits)
    (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B) (c p e M : ℕ)
    (hbits : bits ≤ c * Nat.clog 2 M) (hM : M ≤ p * (Fintype.card V + 2) ^ e) :
    (program ids a B q hB).rounds = roundBound a B q ∧
      (program ids a B q hB).maxBits ≤ bitCoefficient B c p e q * Nat.clog 2 (Fintype.card V + 2) := by
  simpa only [program, roundBound, bitCoefficient] using
    GeneralCoveringInitializedRandomIntegral.public_costs ids q.init.b q.init.h q.init.f q.init.U
      q.L q.Δ a q.k q.t q.b q.n B c p e M hB hbits hM

theorem packet_bound {V : Type} [Fintype V] [LinearOrder V] {bits : ℕ} (ids : BitCode V bits)
    (a B : ℕ) (q : Parameters a) (hB : 1 ≤ B) :
    (program ids a B q hB).maxBits ≤ max (max (bits + 1) (q.init.f * (bits + 1)))
      (max (max ((q.L + q.Δ + 3) *
        (bits + max (ActiveFiniteBitPartition.packetBound bits q.Δ q.k q.b q.n) (q.k * (bits + 1)) + 2))
        (max (bits + 2) (max 1 q.L * (bits + (GeneralCoveringTaskIntegral.program ids a B q.k hB).maxBits + 1)))) (bits + 1)) :=
  GeneralCoveringInitializedRandomIntegral.packet_bound ids q.init.b q.init.h q.init.f q.init.U
    q.L q.Δ a q.k q.t q.b q.n B hB

/-- Program, finite coin space and both resource constants precede V/G/IDs/x. -/
theorem uniform_scheme (a B : ℕ) (ha : 1 ≤ a) (hB : 1 ≤ B) (ε : ℝ) (hε : 0 < ε) (c p e : ℕ) :
    ∃ q : Parameters a, ∃ Kr Kb : ℕ,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G (a : ℝ) → ∀ {bits : ℕ} (ids : BitCode V bits) (M : ℕ),
        bits ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card V + 2) ^ e →
        ∀ (x : V → Private V B) (d : Original G q.k q.t B x),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val) →
        Specification G ids a B q hB ε x d ∧
        (program ids a B q hB).rounds = Kr ∧
        (program ids a B q hB).maxBits ≤ Kb * Nat.clog 2 (Fintype.card V + 2) := by
  obtain ⟨q, hq⟩ := uniform_approximation a B ha hB ε hε
  refine ⟨q, roundBound a B q, bitCoefficient B c p e q, ?_⟩
  intro V _ _ G _ hden bits ids M hbits hM x d hc
  exact ⟨hq G hden ids x d hc, resources ids a B q hB c p e M hbits hM⟩

/-- Real physical density capacity is rounded publicly before every graph. -/
theorem randomized_scheme (ρ : ℝ) (hρ : 1 ≤ ρ) (B : ℕ) (hB : 1 ≤ B)
    (ε : ℝ) (hε : 0 < ε) (c p e : ℕ) :
    ∃ a : ℕ, ∃ q : Parameters a, ∃ Kr Kb : ℕ, ρ ≤ (a : ℝ) ∧
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        MinorDensity.Bound G ρ → ∀ {bits : ℕ} (ids : BitCode V bits) (M : ℕ),
        bits ≤ c * Nat.clog 2 M → M ≤ p * (Fintype.card V + 2) ^ e →
        ∀ (x : V → Private V B) (d : Original G q.k q.t B x),
        (∀ v ∈ CoveringSupport.admissible d.cover d.R, 1 ≤ (x v).2.val) →
        Specification G ids a B q hB ε x d ∧
        (program ids a B q hB).rounds = Kr ∧
        (program ids a B q hB).maxBits ≤ Kb * Nat.clog 2 (Fintype.card V + 2) := by
  let a := Nat.ceil ρ
  have hρa : ρ ≤ (a : ℝ) := Nat.le_ceil ρ
  have ha : 1 ≤ a := by exact_mod_cast hρ.trans hρa
  obtain ⟨q, Kr, Kb, hq⟩ := uniform_scheme a B ha hB ε hε c p e
  refine ⟨a, q, Kr, Kb, hρa, ?_⟩
  intro V _ _ G _ hden bits ids M hbits hM x d hc
  have hdenA : MinorDensity.Bound G (a : ℝ) := by
    intro W _ _ J _ hm
    exact (hden W J hm).trans (mul_le_mul_of_nonneg_right hρa (Nat.cast_nonneg _))
  exact hq G hdenA ids M hbits hM x d hc

end Paper.GeneralCoveringRandomIntegralApproximation

#print axioms Paper.GeneralCoveringRandomIntegralApproximation.sourceEquiv
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.source_card
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.source_pos
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.original
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.centers_eq
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.centers_cost
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.pointwise_cost
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.empty_demands
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.zero_benchmark
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.empty_physical
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.uniform_approximation
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.resources
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.packet_bound
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.uniform_scheme
#print axioms Paper.GeneralCoveringRandomIntegralApproximation.randomized_scheme
