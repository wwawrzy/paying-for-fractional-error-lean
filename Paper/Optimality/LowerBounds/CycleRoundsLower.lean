import Paper.Optimality.LowerBounds.CyclePortLocal
import Paper.Optimality.LowerBounds.CycleRamseyCount

/-! A deterministic cycle lower bound for actual unrestricted per-port LOCAL
execution. Each program may be chosen for its exact public cycle order.
Only identifiers 1,...,N are tested. The evaluator even supplies the stronger
KT1 initial neighbor-identifier table. -/
namespace Paper.CycleRoundsLower

open SimpleGraph SevenFoundation CycleRamseyCount
  DeterministicColorReductionLogStar

theorem program (n : ℕ) (P : PortLocal.Program Unit Bool)
    (ε : ℝ) (hε : 0 < ε) (hq : ε < 1 / 4)
    (hguarantee : ∀ ids : Fin (n + 3) → ℕ, Function.Injective ids →
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n + 3) →
      dominates (cycleGraph (n + 3))
        (selected (P.run (CyclePortLocal.network n) ids (fun _ => ()))) ∧
      ((selected (P.run (CyclePortLocal.network n) ids (fun _ => ()))).card : ℝ) ≤
        (1 + ε) * (cycleGraph (n + 3)).dominationNumber) :
    logStar (n + 3) ≤ 16 * P.rounds + 62 := by
  have hN := exact_order_obstruction n (P.rounds + 1) (by omega)
    (LineLocalWindow.rule (CyclePortLocal.translate P) (P.rounds + 1))
    (fun ids => P.run (CyclePortLocal.network n) ids (fun _ => ())) ε hε hq (by
      intro ids hinj hids
      exact ⟨CyclePortLocal.agrees P _ (by omega) ids, hguarantee ids hinj hids⟩)
  have hh := CycleRamseyLogStar.order_logStar (n + 3) (P.rounds + 1) hN
  omega

/-- The program family is indexed by public N before the adversarial labeling.
No common constant radius or uniform identifier-insensitivity is assumed. -/
theorem family (P : ℕ → PortLocal.Program Unit Bool)
    (ε : ℝ) (hε : 0 < ε) (hq : ε < 1 / 4)
    (hguarantee : ∀ (n : ℕ) (ids : Fin (n + 3) → ℕ), Function.Injective ids →
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n + 3) →
      dominates (cycleGraph (n + 3))
        (selected ((P (n + 3)).run (CyclePortLocal.network n) ids (fun _ => ()))) ∧
      ((selected ((P (n + 3)).run (CyclePortLocal.network n) ids (fun _ => ()))).card : ℝ) ≤
        (1 + ε) * (cycleGraph (n + 3)).dominationNumber) :
    ∀ n, logStar (n + 3) ≤ 16 * (P (n + 3)).rounds + 62 := by
  intro n
  exact program n (P (n + 3)) ε hε hq (hguarantee n)

/-- An explicit positive asymptotic coefficient follows from the checked
additive bound; the threshold is stated in the same binary log-star. -/
theorem omega_bound (n : ℕ) (P : PortLocal.Program Unit Bool)
    (hbound : logStar (n + 3) ≤ 16 * P.rounds + 62)
    (hlarge : 124 ≤ logStar (n + 3)) :
    (logStar (n + 3) : ℝ) / 32 ≤ P.rounds := by
  have hb : (logStar (n + 3) : ℝ) ≤ 16 * (P.rounds : ℝ) + 62 := by exact_mod_cast hbound
  have hn : (124 : ℝ) ≤ logStar (n + 3) := by exact_mod_cast hlarge
  linarith

def tower : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ tower k

theorem tower_positive (k : ℕ) : 0 < tower k := by
  cases k <;> simp only [tower] <;> positivity

theorem logStar_tower (k : ℕ) : logStar (tower k) = k := by
  induction k with
  | zero => exact logStar_small 1 (by decide)
  | succ k ih =>
    have hp : 1 < 2 ^ tower k := Nat.one_lt_pow (Nat.ne_of_gt (tower_positive k)) (by decide)
    rw [tower, logStar_step _ hp, Nat.clog_pow 2 (tower k) (by decide), ih]

/-- Full asymptotic quantifiers: a family chosen for public N, every exact-ID
labeling, and a fixed positive lower-bound coefficient beyond a fixed order. -/
theorem asymptotic (P : ℕ → PortLocal.Program Unit Bool)
    (ε : ℝ) (hε : 0 < ε) (hq : ε < 1 / 4)
    (hguarantee : ∀ (n : ℕ) (ids : Fin (n + 3) → ℕ), Function.Injective ids →
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n + 3) →
      dominates (cycleGraph (n + 3))
        (selected ((P (n + 3)).run (CyclePortLocal.network n) ids (fun _ => ()))) ∧
      ((selected ((P (n + 3)).run (CyclePortLocal.network n) ids (fun _ => ()))).card : ℝ) ≤
        (1 + ε) * (cycleGraph (n + 3)).dominationNumber) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n + 3 →
      (logStar (n + 3) : ℝ) / 32 ≤ (P (n + 3)).rounds := by
  refine ⟨tower 124, ?_⟩
  intro n hn
  have hh := DeterministicColorReductionLogStar.logStar_mono hn
  rw [logStar_tower] at hh
  exact omega_bound n (P (n + 3)) (family P ε hε hq hguarantee n) hh

/-- A guarantee for every ordinary port numbering specializes to the checked
closed-cycle network. All public-order and identifier quantifiers stay outside
the execution; arbitrary per-port message types remain unrestricted. -/
theorem local_algorithm (P : ℕ → PortLocal.Program Unit Bool)
    (ε : ℝ) (hε : 0 < ε) (hq : ε < 1 / 4)
    (hguarantee : ∀ (n : ℕ) (net : PortLocal.Network (Fin (n + 3))),
      net.Compatible (cycleGraph (n + 3)) →
      ∀ ids : Fin (n + 3) → ℕ, Function.Injective ids →
      (∀ i, 1 ≤ ids i ∧ ids i ≤ n + 3) →
      dominates (cycleGraph (n + 3))
        (selected ((P (n + 3)).run net ids (fun _ => ()))) ∧
      ((selected ((P (n + 3)).run net ids (fun _ => ()))).card : ℝ) ≤
        (1 + ε) * (cycleGraph (n + 3)).dominationNumber) :
    (∀ n, logStar (n + 3) ≤ 16 * (P (n + 3)).rounds + 62) ∧
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n + 3 →
      (logStar (n + 3) : ℝ) / 32 ≤ (P (n + 3)).rounds := by
  have hcanonical := fun n => hguarantee n (CyclePortLocal.network n) (CyclePortLocal.compatible n)
  exact ⟨family P ε hε hq hcanonical, asymptotic P ε hε hq hcanonical⟩

end Paper.CycleRoundsLower

#print axioms Paper.CycleRoundsLower.program
#print axioms Paper.CycleRoundsLower.family
#print axioms Paper.CycleRoundsLower.omega_bound
#print axioms Paper.CycleRoundsLower.asymptotic
#print axioms Paper.CycleRoundsLower.local_algorithm
