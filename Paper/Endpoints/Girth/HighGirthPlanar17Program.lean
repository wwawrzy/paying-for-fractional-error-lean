import Paper.Endpoints.Girth.HighGirthPhysicalRoundingCorrect

/-! One physical KT0 algorithm family for the planar girth-seventeen upper
bound. All configuration numbers are fixed before the graph. -/
namespace Paper.HighGirthPlanar17Program
open BroadcastModel (BitCode)

structure Config where
  A : Nat
  L : Nat
  Δ : Nat
  r : Nat
  k : Nat
  t : Nat
  Q : Nat
  T : Nat
  s : Nat
  q : Nat
  M : Nat
  Q_pos : 0 < Q
  q_pos : 0 < q

variable {V : Type} [LinearOrder V]

def solver {b : Nat} (C : BitCode V b) (p : Config) :=
  GeneralFractionalBroadcast.program C p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s 3 p.q p.M p.Q_pos

def denominator (p : Config) : Nat :=
  PartialFractionalProgram.denominator p.Δ p.k p.Q p.T p.s p.q

def program {b : Nat} (C : BitCode V b) (p : Config) : PortBroadcastModel.Program V Unit Bool :=
  HighGirthPhysicalRounding.program C (solver C p) (denominator p)

def roundBound (p : Config) : Nat :=
  11 + ((2 * p.A) * (4 + 2 * GeneralInitBroadcast.rank p.A) +
    (34 + 4 * OwnerBoundaryMean.radius p.k p.T + 4 * p.r + RecursiveSearch.roundBound (4 * p.k) p.A p.M))

def solverMessageConstant (p : Config) (c : Nat) : Nat :=
  max (1 + GeneralInitBroadcast.rank p.A * (c + 1))
    (PartialFractionalBudget.constant p.L p.Δ p.r p.k p.Q p.T p.s p.A 3 p.q p.M c)

def messageConstant (p : Config) (c : Nat) : Nat := max 1 (max c (solverMessageConstant p c))

variable [Fintype V]

theorem rounds {b : Nat} (C : BitCode V b) (p : Config) :
    (program C p).rounds = roundBound p := by
  rw [program, HighGirthPhysicalRounding.rounds]
  rw [solver, GeneralFractionalBroadcast.rounds]
  rfl

theorem logarithmic_bits {b : Nat} (C : BitCode V b) (p : Config)
    (n c : Nat) (hids : b ≤ c * Nat.clog 2 (n+2)) :
    (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n+2) := by
  rw [program, HighGirthPhysicalRounding.maxBits]
  have hp := GeneralFractionalBroadcast.logarithmic_bits C p.A p.L p.Δ p.r p.k p.t p.Q p.T p.s 3 p.q p.M p.Q_pos n c hids
  have hl : 1 ≤ Nat.clog 2 (n+2) := Nat.clog_pos (by omega) (by omega)
  have h1 : 1 ≤ messageConstant p c := le_max_left _ _
  have hc : c ≤ messageConstant p c := (le_max_left _ _).trans (le_max_right _ _)
  have hk : solverMessageConstant p c ≤ messageConstant p c :=
    (le_max_right _ _).trans (le_max_right _ _)
  apply max_le
  · simpa using Nat.mul_le_mul h1 hl
  · apply max_le
    · exact hids.trans (Nat.mul_le_mul_right _ hc)
    · exact hp.trans (Nat.mul_le_mul_right _ hk)

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def raw {b : Nat} (C : BitCode V b) (p : Config) (v : V) : Real :=
  (((solver C p).runEncoded (HighGirthMaskedInput.graph G)
    (fun u => (decide (u ∈ HighGirthTransformation.demands G), HighGirthMaskedInput.weight G u)) v).val : Real) /
    denominator p

noncomputable def fractional {b : Nat} (C : BitCode V b) (p : Config) : V → Real :=
  HighGirthMaskedInput.capped G (raw G C p)

def output (ports : PortBroadcastModel.Numbering G) {b : Nat} (C : BitCode V b) (p : Config) : Finset V :=
  Finset.univ.filter (fun v => (program C p).runEncoded G ports (fun _ => ()) v = true)

theorem output_eq (ports : PortBroadcastModel.Numbering G) {b : Nat} (C : BitCode V b) (p : Config) :
    output G ports C p = HighGirthTransformation.far G ∪ HighGirthRounding.output G (fractional G C p) := by
  have hd : 0 < denominator p := PartialFractionalProgram.denominator_pos _ _ _ _ _ _ p.Q_pos p.q_pos
  have h := HighGirthPhysicalRoundingCorrect.physical_rounding_encoded_correct G ports C (solver C p) (denominator p) hd
  ext v
  change (v ∈ Finset.univ.filter (fun u => (HighGirthPhysicalRounding.program C (solver C p) (denominator p)).runEncoded G ports (fun _ => ()) u = true)) ↔ _
  rw [h.1]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  rfl

theorem girth_density (hplanar : G.IsPlanar)
    (hgirth : ∀ (v : V) (w : G.Walk v v), w.IsCycle → 17 ≤ w.length) :
    Incidence.InducedDensityBound G ((17/15 : Rat) : Real) := by
  have h := CurrentPlanarFaceBound.induced_density hplanar 17 (by decide) hgirth
  convert h using 1 <;> norm_num

end Paper.HighGirthPlanar17Program

namespace Paper.HighGirthPlanar17Program

theorem uniform_solver_input
    : ∃ p : Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → ∀ {b : Nat} (C : BroadcastModel.BitCode V b),
        SevenFoundation.feasible (HighGirthAuxiliary.auxiliary G) (fractional G C p) ∧
        (∀ v ∈ HighGirthTransformation.zone G, fractional G C p v ≤ 1) ∧
        SevenFoundation.cost (HighGirthAuxiliary.auxiliary G) (fractional G C p) ≤
          (1+(5 : Real)/8482)*HighGirthAuxiliary.number G := by
  obtain ⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq,hp⟩ := HighGirthSolverParameters.planar_solver_input_parameters
  refine ⟨⟨A,L,Δ,r,k,t,Q,T,s,q,M,hQ,hq⟩, ?_⟩
  intro V _ _ G _ hplanar b C
  exact hp G hplanar C

end Paper.HighGirthPlanar17Program
#print axioms Paper.HighGirthPlanar17Program.rounds
#print axioms Paper.HighGirthPlanar17Program.logarithmic_bits
#print axioms Paper.HighGirthPlanar17Program.output_eq
#print axioms Paper.HighGirthPlanar17Program.girth_density
#print axioms Paper.HighGirthPlanar17Program.uniform_solver_input
