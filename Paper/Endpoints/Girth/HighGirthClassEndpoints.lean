import Paper.Endpoints.Girth.HighGirthMinorUpper
import Paper.Endpoints.Girth.HighGirthProperClass
import Paper.Endpoints.Girth.HighGirthMinorLower

/-! The proper-minor-closed-class consequence and the all-paths LOCAL lower
branch of fv:hg:minor-three. All assertions retain the actual execution model. -/
namespace Paper.HighGirthClassEndpoints
open HighGirthPlanar17Program

theorem proper_upper (P : HighGirthProperClass.Class)
    (hclosed : HighGirthProperClass.Closed P)
    (hproper : ∃ n, ∃ H : SimpleGraph (Fin n), ¬ P H) :
    ∃ rho : Rat, 1 ≤ rho ∧ ∃ p : Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        P G →
        (∀ (v : V) (w : G.Walk v v), w.IsCycle → HighGirthMinorParameters.girth rho ≤ w.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : Nat} (C : BroadcastModel.BitCode V b),
        SevenFoundation.dominates G (output G ports C p) ∧
        ((output G ports C p).card:Real) ≤ 3*SevenFoundation.fractionalNumber G ∧
        (program C p).rounds = roundBound p ∧
        ∀ n c : Nat, b ≤ c*Nat.clog 2 (n+2) →
          (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n+2) := by
  obtain ⟨rho,hrho,hden⟩ := HighGirthProperClass.rational_density P hclosed hproper
  obtain ⟨p,hp⟩ := HighGirthMinorUpper.upper rho hrho
  refine ⟨rho,hrho,p,?_⟩
  intro V _ _ G _ hG hg ports b C
  exact hp G (hden G hG) hg ports C

theorem all_paths_lower (P : HighGirthProperClass.Class)
    (hpaths : ∀ n, P (SimpleGraph.pathGraph n)) (g T : Nat) (c : Real) (hc : c < 3) :
    ∃ n : Nat, 0 < n ∧ P (PathPowerTreewidth.graph n 1) ∧
      (∀ (v : Fin n) (w : (PathPowerTreewidth.graph n 1).Walk v v), w.IsCycle → g ≤ w.length) ∧
      ∀ Q : PortLocal.Program Unit Bool, Q.rounds ≤ T →
        (∀ (N : PortLocal.Network (Fin n)), N.Compatible (PathPowerTreewidth.graph n 1) →
          ∀ ids : Fin n → Nat, Function.Injective ids →
          (∀ i, 1 ≤ ids i ∧ ids i ≤ n) →
          SevenFoundation.dominates (PathPowerTreewidth.graph n 1)
            (TreewidthLocalLower.output N Q ids)) →
        ∃ (N : PortLocal.Network (Fin n)) (ids : Fin n → Nat),
          N.Compatible (PathPowerTreewidth.graph n 1) ∧ Function.Injective ids ∧
          Finset.univ.image ids = Finset.Icc 1 n ∧
          c * (PathPowerTreewidth.graph n 1).dominationNumber <
            (TreewidthLocalLower.output N Q ids).card := by
  obtain ⟨n,hn,_,_,hg,hbad⟩ := HighGirthMinorLower.minor_density_large_girth_lower 1 (by norm_num) g T c hc
  refine ⟨n,hn,?_,hg,hbad⟩
  rw [HighGirthPathFamily.first_power_eq_path]
  exact hpaths n

end Paper.HighGirthClassEndpoints
#print axioms Paper.HighGirthClassEndpoints.proper_upper
#print axioms Paper.HighGirthClassEndpoints.all_paths_lower
