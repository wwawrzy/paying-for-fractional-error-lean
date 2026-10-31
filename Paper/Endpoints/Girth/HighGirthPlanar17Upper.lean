import Paper.Endpoints.Girth.HighGirthPlanar17Program
set_option maxHeartbeats 200000
namespace Paper.HighGirthPlanar17Upper

theorem planar_girth_seventeen_upper
    : ∃ p : Paper.HighGirthPlanar17Program.Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar → (∀ (v : V) (w : G.Walk v v), w.IsCycle → 17 ≤ w.length) →
        ∀ (ports : Paper.PortBroadcastModel.Numbering G) {b : Nat}
          (C : Paper.BroadcastModel.BitCode V b),
        Paper.SevenFoundation.dominates G (Paper.HighGirthPlanar17Program.output G ports C p) ∧
        ((Paper.HighGirthPlanar17Program.output G ports C p).card : Real) ≤
          3 * Paper.SevenFoundation.fractionalNumber G ∧
        (Paper.HighGirthPlanar17Program.program C p).rounds = Paper.HighGirthPlanar17Program.roundBound p ∧
        ∀ n c : Nat, b ≤ c * Nat.clog 2 (n+2) →
          (Paper.HighGirthPlanar17Program.program C p).maxBits ≤
            Paper.HighGirthPlanar17Program.messageConstant p c * Nat.clog 2 (n+2) := by
  classical
    obtain ⟨p,hp⟩ := Paper.HighGirthPlanar17Program.uniform_solver_input
    refine ⟨p,?_⟩
    intro V _ _ G _ hplanar hgirth ports b C
    have h := hp G hplanar C
    have hs : Paper.SevenFoundation.cost (Paper.HighGirthAuxiliary.auxiliary G) (Paper.HighGirthPlanar17Program.fractional G C p) ≤
        (1 + (Paper.HighGirthSlackParameter.delta (17/15) : Real)) * Paper.HighGirthAuxiliary.number G := by
      simpa only [Paper.HighGirthSlackParameter.at_seventeen_fifteenths, Rat.cast_div, Rat.cast_ofNat] using h.2.2
    have hdensity := Paper.HighGirthPlanar17Program.girth_density G hplanar hgirth
    obtain ⟨hdelta,h17,hD,hdom,hcard⟩ := Paper.HighGirthStaticThree.coefficient_three_static
      G (Paper.HighGirthPlanar17Program.fractional G C p) (17/15) (by norm_num) (by norm_num) h.1 h.2.1 hdensity hs
    refine ⟨?_,?_,Paper.HighGirthPlanar17Program.rounds C p,fun n c hids => Paper.HighGirthPlanar17Program.logarithmic_bits C p n c hids⟩
    · rw [Paper.HighGirthPlanar17Program.output_eq]
      exact hdom
    · rw [Paper.HighGirthPlanar17Program.output_eq]
      exact hcard

end Paper.HighGirthPlanar17Upper

#print axioms Paper.HighGirthPlanar17Upper.planar_girth_seventeen_upper
