import Paper.Endpoints.Girth.CurrentGirthProgram
import Paper.Endpoints.Girth.NoncriticalGirth

/-!
# Theorem C(iii): one public configuration for every fixed girth

The configuration is selected before the vertex type, input graph, ports,
or identifier representation. Its program is the actual encoded KT0
broadcast program; the drawing and component minor occur only in proofs.
-/

namespace Paper.CurrentGirthKT0

open BroadcastModel SevenFoundation

inductive Config where
  | critical (d A L Δ r k t Q T s q M : ℕ) (hQ : 0 < Q)
  | noncritical (p : MinorDensityBroadcast.Config)

def program {V : Type} [Fintype V] [LinearOrder V] {b : ℕ} (C : BitCode V b) :
    Config → PortBroadcastModel.Program V Unit Bool
  | .critical d A L Δ r k t Q T s q M hQ =>
      CurrentCriticalKT0.program C d (PartialFractionalProgram.denominator Δ k Q T s q)
        (GeneralFractionalBroadcast.program C A L Δ r k t Q T s (d + 1) q M hQ)
  | .noncritical p => MinorDensityKT0.program C p

def roundBound : Config → ℕ
  | .critical _ A _ _ r k _ _ T _ _ M _ => CurrentCriticalKT0.roundBound A r k T M
  | .noncritical p => 1 + MinorDensityBroadcast.roundBound p

def messageConstant (p : Config) (c : ℕ) : ℕ :=
  match p with
  | .critical d A L Δ r k _ Q T s q M _ =>
      CurrentCriticalKT0.messageConstant d A L Δ r k Q T s q M c
  | .noncritical p => max c (MinorDensityBroadcast.messageConstant p c)

def output {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ports : PortBroadcastModel.Numbering G)
    {b : ℕ} (C : BitCode V b) (p : Config) : Finset V :=
  Finset.univ.filter (fun v => (program C p).runEncoded G ports (fun _ => ()) v)

set_option maxHeartbeats 1500000 in
theorem parameters (g : ℕ) (hg : 3 ≤ g) :
    ∃ p : Config,
      ∀ {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
        G.IsPlanar →
        (∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) →
        ∀ (ports : PortBroadcastModel.Numbering G) {b : ℕ} (C : BitCode V b),
          dominates G (output G ports C p) ∧
          ((output G ports C p).card : ℝ) ≤
            (3 + 4 / ((g : ℝ) - 2)) * fractionalNumber G ∧
          (program C p).rounds = roundBound p ∧
          ∀ n c : ℕ, b ≤ c * Nat.clog 2 (n + 2) →
            (program C p).maxBits ≤ messageConstant p c * Nat.clog 2 (n + 2) := by
  by_cases h3 : g = 3
  · subst g
    obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hp⟩ :=
      CurrentCriticalKT0.parameters 3 (by norm_num) 6 (by norm_num)
    refine ⟨.critical 6 A L Δ r k t Q T s q M hQ, ?_⟩
    intro V _ _ G _ hplanar hgirth ports b C
    have hh := hp G (PlanarDensity.minor_density G hplanar) ports C
    dsimp only at hh
    have hs := And.intro hh.1
      (And.intro hh.2.1 (And.intro hh.2.2.2.1 hh.2.2.2.2.2))
    norm_num at hs ⊢
    simpa only [output, program, roundBound, messageConstant, CurrentCriticalKT0.output] using hs
  by_cases h4 : g = 4
  · subst g
    obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hp⟩ :=
      CurrentGirthProgram.parameters_four
    refine ⟨.critical 4 A L Δ r k t Q T s q M hQ, ?_⟩
    intro V _ _ G _ hplanar hgirth ports b C
    have hh := hp G hplanar hgirth ports C
    dsimp only at hh
    norm_num at hh ⊢
    simpa only [output, program, roundBound, messageConstant, CurrentCriticalKT0.output] using hh
  by_cases h6 : g = 6
  · subst g
    obtain ⟨A, L, Δ, r, k, t, Q, T, s, q, M, hQ, hq, hp⟩ :=
      CurrentGirthProgram.parameters_six
    refine ⟨.critical 3 A L Δ r k t Q T s q M hQ, ?_⟩
    intro V _ _ G _ hplanar hgirth ports b C
    have hh := hp G hplanar hgirth ports C
    dsimp only at hh
    norm_num at hh ⊢
    simpa only [output, program, roundBound, messageConstant, CurrentCriticalKT0.output] using hh
  have hg5 : 5 ≤ g := by omega
  obtain ⟨p, hp⟩ := NoncriticalGirth.parameters g hg5 h6
  refine ⟨.noncritical p, ?_⟩
  intro V _ _ G _ hplanar hgirth ports b C
  simpa only [output, program, roundBound, messageConstant, MinorDensityKT0.output] using
    hp G hplanar hgirth ports C

end Paper.CurrentGirthKT0

#print axioms Paper.CurrentGirthKT0.parameters
