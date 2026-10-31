import Paper.Partitions.Local.DeterministicPartitionGreedy
import Paper.Partitions.Local.PriorityTableCode
import Paper.Preliminaries.CandidateFrameAgreement

/-! Explicit bounded candidate colors from supplied colors of the 2k power.
We use a padded membership mask instead of a rank among assigned sets. This
coarser palette is parameter bounded and its evaluation is fully executable.
Computing the supplied power coloring is not asserted here. -/
namespace Paper.DeterministicPartitionColors
variable {V : Type} [LinearOrder V]

def code (N : V → Finset V) (Δ k : ℕ) (fallback : V) (Φ : ℕ)
    (χ : V → Fin Φ) (U : Finset V) : Fin (Φ * 2 ^ ((Δ + 1) ^ k)) :=
  let p := FinitePriorityIndex.index N Δ k U fallback
  finProdFinEquiv (χ p.1, PriorityTableCode.masks ((Δ + 1) ^ k) p.2)

def color (N : V → Finset V) (Δ k : ℕ) (fallback : V) (Φ : ℕ)
    (χ : V → Fin Φ) (U : Finset V) : ℕ := (code N Δ k fallback Φ χ U).val

theorem palette (N : V → Finset V) (Δ k : ℕ) (fallback : V) (Φ : ℕ)
    (χ : V → Fin Φ) (U : Finset V) :
    color N Δ k fallback Φ χ U < Φ * 2 ^ ((Δ + 1) ^ k) :=
  (code N Δ k fallback Φ χ U).isLt

theorem fallback_eq (N : V → Finset V) (Δ k : ℕ) (a b : V) (Φ : ℕ)
    (χ : V → Fin Φ) (U : Finset V) (hne : U.Nonempty) :
    color N Δ k a Φ χ U = color N Δ k b Φ χ U := by
  simp only [color, code, FinitePriorityIndex.index, FinitePriorityIndex.leader, dif_pos hne]

theorem components (N : V → Finset V) (Δ k : ℕ) (fallback : V) (Φ : ℕ)
    (χ : V → Fin Φ) (U W : Finset V)
    (he : color N Δ k fallback Φ χ U = color N Δ k fallback Φ χ W) :
    χ (FinitePriorityIndex.index N Δ k U fallback).1 =
        χ (FinitePriorityIndex.index N Δ k W fallback).1 ∧
      (FinitePriorityIndex.index N Δ k U fallback).2 =
        (FinitePriorityIndex.index N Δ k W fallback).2 := by
  have hcode : code N Δ k fallback Φ χ U = code N Δ k fallback Φ χ W := Fin.ext he
  have hp := finProdFinEquiv.injective hcode
  exact ⟨congrArg Prod.fst hp,
    (PriorityTableCode.masks ((Δ + 1) ^ k)).injective (congrArg Prod.snd hp)⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem equal_of_touching (Δ k : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (fallback : V) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (U W : Finset V)
    (hU : (G.induce (U : Set V)).Connected ∧ U.card ≤ k)
    (hW : (G.induce (W : Set V)).Connected ∧ W.card ≤ k)
    (he : color (fun v => G.neighborFinset v) Δ k fallback Φ χ U =
      color (fun v => G.neighborFinset v) Δ k fallback Φ χ W)
    (hd : ¬ Disjoint U W) : U = W := by
  let a := FinitePriorityIndex.index (fun v => G.neighborFinset v) Δ k U fallback
  let b := FinitePriorityIndex.index (fun v => G.neighborFinset v) Δ k W fallback
  have hu : U.Nonempty := by obtain ⟨v⟩ := hU.1.nonempty; exact ⟨v.val, v.property⟩
  have hw : W.Nonempty := by obtain ⟨v⟩ := hW.1.nonempty; exact ⟨v.val, v.property⟩
  have ha : a.1 ∈ U := by
    dsimp only [a, FinitePriorityIndex.index]
    rw [FinitePriorityIndex.leader, dif_pos hu]
    exact Finset.min'_mem U hu
  have hb : b.1 ∈ W := by
    dsimp only [b, FinitePriorityIndex.index]
    rw [FinitePriorityIndex.leader, dif_pos hw]
    exact Finset.min'_mem W hw
  have hp := components (fun v => G.neighborFinset v) Δ k fallback Φ χ U W he
  obtain ⟨z, hzU, hzW⟩ := Finset.not_disjoint_iff.mp hd
  have hz : z ∈ NeighborBalls.ball (fun v => G.neighborFinset v) a.1 k := by
    rw [BoundedBallBridge.balls_eq G a.1 k]
    exact BoundedBall.contains_connected G U hU.1 k hU.2 a.1 ha hzU
  have hbz : b.1 ∈ NeighborBalls.ball (fun v => G.neighborFinset v) z k := by
    rw [BoundedBallBridge.balls_eq G z k]
    exact BoundedBall.contains_connected G W hW.1 k hW.2 z hzW hb
  have hnear : b.1 ∈ NeighborBalls.ball (fun v => G.neighborFinset v) a.1 (2 * k) := by
    simpa only [two_mul] using
      NeighborBalls.subball (fun v => G.neighborFinset v) k k a.1 z hz hbz
  have hl : a.1 = b.1 := by
    by_contra hn
    exact hpower a.1 b.1 hn hnear hp.1
  have hab : a = b := Prod.ext hl hp.2
  have hi : LocalPriorityIndex.index G Δ k (⟨U, hU⟩ : LocalPriorityIndex.Domain G k) =
      LocalPriorityIndex.index G Δ k (⟨W, hW⟩ : LocalPriorityIndex.Domain G k) :=
    (FinitePriorityIndex.index_correct G Δ k ⟨U, hU⟩ fallback).symm.trans
      (hab.trans (FinitePriorityIndex.index_correct G Δ k ⟨W, hW⟩ fallback))
  exact congrArg Subtype.val (LocalPriorityIndex.injective G Δ hdeg k hi)

theorem proper (Δ k : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (fallback : V) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (E : Finset (Finset V))
    (hE : ∀ U ∈ E, (G.induce (U : Set V)).Connected ∧ U.card ≤ k) :
    DeterministicPartitionGreedy.Proper E
      (color (fun v => G.neighborFinset v) Δ k fallback Φ χ) := by
  intro U hU W hW he hn
  by_contra hd
  exact hn (equal_of_touching G Δ k hdeg fallback Φ χ hpower U W (hE U hU) (hE W hW) he hd)

theorem proper_eligible (Δ k : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (fallback : V) (Φ : ℕ) (χ : V → Fin Φ)
    (hpower : ∀ u v : V, u ≠ v →
      v ∈ NeighborBalls.ball (fun w => G.neighborFinset w) u (2 * k) → χ u ≠ χ v)
    (S : Finset V) (t : ℕ) :
    DeterministicPartitionGreedy.Proper
      (FiniteEligibility.family (fun v => G.neighborFinset v) S k t)
      (color (fun v => G.neighborFinset v) Δ k fallback Φ χ) := by
  apply proper G Δ k hdeg fallback Φ χ hpower
  intro U hU
  have hh := (FiniteEligibility.mem_family _ S U k t).mp hU
  exact ⟨(FiniteConnectivity.correct G U).mp hh.2.1, hh.2.2.1⟩

theorem color_eq (M : V → Finset V) (F U : Finset V) (x : V)
    (r Δ k : ℕ) (fallback : V) (Φ : ℕ) (χ : V → Fin Φ)
    (hm : ∀ u ∈ F, M u = G.neighborFinset u)
    (hF : NeighborBalls.ball (fun u => G.neighborFinset u) x (r + k) ⊆ F)
    (hU : U ⊆ NeighborBalls.ball (fun u => G.neighborFinset u) x r)
    (hne : U.Nonempty) :
    color M Δ k fallback Φ χ U = color (fun v => G.neighborFinset v) Δ k fallback Φ χ U := by
  have hi := CandidateFrameAgreement.index_eq G M F U x r Δ k fallback hm hF hU hne
  exact congrArg (fun p : V × (Fin ((Δ + 1) ^ k) → Bool) =>
    (finProdFinEquiv (χ p.1, PriorityTableCode.masks ((Δ + 1) ^ k) p.2)).val) hi

end Paper.DeterministicPartitionColors

#print axioms Paper.DeterministicPartitionColors.proper
#print axioms Paper.DeterministicPartitionColors.color_eq
