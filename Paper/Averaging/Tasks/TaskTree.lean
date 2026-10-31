import Paper.Preliminaries.LeaderTreeCorrect
import Paper.Averaging.Tasks.TaskDiameter

/-! An actual public-ID broadcast program constructs the physical task
tree in 8k+1 rounds, including leader election. -/
namespace Paper.TaskTree
open BroadcastModel OwnerTasks
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem induced {b : ℕ} (C : BitCode V b) (H : Finset V) (hne : H.Nonempty)
    (D : ℕ) (hd : ∀ x y : ↥(H : Set V), ∃ p : (G.induce (H : Set V)).Walk x y,
      p.length ≤ D) :
    LeaderTreeCorrect.Spec G (fun v => decide (v ∈ H)) D (H.min' hne)
      ((LeaderTree.program C D).run G (fun v => decide (v ∈ H))) ∧
      (LeaderTree.program C D).rounds = 2 * D + 1 ∧
      (LeaderTree.program C D).maxBits ≤ max (b + 1) (D + 2) := by
  let root : ↥(H : Set V) := ⟨H.min' hne, Finset.min'_mem H hne⟩
  have har : decide (root.val ∈ H) = true := decide_eq_true root.property
  have hmin : ∀ v, decide (v ∈ H) = true → root.val ≤ v :=
    fun v hv => Finset.min'_le H v (of_decide_eq_true hv)
  have hdiam : ∀ v, decide (v ∈ H) = true → ∃ p : G.Walk v root.val,
      p.length ≤ D ∧ ∀ z ∈ p.support, decide (z ∈ H) = true := by
    intro v hv
    obtain ⟨p, hp⟩ := hd ⟨v, of_decide_eq_true hv⟩ root
    let f := (SimpleGraph.Embedding.induce (H : Set V) : G.induce (H : Set V) ↪g G).toHom
    refine ⟨p.map f, (SimpleGraph.Walk.length_map f p).trans_le hp, ?_⟩
    intro z hz
    have hz' : z ∈ p.support.map f := (SimpleGraph.Walk.support_map f p) ▸ hz
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hz'
    exact decide_eq_true u.property
  exact ⟨LeaderTreeCorrect.correct G _ C D root.val har hmin hdiam,
    LeaderTree.rounds C D, LeaderTree.maxBits C D⟩

theorem spec {b : ℕ} (C : BitCode V b) (D R : Finset V) (L : ℕ) (Q : Finset D)
    (I : Finset (Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) :
    ∃ hne : (PhysicalTasks.vertices G D R L Q I).Nonempty,
      LeaderTreeCorrect.Spec G (fun v => decide (v ∈ PhysicalTasks.vertices G D R L Q I))
        (4 * k) ((PhysicalTasks.vertices G D R L Q I).min' hne)
        ((LeaderTree.program C (4 * k)).run G
          (fun v => decide (v ∈ PhysicalTasks.vertices G D R L Q I))) ∧
      (LeaderTree.program C (4 * k)).rounds = 8 * k + 1 ∧
      (LeaderTree.program C (4 * k)).maxBits ≤ max (b + 1) (4 * k + 2) := by
  obtain ⟨hc, hd⟩ := TaskDiameter.spec G D R L Q I hI k hsize
  have hne : (PhysicalTasks.vertices G D R L Q I).Nonempty := by
    obtain ⟨v⟩ := hc.nonempty
    exact ⟨v.val, v.property⟩
  obtain ⟨hs, hr, hb⟩ := induced G C _ hne (4 * k) hd
  exact ⟨hne, hs, by omega, hb⟩
end Paper.TaskTree
