import Paper.Averaging.Tasks.TaskAggregate
import Paper.Preliminaries.PayloadFlood
import Paper.Preliminaries.TreeRoutes

/-! Actual bounded-bit task query: aggregate a coded monoid payload and
broadcast the answer to every active physical vertex of the task. -/
namespace Paper.TaskAllReduce
open BroadcastModel
variable {V A : Type} [LinearOrder V] [AddCommMonoid A]

def seed {D : ℕ} : Program V (TreeAggregateRound.State V A D) (PayloadFlood.State A) :=
  .local fun _ _ s => (s.1.active,
    if s.1.active && s.1.parent.isNone then some s.2 else none)

def program {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    Program V (Bool × A) (PayloadFlood.State A) :=
  .seq (TaskAggregate.program C F D) (.seq seed (PayloadFlood.program F D))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem seed_eq {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ)
    (active : V → Bool) (root : V)
    (h : LeaderTreeCorrect.Spec G active D root ((LeaderTree.program C D).run G active))
    (har : active root = true) (weights : V → A)
    (hz : ∀ v, active v = false → weights v = 0) :
    seed.run G ((TaskAggregate.program C F D).run G (fun v => (active v, weights v))) =
      fun v => (active v, if v = root then some (∑ u, weights u) else none) := by
  have hn : ∀ v, ((TaskAggregate.program C F D).run G
      (fun u => (active u, weights u)) v).1 = (LeaderTree.program C D).run G active v := by
    intro v
    rw [TaskAggregate.run_eq]
    exact (TreeAggregate.correct G C F h weights hz).1 v
  have hm := (TaskAggregate.correct G C F D active root h weights hz).1
  funext v
  change (((TaskAggregate.program C F D).run G (fun u => (active u, weights u)) v).1.active,
    if ((TaskAggregate.program C F D).run G (fun u => (active u, weights u)) v).1.active &&
      ((TaskAggregate.program C F D).run G (fun u => (active u, weights u)) v).1.parent.isNone
    then some (((TaskAggregate.program C F D).run G (fun u => (active u, weights u)) v).2)
    else none) = _
  rw [hn, h.active]
  by_cases hv : v = root
  · subst v
    simp [har, h.root_parent, hm]
  · cases ha : active v with
    | false => simp [ha, hv]
    | true =>
      obtain ⟨u, hu⟩ := h.parent_exists v ha hv
      simp [ha, hu, hv]

theorem correct {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ)
    (active : V → Bool) (root : V)
    (h : LeaderTreeCorrect.Spec G active D root ((LeaderTree.program C D).run G active))
    (har : active root = true) (weights : V → A)
    (hz : ∀ v, active v = false → weights v = 0) :
    ∀ v, active v = true →
      ((program C F D).run G (fun u => (active u, weights u)) v).2 = some (∑ u, weights u) := by
  change ∀ v, active v = true → ((PayloadFlood.program F D).run G
    (seed.run G ((TaskAggregate.program C F D).run G (fun u => (active u, weights u)))) v).2 = _
  rw [seed_eq G C F D active root h har weights hz]
  let S : V → PayloadFlood.State A := fun v =>
    (active v, if v = root then some (∑ u, weights u) else none)
  have hi : ∀ v, (S v).2 = none ∨ (S v).2 = some (∑ u, weights u) := by
    intro v
    by_cases hv : v = root <;> simp [S, hv]
  exact (PayloadFlood.correct G S F D root (∑ u, weights u) hi
    (by simp [S]) (fun v hv => TreeRoutes.routes h hv)).1

theorem physical_task {b c : ℕ} (C : BitCode V b) (F : BitCode A c)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (weights : V → A)
    (hz : ∀ v, v ∉ PhysicalTasks.vertices G D R L Q I → weights v = 0) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      ((program C F (4 * k)).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), weights u)) v).2 =
          some (∑ u, weights u) := by
  obtain ⟨hne, hs, _, _⟩ := TaskTree.spec G C D R L Q I hI k hsize
  have har : decide ((PhysicalTasks.vertices G D R L Q I).min' hne ∈
      PhysicalTasks.vertices G D R L Q I) = true :=
    decide_eq_true (Finset.min'_mem _ hne)
  intro v hv
  exact correct G C F (4 * k) _ _ hs har weights
    (fun u hu => hz u (by simpa using hu)) v (decide_eq_true hv)

theorem rounds {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    (program C F D).rounds = 4 * D + 1 := by
  have hf : (PayloadFlood.program (V := V) F D).rounds = D := by
    simp only [PayloadFlood.program, PayloadFlood.step, Program.iterate_rounds,
      Program.rounds, Nat.mul_one]
  simp only [program, Program.rounds, TaskAggregate.rounds, seed, hf]
  omega

theorem maxBits {b c : ℕ} (C : BitCode V b) (F : BitCode A c) (D : ℕ) :
    (program C F D).maxBits ≤ max (b + c + 1) (D + 2) := by
  have hf : (PayloadFlood.program (V := V) F D).maxBits ≤ c + 1 :=
    Program.iterate_maxBits (PayloadFlood.step F) D
  apply max_le (TaskAggregate.maxBits C F D)
  apply max_le (Nat.zero_le _)
  exact hf.trans ((by omega : c + 1 ≤ b + c + 1).trans (le_max_left _ _))
end Paper.TaskAllReduce
