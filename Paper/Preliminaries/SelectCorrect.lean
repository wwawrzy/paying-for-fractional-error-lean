import Paper.Preliminaries.SelectStep

/-! Exact execution of the repeated minimum program and its complete
enumeration guarantee for bounded eligible candidate sets. -/
namespace Paper.SelectCorrect
open BroadcastModel SelectProtocol SelectStep
variable {V : Type} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem invariant {b : ℕ} (C : BitCode V b) (D : ℕ) (active eligible : V → Bool) (root : V)
    (h : LeaderTreeCorrect.Spec G active D root ((LeaderTree.program C D).run G active))
    (har : active root = true) (n : ℕ) :
    (∀ v, ((program C D n).run G (fun u => (active u, eligible u)) v).active = active v ∧
      ((program C D n).run G (fun u => (active u, eligible u)) v).eligible = eligible v) ∧
    (∀ v, active v = true → ((program C D n).run G
      (fun u => (active u, eligible u)) v).chosen = MinimumList.run (candidates active eligible) n) := by
  induction n with
  | zero => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
  | succ n ih =>
    rw [run_succ]
    let s := (program C D n).run G (fun u => (active u, eligible u))
    have ha : ∀ v, (s v).active = active v := fun v => (ih.1 v).1
    have he : ∀ v, (s v).eligible = eligible v := fun v => (ih.1 v).2
    refine ⟨fun v => ⟨((metadata G C D s v).1).trans (ha v),
      ((metadata G C D s v).2).trans (he v)⟩, ?_⟩
    exact SelectStep.correct G C D active eligible root h har
      (MinimumList.run (candidates active eligible) n) s ha he ih.2

theorem complete {b : ℕ} (C : BitCode V b) (D : ℕ) (active eligible : V → Bool) (root : V)
    (h : LeaderTreeCorrect.Spec G active D root ((LeaderTree.program C D).run G active))
    (har : active root = true) (n : ℕ) (hn : (candidates active eligible).card ≤ n) :
    ∀ v, active v = true →
      (((program C D n).run G (fun u => (active u, eligible u)) v).chosen.toFinset =
        candidates active eligible) ∧
      ((program C D n).run G (fun u => (active u, eligible u)) v).chosen.Nodup ∧
      ((program C D n).run G (fun u => (active u, eligible u)) v).chosen.length ≤ n := by
  intro v hv
  rw [(invariant G C D active eligible root h har n).2 v hv]
  exact ⟨MinimumList.complete _ n hn, MinimumList.run_nodup _ n, MinimumList.run_length _ n⟩

theorem rounds {b : ℕ} (C : BitCode V b) (D n : ℕ) :
    (program C D n).rounds = n * (4 * D + 1) := by
  have hs : (step C D).rounds = 4 * D + 1 := by
    simp [step, prepare, finish, Program.rounds, ProgramMemory.rounds,
      TaskQueries.minimumProgram, TaskAllReduce.rounds]
  simp only [program, Program.rounds, start, Program.iterate_rounds, hs, Nat.zero_add]

theorem maxBits {b : ℕ} (C : BitCode V b) (D n : ℕ) :
    (program C D n).maxBits ≤ max (2 * b + 2) (D + 2) := by
  have hs : (step C D).maxBits = (TaskQueries.minimumProgram C D).maxBits := by
    simp [step, prepare, finish, Program.maxBits, ProgramMemory.maxBits]
  have hb : (TaskQueries.minimumProgram C D).maxBits ≤ max (2 * b + 2) (D + 2) := by
    have hh := TaskAllReduce.maxBits C (MinimumPayload.code C) D
    have hw : b + (b + 1) + 1 = 2 * b + 2 := by omega
    rw [hw] at hh
    exact hh
  apply max_le (Nat.zero_le _)
  exact (Program.iterate_maxBits (step C D) n).trans (hs.trans_le hb)

theorem physical_task {b : ℕ} (C : BitCode V b)
    (D R : Finset V) (L : ℕ) (Q : Finset D) (I : Finset (OwnerTasks.Low D Q))
    (hI : ((OwnerTasks.graph G D R L Q).induce (I : Set (OwnerTasks.Low D Q))).Connected)
    (k : ℕ) (hsize : I.card ≤ k) (eligible : V → Bool) (n : ℕ)
    (hn : ((PhysicalTasks.vertices G D R L Q I).filter (fun v => eligible v = true)).card ≤ n) :
    ∀ v ∈ PhysicalTasks.vertices G D R L Q I,
      (((program C (4 * k) n).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), eligible u)) v).chosen.toFinset =
          (PhysicalTasks.vertices G D R L Q I).filter (fun u => eligible u = true)) ∧
      ((program C (4 * k) n).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), eligible u)) v).chosen.Nodup ∧
      ((program C (4 * k) n).run G
        (fun u => (decide (u ∈ PhysicalTasks.vertices G D R L Q I), eligible u)) v).chosen.length ≤ n := by
  obtain ⟨hne, hs, _, _⟩ := TaskTree.spec G C D R L Q I hI k hsize
  have he : candidates (fun v => decide (v ∈ PhysicalTasks.vertices G D R L Q I)) eligible =
      (PhysicalTasks.vertices G D R L Q I).filter (fun v => eligible v = true) := by
    ext v
    simp [candidates]
  have har : decide ((PhysicalTasks.vertices G D R L Q I).min' hne ∈
      PhysicalTasks.vertices G D R L Q I) = true := decide_eq_true (Finset.min'_mem _ hne)
  intro v hv
  have hc := complete G C (4 * k) _ eligible _ hs har n (by simpa only [he] using hn)
    v (decide_eq_true hv)
  simpa only [he] using hc
end Paper.SelectCorrect
