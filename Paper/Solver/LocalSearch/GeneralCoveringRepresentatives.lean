import Paper.Solver.LocalSearch.GeneralCoveringQuery

/-! Actual fixed finite loop of min-cost mask queries. The private local
input is preserved; answers contain one optional cost/ID representative
for every public mask, with a number depending only on T. -/
namespace Paper.GeneralCoveringRepresentatives
open BroadcastModel
variable {V : Type} [LinearOrder V]

abbrev State (V : Type) (B : ℕ) := GeneralCoveringQuery.Input V B × List (Option (CostTag.Tag V B))

def step {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) :
    Program V (State V B) (State V B) :=
  .seq (ProgramMemory.carry (GeneralCoveringQuery.program C D B T z))
    (.local fun _ _ s => (s.1.1, s.2 ++ [s.1.2]))

def program {b : ℕ} (C : BitCode V b) (D B T : ℕ) :
    List (Fin T → Bool) → Program V (State V B) (State V B)
  | [] => .local fun _ _ s => s
  | z :: zs => .seq (step C D B T z) (program C D B T zs)

def patterns : (T : ℕ) → List (Fin T → Bool)
  | 0 => [Fin.elim0]
  | T + 1 => (patterns T).flatMap (fun f => [Fin.cons false f, Fin.cons true f])

def start (B : ℕ) : Program V (GeneralCoveringQuery.Input V B) (State V B) :=
  .local fun _ _ s => (s, [])

def all {b : ℕ} (C : BitCode V b) (D B T : ℕ) :=
  Program.seq (start B) (program C D B T (patterns T))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem run_step {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool) (s : V → State V B) :
    (step C D B T z).run G s = fun v =>
      (((GeneralCoveringQuery.program C D B T z).run G (fun u => (s u).1) v).1,
        (s v).2 ++ [((GeneralCoveringQuery.program C D B T z).run G (fun u => (s u).1) v).2]) := by
  change Program.run G (.local (fun _ _ s => (s.1.1, s.2 ++ [s.1.2])))
    ((ProgramMemory.carry (GeneralCoveringQuery.program C D B T z)).run G
      (fun v => ((s v).1, (s v).2))) = _
  rw [ProgramMemory.run]
  rfl

theorem metadata {b : ℕ} (C : BitCode V b) (D B T : ℕ) (z : Fin T → Bool)
    (s : V → State V B) (v : V) : ((step C D B T z).run G s v).1 = (s v).1 := by
  rw [run_step, GeneralCoveringQuery.run_program]

theorem patterns_length (T : ℕ) : (patterns T).length = 2 ^ T := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have hlen (l : List (Fin T → Bool)) :
        (l.flatMap (fun f => [(Fin.cons false f : Fin (T + 1) → Bool),
          Fin.cons true f])).length = 2 * l.length := by
      induction l with
      | nil => rfl
      | cons f fs ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
          List.length_nil, ih]; omega
    rw [patterns, hlen, ih, Nat.pow_succ]
    omega

theorem patterns_complete (T : ℕ) (z : Fin T → Bool) : z ∈ patterns T := by
  induction T with
  | zero =>
    have he : z = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [patterns, he]
  | succ T ih =>
    let tail : Fin T → Bool := fun i => z i.succ
    have he : Fin.cons (z 0) tail = z := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail, ih tail, ?_⟩
    cases hz : z 0 with
    | false =>
      have hf : Fin.cons false tail = z := by simpa only [hz] using he
      exact List.mem_cons.mpr (Or.inl hf.symm)
    | true =>
      have ht : Fin.cons true tail = z := by simpa only [hz] using he
      exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr ht.symm))

theorem rounds {b : ℕ} (C : BitCode V b) (D B T : ℕ) (zs : List (Fin T → Bool)) :
    (program C D B T zs).rounds = zs.length * (4 * D + 1) := by
  induction zs with
  | nil => simp [program, Program.rounds]
  | cons z zs ih =>
    simp only [program, step, Program.rounds, ProgramMemory.rounds, GeneralCoveringQuery.rounds, ih,
      List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem maxBits {b : ℕ} (C : BitCode V b) (D B T : ℕ) (zs : List (Fin T → Bool)) :
    (program C D B T zs).maxBits ≤ max (2 * b + B + 3) (D + 2) := by
  induction zs with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
    apply max_le ?_ ih
    simpa only [step, Program.maxBits, ProgramMemory.maxBits, Nat.max_zero] using
      GeneralCoveringQuery.maxBits C D B T z
end Paper.GeneralCoveringRepresentatives
