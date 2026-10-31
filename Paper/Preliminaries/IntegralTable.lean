import Paper.Solver.LocalSearch.TabularSearch

/-! Pure finite arithmetic completeness of table search: integral copies
can be replaced by returned representatives preserving rows and cost.
The graph/API bridge is supplied by actual mask-query correctness. -/
namespace Paper.IntegralTable
open TabularSearch
variable {V : Type*} [Fintype V] [DecidableEq V] {T : ℕ}

def erase (p : V → ℕ) (v u : V) : ℕ := p u - if u = v then 1 else 0

def mass (row : V → Fin T → Bool) (p : V → ℕ) (i : Fin T) : ℕ :=
  ∑ v, (if row v i then 1 else 0) * p v

def cost (c : V → ℕ) (p : V → ℕ) : ℕ := ∑ v, c v * p v

theorem erase_le (p : V → ℕ) (v u : V) : erase p v u ≤ p u := Nat.sub_le _ _

theorem restore (p : V → ℕ) (v : V) (hv : 0 < p v) (u : V) :
    p u = erase p v u + if u = v then 1 else 0 := by
  by_cases hu : u = v
  · subst u
    simp [erase] <;> omega
  · simp [erase, hu]

theorem sum_restore (p : V → ℕ) (v : V) (hv : 0 < p v) :
    ∑ u, p u = (∑ u, erase p v u) + 1 := by
  calc
    _ = ∑ u, (erase p v u + if u = v then 1 else 0) :=
      Finset.sum_congr rfl (fun u _ => restore p v hv u)
    _ = _ := by simp [Finset.sum_add_distrib]

theorem mass_restore (row : V → Fin T → Bool) (p : V → ℕ) (v : V) (hv : 0 < p v) (i : Fin T) :
    mass row p i = mass row (erase p v) i + if row v i then 1 else 0 := by
  calc
    _ = ∑ u, (if row u i then 1 else 0) * (erase p v u + if u = v then 1 else 0) :=
      Finset.sum_congr rfl (fun u _ => congrArg (fun n => (if row u i then 1 else 0) * n) (restore p v hv u))
    _ = _ := by simp [mass, mul_add, Finset.sum_add_distrib, mul_ite]

theorem cost_restore (c : V → ℕ) (p : V → ℕ) (v : V) (hv : 0 < p v) :
    cost c p = cost c (erase p v) + c v := by
  calc
    _ = ∑ u, c u * (erase p v u + if u = v then 1 else 0) :=
      Finset.sum_congr rfl (fun u _ => congrArg (fun n => c u * n) (restore p v hv u))
    _ = _ := by simp [cost, mul_add, Finset.sum_add_distrib, mul_ite]

theorem zero_word (alphabet : List (Entry V T)) (row : V → Fin T → Bool) (c : V → ℕ)
    (m : ℕ) (target : Fin T → ℕ) (p : V → ℕ) (hz : ∑ v, p v = 0)
    (hcov : ∀ i, target i ≤ mass row p i) :
    ∃ w : List (Entry V T), w.length ≤ m ∧ (∀ e ∈ w, e ∈ alphabet) ∧
      (∀ i, target i ≤ coverage w i) ∧ price w ≤ cost c p := by
  have hp0 : ∀ v, p v = 0 := by
    intro v
    have hle : p v ≤ ∑ u, p u :=
      Finset.single_le_sum (fun u _ => Nat.zero_le (p u)) (Finset.mem_univ v)
    omega
  refine ⟨[], Nat.zero_le _, by simp, ?_, Nat.zero_le _⟩
  intro i
  simpa [mass, hp0, coverage] using hcov i

theorem word_exists (alphabet : List (Entry V T)) (row : V → Fin T → Bool) (c : V → ℕ)
    (m : ℕ) (target : Fin T → ℕ) (p : V → ℕ) (hsize : ∑ v, p v ≤ m)
    (hcov : ∀ i, target i ≤ mass row p i)
    (hrep : ∀ v, 0 < p v → ∃ e ∈ alphabet, e.row = row v ∧ e.price ≤ c v) :
    ∃ w : List (Entry V T), w.length ≤ m ∧ (∀ e ∈ w, e ∈ alphabet) ∧
      (∀ i, target i ≤ coverage w i) ∧ price w ≤ cost c p := by
  induction m generalizing target p with
  | zero => exact zero_word alphabet row c 0 target p (by omega) hcov
  | succ m ih =>
    by_cases hz : ∑ v, p v = 0
    · exact zero_word alphabet row c (m + 1) target p hz hcov
    · obtain ⟨v, _, hv⟩ := Finset.sum_pos_iff.mp (Nat.pos_of_ne_zero hz)
      let p' := erase p v
      let target' : Fin T → ℕ := fun i => target i - if row v i then 1 else 0
      have hsize' : ∑ u, p' u ≤ m := by
        dsimp only [p']
        have hh := sum_restore p v hv
        omega
      have hcov' : ∀ i, target' i ≤ mass row p' i := by
        intro i
        have hh := mass_restore row p v hv i
        have hc := hcov i
        dsimp only [target', p']
        omega
      have hrep' : ∀ u, 0 < p' u → ∃ e ∈ alphabet, e.row = row u ∧ e.price ≤ c u := by
        intro u hu
        exact hrep u (lt_of_lt_of_le hu (erase_le p v u))
      obtain ⟨w, hlen, hall, hwcov, hwcost⟩ := ih target' p' hsize' hcov' hrep'
      obtain ⟨e, he, herow, hecost⟩ := hrep v hv
      refine ⟨e :: w, by simpa only [List.length_cons] using Nat.add_le_add_right hlen 1,
        ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact he
        · exact hall a ha
      · intro i
        have hh := hwcov i
        change target i ≤ (if e.row i then 1 else 0) + coverage w i
        rw [herow]
        dsimp only [target'] at hh
        omega
      · have hh := cost_restore c p v hv
        change e.price + price w ≤ cost c p
        dsimp only [p'] at hwcost
        omega

theorem choose_complete (alphabet : List (Entry V T)) (row : V → Fin T → Bool) (c : V → ℕ)
    (m : ℕ) (target : Fin T → ℕ) (p : V → ℕ) (hsize : ∑ v, p v ≤ m)
    (hcov : ∀ i, target i ≤ mass row p i)
    (hrep : ∀ v, 0 < p v → ∃ e ∈ alphabet, e.row = row v ∧ e.price ≤ c v) :
    ∃ w, TabularSearch.choose alphabet m target = some w ∧ price w ≤ cost c p := by
  obtain ⟨w, hlen, hall, hwcov, hwcost⟩ := word_exists alphabet row c m target p hsize hcov hrep
  obtain ⟨r, hr, hcost⟩ := TabularSearch.choose_complete alphabet m target w hlen hall hwcov
  exact ⟨r, hr, hcost.trans hwcost⟩
end Paper.IntegralTable
