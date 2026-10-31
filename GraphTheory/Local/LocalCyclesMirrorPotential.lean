import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Algebraic core for weighted undirected-cycle automata.
This file proves finite-walk facts, not a distributed complexity classification.
No production modules or catalog declarations are changed.
-/

noncomputable section

namespace LocalCycles

variable {Q : Type*}

/-- An arc cost normalized by target mean `b` and potential `p`. -/
def reduced (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ) (u v : Q) : ℝ :=
  c u v - b + p u - p v

/-- Antisymmetrization with respect to reversal of automaton states. -/
def mirrorPotential (rev : Q → Q) (p : Q → ℝ) (u : Q) : ℝ :=
  (p u - p (rev u)) / 2

theorem mirrorPotential_antisymm (rev : Q → Q)
    (hinv : Function.Involutive rev) (p : Q → ℝ) (u : Q) :
    mirrorPotential rev p (rev u) = -mirrorPotential rev p u := by
  simp only [mirrorPotential, hinv u]
  ring

theorem reduced_mirror_average (rev : Q → Q) (c : Q → Q → ℝ)
    (b : ℝ) (p : Q → ℝ) (u v : Q)
    (hsym : c (rev v) (rev u) = c u v) :
    reduced c b (mirrorPotential rev p) u v =
      (reduced c b p u v + reduced c b p (rev v) (rev u)) / 2 := by
  simp only [reduced, mirrorPotential, hsym]
  ring

/-- A feasible potential can be made antisymmetric without losing feasibility. -/
theorem mirrorPotential_feasible (E : Q → Q → Prop) (rev : Q → Q)
    (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ)
    (hrev : ∀ u v, E u v → E (rev v) (rev u))
    (hsym : ∀ u v, E u v → c (rev v) (rev u) = c u v)
    (hfeas : ∀ u v, E u v → 0 ≤ reduced c b p u v) :
    ∀ u v, E u v → 0 ≤ reduced c b (mirrorPotential rev p) u v := by
  intro u v huv
  rw [reduced_mirror_average rev c b p u v (hsym u v huv)]
  exact div_nonneg (add_nonneg (hfeas u v huv)
    (hfeas (rev v) (rev u) (hrev u v huv))) (by norm_num)

/-- The new reduced costs respect reversal, so their zero-cost graph does too. -/
theorem reduced_mirror_eq (rev : Q → Q) (hinv : Function.Involutive rev)
    (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ) (u v : Q)
    (hsym : c (rev v) (rev u) = c u v) :
    reduced c b (mirrorPotential rev p) (rev v) (rev u) =
      reduced c b (mirrorPotential rev p) u v := by
  simp only [reduced, hsym, mirrorPotential_antisymm rev hinv p]
  ring

inductive Walk (E : Q → Q → Prop) : Q → Q → Type _
  | nil (u : Q) : Walk E u u
  | cons {u v w : Q} (h : E u v) (tail : Walk E v w) : Walk E u w

namespace Walk

variable {E : Q → Q → Prop} {u v w : Q}

def length : {u v : Q} → Walk E u v → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => tail.length + 1

def cost (c : Q → Q → ℝ) : {u v : Q} → Walk E u v → ℝ
  | _, _, .nil _ => 0
  | _, _, @cons _ _ a b _ _ tail => c a b + tail.cost c

def append : {u v w : Q} → Walk E u v → Walk E v w → Walk E u w
  | _, _, _, .nil _, b => b
  | _, _, _, .cons h tail, b => .cons h (append tail b)

def Tight (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ) : {u v : Q} → Walk E u v → Prop
  | _, _, .nil _ => True
  | _, _, @cons _ _ a d _ _ tail => reduced c b p a d = 0 ∧ tail.Tight c b p

theorem cost_append (c : Q → Q → ℝ) (a : Walk E u v) (b : Walk E v w) :
    (a.append b).cost c = a.cost c + b.cost c := by
  induction a with
  | nil => simp [append, cost]
  | cons h tail ih => simp [append, cost, ih, add_assoc]

theorem length_append (a : Walk E u v) (b : Walk E v w) :
    (a.append b).length = a.length + b.length := by
  induction a with
  | nil => simp [append, length]
  | cons h tail ih => simp [append, length, ih]; omega

/-- Reduced costs telescope along an actual valid walk. -/
theorem cost_reduced (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ)
    (a : Walk E u v) :
    a.cost (reduced c b p) = a.cost c - b * a.length + p u - p v := by
  induction a with
  | nil => simp [cost, length]
  | cons h tail ih =>
    simp only [cost, length, Nat.cast_add, Nat.cast_one, reduced] at *
    rw [ih]
    ring

theorem cost_nonneg (c : Q → Q → ℝ)
    (hnonneg : ∀ a d, E a d → 0 ≤ c a d) (a : Walk E u v) :
    0 ≤ a.cost c := by
  induction a with
  | nil => simp [cost]
  | cons h tail ih => exact add_nonneg (hnonneg _ _ h) ih

theorem reduced_zero_iff_tight (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ)
    (hfeas : ∀ a d, E a d → 0 ≤ reduced c b p a d) (a : Walk E u v) :
    a.cost (reduced c b p) = 0 ↔ a.Tight c b p := by
  induction a with
  | nil => simp [cost, Tight]
  | cons h tail ih =>
    change reduced c b p _ _ + tail.cost (reduced c b p) = 0 ↔
      reduced c b p _ _ = 0 ∧ tail.Tight c b p
    rw [← ih]
    exact add_eq_zero_iff_of_nonneg (hfeas _ _ h)
      (cost_nonneg (reduced c b p) hfeas tail)

/-- Exact mean on a closed walk forces every traversed arc to be tight. -/
theorem closed_cost_eq_iff_tight (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ)
    (hfeas : ∀ a d, E a d → 0 ≤ reduced c b p a d) (a : Walk E u u) :
    a.cost c = b * a.length ↔ a.Tight c b p := by
  rw [← reduced_zero_iff_tight c b p hfeas a, cost_reduced]
  constructor <;> intro h <;> linarith

/-- A nonpositive closed mirror trip is tight if every reduced arc cost is nonnegative. -/
theorem mirror_trip_tight (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ)
    (hfeas : ∀ a d, E a d → 0 ≤ reduced c b p a d)
    (a : Walk E u v) (d : Walk E v u)
    (hcost : a.cost c + d.cost c ≤ b * (a.length + d.length)) :
    (a.append d).Tight c b p := by
  apply (closed_cost_eq_iff_tight c b p hfeas (a.append d)).mp
  have hn := cost_nonneg (reduced c b p) hfeas (a.append d)
  rw [cost_reduced] at hn
  rw [cost_append, length_append] at hn ⊢
  push_cast at hn ⊢
  linarith


/-- Total excess above a target mean, including endpoint effects. -/
def excess (c : Q → Q → ℝ) (b : ℝ) (a : Walk E u v) : ℝ :=
  a.cost c - b * a.length

theorem excess_append (c : Q → Q → ℝ) (b : ℝ)
    (a : Walk E u v) (d : Walk E v w) :
    (a.append d).excess c b = a.excess c b + d.excess c b := by
  simp only [excess, cost_append, length_append, Nat.cast_add]
  ring

def iterate (a : Walk E u u) : ℕ → Walk E u u
  | 0 => .nil u
  | k + 1 => a.append (a.iterate k)

theorem excess_iterate (c : Q → Q → ℝ) (b : ℝ)
    (a : Walk E u u) (k : ℕ) :
    (a.iterate k).excess c b = k * a.excess c b := by
  induction k with
  | zero => simp [iterate, excess, cost, length]
  | succ k ih =>
    simp only [iterate, excess_append, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- Repeating a negative-excess loop pays any fixed connector cost. -/
theorem negative_excursion_pays (c : Q → Q → ℝ) (b : ℝ)
    (entry : Walk E u v) (cycle : Walk E v v) (exit : Walk E v w)
    (hnegative : cycle.excess c b < 0) (budget : ℝ) :
    ∃ k : ℕ, ((entry.append (cycle.iterate k)).append exit).excess c b ≤ budget := by
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((entry.excess c b + exit.excess c b - budget) / (-cycle.excess c b))
  have hpos : 0 < -cycle.excess c b := by linarith
  have hp := (div_lt_iff₀ hpos).mp hk
  refine ⟨k, ?_⟩
  rw [excess_append, excess_append, excess_iterate]
  nlinarith

/-- A cheaper cycle anywhere along accessible paths yields a mirror-trip certificate. -/
theorem negative_cycle_mirror_certificate (c : Q → Q → ℝ) (b : ℝ)
    (rev : Q → Q) (q z : Q)
    (entry : Walk E q z) (cycle : Walk E z z) (exit : Walk E z (rev q))
    (back : Walk E (rev q) q) (hnegative : cycle.excess c b < 0) :
    ∃ forward : Walk E q (rev q), forward.excess c b + back.excess c b ≤ 0 := by
  obtain ⟨k, hk⟩ := negative_excursion_pays c b entry cycle exit hnegative
    (-back.excess c b)
  exact ⟨(entry.append (cycle.iterate k)).append exit, by linarith⟩

/-- Tight mirror connectors have zero combined excess despite possible endpoint potentials. -/
theorem tight_mirror_certificate (c : Q → Q → ℝ) (b : ℝ) (p : Q → ℝ)
    (hfeas : ∀ a d, E a d → 0 ≤ reduced c b p a d)
    (a : Walk E u v) (d : Walk E v u)
    (ha : a.Tight c b p) (hd : d.Tight c b p) :
    a.excess c b + d.excess c b = 0 := by
  have ha' := (reduced_zero_iff_tight c b p hfeas a).mpr ha
  have hd' := (reduced_zero_iff_tight c b p hfeas d).mpr hd
  rw [cost_reduced] at ha' hd'
  simp only [excess]
  linarith


theorem length_iterate (a : Walk E u u) (k : ℕ) :
    (a.iterate k).length = k * a.length := by
  induction k with
  | zero => simp [iterate, length]
  | succ k ih => simp [iterate, length_append, ih, Nat.add_mul, Nat.add_comm]

/-- Exact optimum on the arithmetic progression generated by a minimum-mean
closed walk. No claim is made about other residue classes. -/
theorem optimal_on_multiples (c : Q → Q → ℝ) (β : ℝ)
    (a : Walk E u u) (ha : a.cost c = β * a.length)
    (hmin : ∀ (v : Q) (z : Walk E v v), β * z.length ≤ z.cost c)
    (k : ℕ) :
    ∃ z : Walk E u u, z.length = k * a.length ∧
      z.cost c = β * (k * a.length : ℕ) ∧
      ∀ (v : Q) (b : Walk E v v), b.length = k * a.length → z.cost c ≤ b.cost c := by
  have hzero : a.excess c β = 0 := by simp [excess, ha]
  have hz := excess_iterate c β a k
  rw [hzero, mul_zero] at hz
  have hcost : (a.iterate k).cost c = β * (k * a.length : ℕ) := by
    simpa only [excess, length_iterate] using sub_eq_zero.mp hz
  refine ⟨a.iterate k, length_iterate a k, hcost, ?_⟩
  intro v b hb
  rw [hcost, ← hb]
  exact hmin v b

/-- Every sufficiently large number is a nonnegative combination of consecutive lengths. -/
theorem consecutive_decomposition (a n : ℕ) (ha : 0 < a) (hn : a * a ≤ n) :
    ∃ i j : ℕ, i * a + j * (a + 1) = n := by
  have hdiv : a ≤ n / a := (Nat.le_div_iff_mul_le ha).mpr hn
  have hmod : n % a < a := Nat.mod_lt n ha
  have hsub : (n / a - n % a) + n % a = n / a := Nat.sub_add_cancel (by omega)
  refine ⟨n / a - n % a, n % a, ?_⟩
  calc
    (n / a - n % a) * a + n % a * (a + 1) =
      ((n / a - n % a) + n % a) * a + n % a := by ring
    _ = n / a * a + n % a := by rw [hsub]
    _ = n := by simpa only [Nat.mul_comm] using Nat.div_add_mod n a

/-- Consecutive returning-walk lengths give an explicit flexibility threshold. -/
theorem consecutive_walks_flexible (a d : Walk E u u)
    (ha : 0 < a.length) (hd : d.length = a.length + 1) :
    ∀ n ≥ a.length * a.length, ∃ z : Walk E u u, z.length = n := by
  intro n hn
  obtain ⟨i, j, hij⟩ := consecutive_decomposition a.length n ha hn
  refine ⟨(a.iterate i).append (d.iterate j), ?_⟩
  simpa only [length_append, length_iterate, hd] using hij

/-- One flexible state and paths in both directions give all four long fillings. -/
theorem flexible_pair_fillings (K : ℕ)
    (hflex : ∀ n ≥ K, ∃ z : Walk E u u, z.length = n)
    (forward : Walk E u v) (back : Walk E v u) :
    ∀ n ≥ K + forward.length + back.length,
      (∃ z : Walk E u u, z.length = n) ∧
      (∃ z : Walk E u v, z.length = n) ∧
      (∃ z : Walk E v u, z.length = n) ∧
      (∃ z : Walk E v v, z.length = n) := by
  intro n hn
  refine ⟨hflex n (by omega), ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hflex (n - forward.length) (by omega)
    refine ⟨z.append forward, ?_⟩
    rw [length_append, hz]
    omega
  · obtain ⟨z, hz⟩ := hflex (n - back.length) (by omega)
    refine ⟨back.append z, ?_⟩
    rw [length_append, hz]
    omega
  · obtain ⟨z, hz⟩ := hflex (n - back.length - forward.length) (by omega)
    refine ⟨(back.append z).append forward, ?_⟩
    rw [length_append, length_append, hz]
    omega

/-- Frozen original and reflected anchors yield both mirror connectors. -/
theorem reflected_anchor_connectors {x z : Q} (rev : Q → Q)
    (xz : Walk E x z) (zx : Walk E z x)
    (rz : Walk E (rev x) z) (zr : Walk E z (rev x)) :
    Nonempty (Walk E x (rev x)) ∧ Nonempty (Walk E (rev x) x) :=
  ⟨⟨xz.append zr⟩, ⟨rz.append zx⟩⟩


def castRight (a : Walk E u v) (h : v = w) : Walk E u w := h ▸ a

theorem length_castRight (a : Walk E u v) (h : v = w) :
    (a.castRight h).length = a.length := by
  cases h
  rfl

/-- Finite-state consequence of the original and relocated protected views.
The hypotheses are walk witnesses, not an implementation of the LOCAL surgery. -/
theorem finite_surgery_core [Fintype Q]
    (states : Fin (Fintype.card Q + 1) → Q)
    (paths : ∀ i j, Walk E (states i) (states j))
    (moved : ∀ i j, i ≠ j → Walk E (states i) (states j))
    (hpositive : ∀ i j, i ≠ j → 0 < (paths i j).length)
    (hshift : ∀ i j (h : i ≠ j), (moved i j h).length = (paths i j).length + 1)
    (root : Fin (Fintype.card Q + 1)) (rev : Q → Q)
    (forward : Walk E (states root) (rev (states root)))
    (back : Walk E (rev (states root)) (states root)) :
    ∃ K : ℕ, ∀ n ≥ K,
      (∃ z : Walk E (states root) (states root), z.length = n) ∧
      (∃ z : Walk E (states root) (rev (states root)), z.length = n) ∧
      (∃ z : Walk E (rev (states root)) (states root), z.length = n) ∧
      (∃ z : Walk E (rev (states root)) (rev (states root)), z.length = n) := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt states (by simp)
  let a := (paths i j).castRight heq.symm
  let d := (moved i j hij).castRight heq.symm
  have ha : 0 < a.length := by simpa only [a, length_castRight] using hpositive i j hij
  have hd : d.length = a.length + 1 := by
    simpa only [a, d, length_castRight] using hshift i j hij
  have hflex := consecutive_walks_flexible a d ha hd
  let Kroot := a.length * a.length + (paths i root).length + (paths root i).length
  have hroot : ∀ n ≥ Kroot, ∃ z : Walk E (states root) (states root), z.length = n := by
    intro n hn
    exact (flexible_pair_fillings (a.length * a.length) hflex
      (paths i root) (paths root i) n hn).2.2.2
  exact ⟨Kroot + forward.length + back.length,
    flexible_pair_fillings Kroot hroot forward back⟩

end Walk

namespace OpenEndpoint

abbrev State := Fin 5

def orientation (u : State) : Prop := u.val < 2

def edge (u v : State) : Prop := orientation u ↔ orientation v

def mirror (u : State) : State := if u = 0 then 1 else if u = 1 then 0 else u

def weight (u v : State) : ℝ :=
  if u.val < 2 then (if u = v then 2 else 3) else (if u = v then 3 else 1)

theorem mirror_involutive : Function.Involutive mirror := by
  intro u
  fin_cases u <;> norm_num [mirror]

theorem edge_reversal (u v : State) (h : edge u v) : edge (mirror v) (mirror u) := by
  fin_cases u <;> fin_cases v <;> norm_num [edge, orientation, mirror] at *

theorem weight_reversal (u v : State) (h : edge u v) :
    weight (mirror v) (mirror u) = weight u v := by
  fin_cases u <;> fin_cases v <;> norm_num [edge, orientation, mirror, weight] at *

theorem weight_lower (u v : State) : 1 ≤ weight u v := by
  unfold weight
  split_ifs <;> norm_num

theorem cheap_loop_orientation (q : State) (hq : weight q q ≤ 2) : orientation q := by
  fin_cases q <;> norm_num [weight, orientation] at *

theorem orientation_mirror (q : State) (hq : orientation q) : orientation (mirror q) := by
  fin_cases q <;> norm_num [orientation, mirror] at *

theorem orientation_mirror_ne (q : State) (hq : orientation q) : mirror q ≠ q := by
  fin_cases q <;> norm_num [orientation, mirror] at *

theorem orientation_arc (u v : State) (hu : orientation u) :
    0 ≤ weight u v - 2 ∧ (weight u v - 2 = 0 → u = v) := by
  fin_cases u <;> fin_cases v <;> norm_num [orientation, weight] at *

/-- In orientation mode, zero excess over density 2 forbids every direction change. -/
theorem orientation_walk_excess {u v : State} (a : Walk edge u v)
    (hu : orientation u) :
    0 ≤ a.excess weight 2 ∧ (a.excess weight 2 = 0 → u = v) := by
  induction a with
  | nil u => simp [Walk.excess, Walk.cost, Walk.length]
  | @cons u v w h tail ih =>
    have hv : orientation v := h.mp hu
    obtain ⟨hn, he⟩ := ih hv
    obtain ⟨han, hae⟩ := orientation_arc u v hu
    have hex : (Walk.cons h tail).excess weight 2 =
        (weight u v - 2) + tail.excess weight 2 := by
      simp only [Walk.excess, Walk.cost, Walk.length, Nat.cast_add, Nat.cast_one]
      ring
    rw [hex]
    refine ⟨add_nonneg han hn, ?_⟩
    intro hz
    have hzero : weight u v - 2 = 0 := by linarith
    have htail : tail.excess weight 2 = 0 := by linarith
    exact (hae hzero).trans (he htail)

/-- This five-state automaton has no deterministic mirror certificate at mean 2. -/
theorem no_certificate_at_two (q : State) (hq : weight q q ≤ 2)
    (a : Walk edge q (mirror q)) (d : Walk edge (mirror q) q) :
    ¬ (a.excess weight 2 + d.excess weight 2 ≤ 0) := by
  have ho := cheap_loop_orientation q hq
  obtain ⟨ha, hzero⟩ := orientation_walk_excess a ho
  obtain ⟨hd, _⟩ := orientation_walk_excess d (orientation_mirror q ho)
  intro hbudget
  have heq : a.excess weight 2 = 0 := by linarith
  exact orientation_mirror_ne q ho (hzero heq).symm

/-- Every closed output has cost at least its length. -/
theorem closed_cost_lower {u : State} (a : Walk edge u u) :
    (a.length : ℝ) ≤ a.cost weight := by
  have hn := Walk.cost_nonneg (reduced weight 1 (fun _ => 0))
    (fun u v _ => by simp only [reduced]; have h := weight_lower u v; linarith) a
  rw [Walk.cost_reduced] at hn
  simp only [one_mul, add_zero, sub_zero] at hn
  linarith


def two : Walk edge 2 2 :=
  .cons (v := 3) (by norm_num [edge, orientation])
    (.cons (by norm_num [edge, orientation]) (.nil 2))

def three : Walk edge 2 2 :=
  .cons (v := 3) (by norm_num [edge, orientation])
    (.cons (v := 4) (by norm_num [edge, orientation])
      (.cons (by norm_num [edge, orientation]) (.nil 2)))

theorem two_length : two.length = 2 := rfl

theorem three_length : three.length = 3 := rfl

theorem two_excess : two.excess weight 1 = 0 := by
  norm_num [two, Walk.excess, Walk.cost, Walk.length, weight, Fin.ext_iff]

theorem three_excess : three.excess weight 1 = 0 := by
  norm_num [three, Walk.excess, Walk.cost, Walk.length, weight, Fin.ext_iff]

/-- The explicit example has optimum density one at every cycle length at least three. -/
theorem optimum_one_every_length (n : ℕ) (hn : 3 ≤ n) :
    ∃ z : Walk edge 2 2, z.length = n ∧ z.cost weight = n := by
  by_cases h4 : 4 ≤ n
  · obtain ⟨i, j, hij⟩ := Walk.consecutive_decomposition 2 n (by decide) (by omega)
    let z := (two.iterate i).append (three.iterate j)
    have hlen : z.length = n := by
      dsimp [z]
      simpa only [Walk.length_append, Walk.length_iterate, two_length, three_length] using hij
    have hex : z.excess weight 1 = 0 := by
      dsimp [z]
      rw [Walk.excess_append, Walk.excess_iterate, Walk.excess_iterate,
        two_excess, three_excess]
      ring
    refine ⟨z, hlen, ?_⟩
    simp only [Walk.excess, hlen, one_mul] at hex
    linarith
  · have hn3 : n = 3 := by omega
    subst n
    refine ⟨three, three_length, ?_⟩
    norm_num [three, Walk.cost, weight, Fin.ext_iff]


def zeroLoop : Walk edge 0 0 :=
  .cons (by norm_num [edge, orientation]) (.nil 0)

def across : Walk edge 0 1 :=
  .cons (by norm_num [edge, orientation]) (.nil 1)

def back : Walk edge 1 0 :=
  .cons (by norm_num [edge, orientation]) (.nil 0)

theorem certificate_above_two (B : ℝ) (hB : 2 < B) :
    ∃ a : Walk edge 0 1, a.excess weight B + back.excess weight B ≤ 0 := by
  have hn : zeroLoop.excess weight B < 0 := by
    norm_num [zeroLoop, Walk.excess, Walk.cost, Walk.length, weight]
    linarith
  obtain ⟨k, hk⟩ := Walk.negative_excursion_pays weight B (.nil 0) zeroLoop across hn
    (-back.excess weight B)
  exact ⟨((Walk.nil 0).append (zeroLoop.iterate k)).append across, by linarith⟩

def Certificate (B : ℝ) : Prop :=
  ∃ q : State, weight q q ≤ B ∧
    ∃ a : Walk edge q (mirror q), ∃ d : Walk edge (mirror q) q,
      a.excess weight B + d.excess weight B ≤ 0

/-- The finite-certificate threshold is exactly the open interval (2,∞). -/
theorem certificate_iff (B : ℝ) : Certificate B ↔ 2 < B := by
  constructor
  · rintro ⟨q, hq, a, d, hbudget⟩
    by_contra h
    have hB : B ≤ 2 := by linarith
    apply no_certificate_at_two q (le_trans hq hB) a d
    have ha : a.excess weight 2 ≤ a.excess weight B := by
      unfold Walk.excess
      have hlen : (0 : ℝ) ≤ a.length := Nat.cast_nonneg _
      nlinarith
    have hd : d.excess weight 2 ≤ d.excess weight B := by
      unfold Walk.excess
      have hlen : (0 : ℝ) ≤ d.length := Nat.cast_nonneg _
      nlinarith
    linarith
  · intro hB
    obtain ⟨a, ha⟩ := certificate_above_two B hB
    refine ⟨0, ?_, ?_⟩
    · norm_num [weight]
      linarith
    · change ∃ a : Walk edge 0 1, ∃ d : Walk edge 1 0,
        a.excess weight B + d.excess weight B ≤ 0
      exact ⟨a, back, ha⟩

end OpenEndpoint

/-- No negative closed walk in a strongly connected weighted graph gives a
feasible potential. Finiteness is unnecessary: a fixed return walk bounds all
forward costs from below, so their infimum is well-defined. -/
theorem exists_feasible_potential_of_closed_nonneg
    (E : Q → Q → Prop) (c : Q → Q → ℝ) (root : Q)
    (hfrom : ∀ v, Nonempty (Walk E root v))
    (hto : ∀ v, Nonempty (Walk E v root))
    (hclosed : ∀ a : Walk E root root, 0 ≤ a.cost c) :
    ∃ p : Q → ℝ, ∀ u v, E u v → 0 ≤ c u v + p u - p v := by
  let costs (v : Q) : Set ℝ := {x | ∃ a : Walk E root v, a.cost c = x}
  have hne (v : Q) : (costs v).Nonempty := by
    obtain ⟨a⟩ := hfrom v
    exact ⟨a.cost c, a, rfl⟩
  have hbounded (v : Q) : BddBelow (costs v) := by
    obtain ⟨b⟩ := hto v
    refine ⟨-b.cost c, ?_⟩
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    have h := hclosed (a.append b)
    rw [Walk.cost_append] at h
    linarith
  refine ⟨fun v => sInf (costs v), ?_⟩
  intro u v huv
  have hbound : sInf (costs v) - c u v ≤ sInf (costs u) := by
    apply le_csInf (hne u)
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    let e : Walk E u v := .cons huv (.nil v)
    have he : e.cost c = c u v := by simp [e, Walk.cost]
    have h : sInf (costs v) ≤ (a.append e).cost c :=
      csInf_le (hbounded v) ⟨a.append e, rfl⟩
    rw [Walk.cost_append, he] at h
    linarith
  linarith

/-- A reversible strongly connected component whose closed walks have mean
at least b admits an antisymmetric feasible potential. -/
theorem exists_antisymmetric_potential
    (E : Q → Q → Prop) (rev : Q → Q) (hinv : Function.Involutive rev)
    (c : Q → Q → ℝ) (b : ℝ) (root : Q)
    (hfrom : ∀ v, Nonempty (Walk E root v))
    (hto : ∀ v, Nonempty (Walk E v root))
    (hrev : ∀ u v, E u v → E (rev v) (rev u))
    (hsym : ∀ u v, E u v → c (rev v) (rev u) = c u v)
    (hmean : ∀ a : Walk E root root, b * a.length ≤ a.cost c) :
    ∃ p : Q → ℝ, (∀ u, p (rev u) = -p u) ∧
      (∀ u v, E u v → 0 ≤ reduced c b p u v) := by
  have hn : ∀ a : Walk E root root, 0 ≤ a.cost (reduced c b (fun _ => 0)) := by
    intro a
    rw [Walk.cost_reduced]
    have h := hmean a
    linarith
  obtain ⟨p, hp⟩ := exists_feasible_potential_of_closed_nonneg E
    (reduced c b (fun _ => 0)) root hfrom hto hn
  have hp' : ∀ u v, E u v → 0 ≤ reduced c b p u v := by
    intro u v huv
    have h := hp u v huv
    simpa only [reduced, add_zero, sub_zero] using h
  exact ⟨mirrorPotential rev p, mirrorPotential_antisymm rev hinv p,
    mirrorPotential_feasible E rev c b p hrev hsym hp'⟩

/-- In a loop-free reversible automaton, an edge joining equal unordered
outward-state pairs has a self-mirror state, unique at each endpoint.
This is the algebraic core of the constant-coloring postprocessing. -/
theorem equal_pair_edge_is_matching {Q : Type*} (rev : Q → Q)
    (hinv : Function.Involutive rev) (E : Q → Q → Prop)
    (hloop : ∀ q, ¬ E q q) (a b d : Q) (hlocal : E (rev b) a)
    (hpair : (a = rev a ∧ b = d) ∨ (a = d ∧ b = rev a)) :
    a = rev a ∧ b ≠ a := by
  have ha : a = rev a := by
    rcases hpair with h | h
    · exact h.1
    · have hb : rev b = a := by rw [h.2, hinv a]
      exact False.elim (hloop a (hb ▸ hlocal))
  refine ⟨ha, ?_⟩
  intro hb
  have hab : rev b = a := by rw [hb, ← ha]
  exact hloop a (hab ▸ hlocal)

end LocalCycles

#print axioms LocalCycles.mirrorPotential_feasible
#print axioms LocalCycles.reduced_mirror_eq
#print axioms LocalCycles.Walk.closed_cost_eq_iff_tight
#print axioms LocalCycles.Walk.mirror_trip_tight

#print axioms LocalCycles.Walk.negative_cycle_mirror_certificate
#print axioms LocalCycles.Walk.tight_mirror_certificate

#print axioms LocalCycles.Walk.consecutive_walks_flexible
#print axioms LocalCycles.Walk.flexible_pair_fillings
#print axioms LocalCycles.Walk.reflected_anchor_connectors

#print axioms LocalCycles.OpenEndpoint.no_certificate_at_two
#print axioms LocalCycles.OpenEndpoint.closed_cost_lower

#print axioms LocalCycles.OpenEndpoint.optimum_one_every_length

#print axioms LocalCycles.OpenEndpoint.certificate_iff

#print axioms LocalCycles.Walk.finite_surgery_core

#print axioms LocalCycles.equal_pair_edge_is_matching

#print axioms LocalCycles.exists_feasible_potential_of_closed_nonneg

#print axioms LocalCycles.exists_antisymmetric_potential

#print axioms LocalCycles.Walk.optimal_on_multiples
