import Paper.Solver.Density.RationalRuntime
import Paper.Solver.Density.UnitDomination

/-! One actual broadcast normalizes unequal local fulfillment targets.
This is an execution component for a prospective degree-uniform solver,
not a claim that its unequal phase ranges have already been implemented. -/
namespace Paper.Density.RationalLocalNormalization
open BroadcastModel RationalRuntime SevenFoundation
open scoped BigOperators

variable {V : Type} [DecidableEq V]

def values (N : Finset V) (own : ℕ) (messages : N → ℕ) : Finset ℕ :=
  insert own (N.attach.image messages)

def minimum (N : Finset V) (own : ℕ) (messages : N → ℕ) : ℕ :=
  (values N own messages).min' ⟨own, Finset.mem_insert_self _ _⟩

theorem minimum_le_self (N : Finset V) (own : ℕ) (messages : N → ℕ) :
    minimum N own messages ≤ own :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem minimum_le_message (N : Finset V) (own : ℕ) (messages : N → ℕ) (u : N) :
    minimum N own messages ≤ messages u := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, Finset.mem_attach _ _, rfl⟩)

theorem le_minimum (N : Finset V) (own : ℕ) (messages : N → ℕ) (b : ℕ)
    (hown : b ≤ own) (hmsg : ∀ u, b ≤ messages u) : b ≤ minimum N own messages := by
  apply Finset.le_min'
  intro n hn
  rcases Finset.mem_insert.mp hn with he | hn
  · simpa only [he] using hown
  · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hn
    exact hmsg u

structure Input (M : ℕ) where
  primal : ℚ
  index : CappedCount.Count M

def round (m M : ℕ) : Round V (Input M) ℚ (CappedCount.Count M) where
  send _ _ s := s.index
  update _ N s messages :=
    s.primal / (m * (minimum N s.index.value.val (fun u => (messages u).value.val) + 1))

def program (m M : ℕ) : Program V (Input M) ℚ :=
  .broadcast (bits M) (countCode M) (round m M)

theorem resources (m M : ℕ) :
    (program (V := V) m M).rounds = 1 ∧ (program (V := V) m M).maxBits = bits M :=
  ⟨rfl, rfl⟩

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def localIndex {M : ℕ} (s : V → Input M) (v : V) : ℕ :=
  minimum (G.neighborFinset v) (s v).index.value.val
    (fun u => (s u).index.value.val)

theorem localIndex_le {M : ℕ} (s : V → Input M) {r v : V} (hr : r ∈ closed G v) :
    localIndex G s v ≤ (s r).index.value.val := by
  rcases (mem_closed G r v).mp hr with rfl | hr
  · exact minimum_le_self _ _ _
  · exact minimum_le_message _ _ _ ⟨r, (G.mem_neighborFinset v r).mpr hr⟩

theorem localIndex_lower {M : ℕ} (s : V → Input M) (v : V) (b : ℕ)
    (h : ∀ r ∈ closed G v, b ≤ (s r).index.value.val) : b ≤ localIndex G s v := by
  apply le_minimum
  · exact h v (self_mem_closed G v)
  · intro u
    exact h u ((mem_closed G u v).mpr (Or.inr ((G.mem_neighborFinset v u).mp u.property)))

theorem run_eq {M : ℕ} (s : V → Input M) (m : ℕ) (v : V) :
    (program m M).run G s v = (s v).primal / (target m (localIndex G s v) : ℚ) := by
  simp only [program, Program.run, eval, round, target, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rfl

noncomputable def decoded {M : ℕ} (m : ℕ) (s : V → Input M) (v : V) : ℝ :=
  (((program m M).run G s v : ℚ) : ℝ)

theorem decoded_eq {M : ℕ} (s : V → Input M) (m : ℕ) (v : V) :
    decoded G m s v = ((s v).primal : ℝ) / target m (localIndex G s v) := by
  unfold decoded
  rw [run_eq, Rat.cast_div, Rat.cast_natCast]

theorem feasible {M m : ℕ} (hm : 1 ≤ m) (s : V → Input M)
    (hpos : ∀ v, 0 ≤ (s v).primal)
    (hfulfilled : ∀ r, (target m (s r).index.value.val : ℝ) ≤
      ∑ v ∈ closed G r, ((s v).primal : ℝ)) :
    SevenFoundation.feasible (ordinary G) (decoded G m s) := by
  have ht (k : ℕ) : (0 : ℝ) < target m k := by
    unfold target
    have : 0 < m := by omega
    positivity
  apply (UnitDomination.ordinary_feasible G _).2
  refine ⟨?_, ?_⟩
  · intro v
    rw [decoded_eq]
    exact div_nonneg (by exact_mod_cast hpos v) (ht _).le
  · intro r
    change 1 ≤ ∑ v ∈ closed G r, decoded G m s v
    calc
      1 ≤ (∑ v ∈ closed G r, ((s v).primal : ℝ)) / target m (s r).index.value.val :=
        (le_div_iff₀ (ht _)).2 (by simpa using hfulfilled r)
      _ = ∑ v ∈ closed G r, ((s v).primal : ℝ) / target m (s r).index.value.val :=
        Finset.sum_div _ _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [decoded_eq]
        apply div_le_div_of_nonneg_left (by exact_mod_cast hpos v) (ht _)
        exact_mod_cast Nat.mul_le_mul_left m (Nat.add_le_add_right
          (localIndex_le G s ((closed_symm G v r).mp hv)) 1)

/-- A unit gradient of the local indices costs at most one factor of the
fixed accuracy base. This lemma does not assume a common maximum degree. -/
theorem pointwise_cost {M m : ℕ} (hm : 1 ≤ m) (s : V → Input M)
    (hpos : ∀ v, 0 ≤ (s v).primal)
    (hfloor : ∀ v, m ≤ (s v).index.value.val)
    (hgradient : ∀ v r, r ∈ closed G v →
      (s v).index.value.val ≤ (s r).index.value.val + 1) (v : V) :
    decoded G m s v ≤ (1 + 1 / (m : ℝ)) *
      (((s v).primal : ℝ) / target m (s v).index.value.val) := by
  have hmin := localIndex_lower G s v m (fun r _ => hfloor r)
  have hstep : (s v).index.value.val ≤ localIndex G s v + 1 := by
    have hh := localIndex_lower G s v ((s v).index.value.val - 1) (by
      intro r hr
      have hh := hgradient v r hr
      omega)
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hminR : (m : ℝ) ≤ localIndex G s v := by exact_mod_cast hmin
  have hstepR : ((s v).index.value.val : ℝ) ≤ localIndex G s v + 1 := by exact_mod_cast hstep
  have hF : (0 : ℝ) < target m (s v).index.value.val := by unfold target; positivity
  have hf : (0 : ℝ) < target m (localIndex G s v) := by unfold target; positivity
  have hratio : (target m (s v).index.value.val : ℝ) ≤
      (1 + 1 / (m : ℝ)) * target m (localIndex G s v) := by
    unfold target
    push_cast
    have he : (1 + 1 / (m : ℝ)) * ((m : ℝ) * (localIndex G s v + 1)) =
        ((m : ℝ) + 1) * (localIndex G s v + 1) := by field_simp <;> ring
    rw [he]
    nlinarith
  rw [decoded_eq]
  apply (div_le_iff₀ hf).2
  have he : (1 + 1 / (m : ℝ)) * (((s v).primal : ℝ) /
      target m (s v).index.value.val) * target m (localIndex G s v) =
      ((s v).primal : ℝ) * ((1 + 1 / (m : ℝ)) * target m (localIndex G s v)) /
        target m (s v).index.value.val := by ring
  rw [he]
  apply (le_div_iff₀ hF).2
  exact mul_le_mul_of_nonneg_left hratio (by exact_mod_cast hpos v)

theorem cost {M m : ℕ} (hm : 1 ≤ m) (s : V → Input M)
    (hpos : ∀ v, 0 ≤ (s v).primal)
    (hfloor : ∀ v, m ≤ (s v).index.value.val)
    (hgradient : ∀ v r, r ∈ closed G v →
      (s v).index.value.val ≤ (s r).index.value.val + 1) :
    (∑ v, decoded G m s v) ≤ (1 + 1 / (m : ℝ)) *
      ∑ v, (((s v).primal : ℝ) / target m (s v).index.value.val) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => pointwise_cost G hm s hpos hfloor hgradient v)

end Paper.Density.RationalLocalNormalization

#print axioms Paper.Density.RationalLocalNormalization.resources
#print axioms Paper.Density.RationalLocalNormalization.run_eq
#print axioms Paper.Density.RationalLocalNormalization.feasible
#print axioms Paper.Density.RationalLocalNormalization.pointwise_cost
#print axioms Paper.Density.RationalLocalNormalization.cost
