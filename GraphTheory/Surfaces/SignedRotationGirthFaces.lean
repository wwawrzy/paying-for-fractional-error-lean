import GraphTheory.Surfaces.SignedRotationFaceWalk
import GraphTheory.Surfaces.SignedRotationFaceFlags
import GraphTheory.Surfaces.SignedRotationEulerBound
namespace SimpleGraph.SignedRotation
variable {V : Type*} {G : SimpleGraph V} (r : SignedRotation G)
theorem edge_step_sandwich (x : Flag G) :
    r.faceStep (r.edgeFlip (r.faceStep x)) = r.edgeFlip x := by
  change r.cornerFlip (r.edgeFlip (r.edgeFlip (r.cornerFlip (r.edgeFlip x)))) = r.edgeFlip x
  rw [r.edgeFlip_involutive,r.cornerFlip_involutive]

theorem corner_step_sandwich (x : Flag G) :
    r.faceStep (r.cornerFlip (r.faceStep x)) = r.cornerFlip x := by
  change r.cornerFlip (r.edgeFlip (r.cornerFlip (r.cornerFlip (r.edgeFlip x)))) = r.cornerFlip x
  rw [r.cornerFlip_involutive,r.edgeFlip_involutive]

theorem edge_iterate_sandwich (n : ℕ) (x : Flag G) :
    (r.faceStep^[n]) (r.edgeFlip ((r.faceStep^[n]) x)) = r.edgeFlip x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply' r.faceStep n x,
      r.edge_step_sandwich,ih]

theorem corner_iterate_sandwich (n : ℕ) (x : Flag G) :
    (r.faceStep^[n]) (r.cornerFlip ((r.faceStep^[n]) x)) = r.cornerFlip x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply' r.faceStep n x,
      r.corner_step_sandwich,ih]

variable [Fintype V] [DecidableRel G.Adj]
theorem not_sameCycle_edgeFlip (x : Flag G) :
    ¬ r.faceStepPerm.SameCycle x (r.edgeFlip x) := by
  intro h
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  change (r.faceStepPerm ^ n) x = r.edgeFlip x at hn
  rw [Equiv.Perm.coe_pow] at hn
  change (r.faceStep^[n]) x = r.edgeFlip x at hn
  rcases Nat.even_or_odd n with ⟨i,hi⟩ | ⟨i,hi⟩
  · apply r.edgeFlip_ne_self ((r.faceStep^[i]) x)
    apply (r.faceStepPerm ^ i).injective
    change (r.faceStep^[i]) (r.edgeFlip ((r.faceStep^[i]) x)) =
      (r.faceStep^[i]) ((r.faceStep^[i]) x)
    rw [r.edge_iterate_sandwich,← Function.iterate_add_apply,← hi]
    exact hn.symm
  · let j := i+1
    have hj : j+j = n+1 := by omega
    have hn' : (r.faceStep^[j+j]) x = r.cornerFlip x := by
      rw [hj,Function.iterate_succ_apply',hn]
      change r.cornerFlip (r.edgeFlip (r.edgeFlip x)) = r.cornerFlip x
      rw [r.edgeFlip_involutive]
    apply r.cornerFlip_ne_self ((r.faceStep^[j]) x)
    apply (r.faceStepPerm ^ j).injective
    change (r.faceStep^[j]) (r.cornerFlip ((r.faceStep^[j]) x)) =
      (r.faceStep^[j]) ((r.faceStep^[j]) x)
    rw [r.corner_iterate_sandwich,← Function.iterate_add_apply,hn']
theorem sameCycle_edgeFlip_map {x y : Flag G} (h : r.faceStepPerm.SameCycle x y) :
    r.faceStepPerm.SameCycle (r.edgeFlip x) (r.edgeFlip y) := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  change (r.faceStep^[n]) x = y at hn
  have hh : (r.faceStepPerm ^ n) (r.edgeFlip y) = r.edgeFlip x := by
    rw [Equiv.Perm.coe_pow]
    change (r.faceStep^[n]) (r.edgeFlip y) = r.edgeFlip x
    rw [← hn]
    exact r.edge_iterate_sandwich n x
  exact (show r.faceStepPerm.SameCycle (r.edgeFlip y) (r.edgeFlip x) from
    ⟨(n : ℤ),by rw [zpow_natCast]; exact hh⟩).symm

variable [DecidableEq V]
noncomputable def orbitFlag (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x) (i : Fin g) : Flag G :=
  (r.faceStepPerm.toList x)[i.val]'(by rw [Equiv.Perm.length_toList]; exact i.isLt.trans_le hg)

theorem orbitFlag_sameCycle (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x) (i : Fin g) :
    r.faceStepPerm.SameCycle x (r.orbitFlag x g hg i) :=
  (Equiv.Perm.mem_toList_iff.mp (List.getElem_mem _)).1

theorem orbitFlag_injective (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x) :
    Function.Injective (r.orbitFlag x g hg) := by
  intro i j h
  apply Fin.ext
  exact (r.faceStepPerm.nodup_toList x).getElem_inj_iff.mp h

theorem orbitFlag_ne_reflected (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x) (i j : Fin g) :
    r.orbitFlag x g hg i ≠ r.edgeFlip (r.orbitFlag x g hg j) := by
  intro h
  have ha := r.orbitFlag_sameCycle x g hg i
  have hb := r.sameCycle_edgeFlip_map (r.orbitFlag_sameCycle x g hg j)
  rw [← h] at hb
  exact r.not_sameCycle_edgeFlip x (ha.trans hb.symm)

noncomputable def pairedOrbitFlag (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x)
    (i : Fin g × Bool) : Flag G :=
  if i.2 then r.edgeFlip (r.orbitFlag x g hg i.1) else r.orbitFlag x g hg i.1

theorem pairedOrbitFlag_injective (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x) :
    Function.Injective (r.pairedOrbitFlag x g hg) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  cases b <;> cases c <;> simp only [pairedOrbitFlag,Bool.false_eq_true,↓reduceIte] at h
  · exact Prod.ext (r.orbitFlag_injective x g hg h) rfl
  · exact False.elim (r.orbitFlag_ne_reflected x g hg i j h)
  · exact False.elim (r.orbitFlag_ne_reflected x g hg j i h.symm)
  · exact Prod.ext (r.orbitFlag_injective x g hg (r.edgeFlip_involutive.injective h)) rfl

@[simp] theorem faceOf_faceStep (x : Flag G) : r.faceOf (r.faceStep x) = r.faceOf x := by
  simp only [faceStep,r.faceOf_cornerFlip,r.faceOf_edgeFlip]

theorem faceOf_sameCycle {x y : Flag G} (h : r.faceStepPerm.SameCycle x y) : r.faceOf y = r.faceOf x := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  change (r.faceStep^[n]) x = y at hn
  have hp : ∀ n : ℕ, r.faceOf ((r.faceStep^[n]) x) = r.faceOf x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply',r.faceOf_faceStep,ih]
  rw [← hn]
  exact hp n

theorem faceOf_pairedOrbitFlag (x : Flag G) (g : ℕ) (hg : g ≤ r.facePeriod x) (i : Fin g × Bool) :
    r.faceOf (r.pairedOrbitFlag x g hg i) = r.faceOf x := by
  have hh := r.faceOf_sameCycle (r.orbitFlag_sameCycle x g hg i.1)
  cases hb : i.2 <;> simp only [pairedOrbitFlag,hb,Bool.false_eq_true,↓reduceIte,r.faceOf_edgeFlip,hh]

theorem girth_face_flag_bound (hdeg : ∀ v, 2 ≤ G.degree v) (g : ℕ)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    2 * g * Nat.card r.Face ≤ Fintype.card (Flag G) := by
  classical
  letI : Finite r.Face := Finite.of_surjective r.faceOf (fun q => Quotient.exists_rep q)
  letI : Fintype r.Face := Fintype.ofFinite _
  let f : r.Face × (Fin g × Bool) → Flag G := fun z =>
    r.pairedOrbitFlag z.1.out g (r.facePeriod_ge_girth hdeg g hg z.1.out) z.2
  have hi : Function.Injective f := by
    rintro ⟨a,i⟩ ⟨b,j⟩ h
    have hab : a = b := by
      have hh := congrArg r.faceOf h
      change r.faceOf (r.pairedOrbitFlag a.out g _ i) = r.faceOf (r.pairedOrbitFlag b.out g _ j) at hh
      rw [r.faceOf_pairedOrbitFlag,r.faceOf_pairedOrbitFlag] at hh
      simpa only [faceOf,Quotient.out_eq] using hh
    subst b
    exact Prod.ext rfl (r.pairedOrbitFlag_injective a.out g _ h)
  have hh := Fintype.card_le_of_injective f hi
  simpa [Fintype.card_prod,Nat.card_eq_fintype_card,
    Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh

theorem girth_face_edge_bound (hdeg : ∀ v, 2 ≤ G.degree v) (g : ℕ)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    g * Nat.card r.Face ≤ 2 * G.edgeFinset.card := by
  have hh := r.girth_face_flag_bound hdeg g hg
  rw [flag_card] at hh
  rw [Nat.mul_assoc] at hh
  omega

theorem girth_euler_mul_bound (hdeg : ∀ v, 2 ≤ G.degree v) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    ((g : ℤ)-2) * G.edgeFinset.card ≤ (g : ℤ) * (Fintype.card V + r.eulerGenus) := by
  have hf : (g : ℤ) * (Nat.card r.Face : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) := by
    exact_mod_cast r.girth_face_edge_bound hdeg g hg
  have hv : (Nat.card r.Vertex : ℤ) ≤ Fintype.card V := by exact_mod_cast r.vertex_card_le
  have hc : (0 : ℤ) ≤ Nat.card r.Component := by positivity
  have he : (Nat.card r.Edge : ℤ) = G.edgeFinset.card := by exact_mod_cast r.edge_card
  have hEuler : (G.edgeFinset.card : ℤ) ≤ Fintype.card V + Nat.card r.Face + r.eulerGenus := by
    unfold eulerGenus eulerCharacteristic
    rw [he]
    omega
  have hgpos : (0 : ℤ) ≤ g := by positivity
  have hm := mul_le_mul_of_nonneg_left hEuler hgpos
  nlinarith

theorem girth_euler_bound (hdeg : ∀ v, 2 ≤ G.degree v) (g : ℕ) (hg3 : 3 ≤ g)
    (hg : ∀ (v : V) (c : G.Walk v v), c.IsCycle → g ≤ c.length) :
    (G.edgeFinset.card : ℝ) ≤ (g : ℝ) / ((g : ℝ)-2) * (Fintype.card V + (r.eulerGenus : ℝ)) := by
  have hm : ((g : ℝ)-2) * G.edgeFinset.card ≤ (g : ℝ) * (Fintype.card V + (r.eulerGenus : ℝ)) := by
    exact_mod_cast r.girth_euler_mul_bound hdeg g hg3 hg
  have hpos : 0 < (g : ℝ)-2 := by exact_mod_cast (show (0 : ℤ) < (g : ℤ)-2 by omega)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  nlinarith

end SimpleGraph.SignedRotation



