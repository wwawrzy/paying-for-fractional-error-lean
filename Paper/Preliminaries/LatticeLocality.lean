import Paper.Preliminaries.LatticeBlockPorts
namespace Paper.LatticeBlock

def SameBox {q : ℕ} {A : Type} (r : ℕ) (f g : Delta q → A) (x y : Delta q) : Prop :=
  ∀ d : Delta q, (∀ i, -(r:ℤ)  ≤  d i ∧ d i  ≤  r) →
    f (fun i => x i+d i)=g (fun i => y i+d i)

theorem SameBox.zero {q : ℕ} {A : Type} {r : ℕ} {f g : Delta q → A} {x y : Delta q}
    (h : SameBox r f g x y) : f x=g y := by
  simpa only [add_zero] using h (fun _=>0) (by intro i; dsimp only; omega)

theorem SameBox.mono {q : ℕ} {A : Type} {r R : ℕ} {f g : Delta q → A} {x y : Delta q}
    (h : SameBox R f g x y) (hr : r ≤ R) : SameBox r f g x y := by
  intro d hd
  apply h d
  intro i
  have hh:=hd i
  omega

theorem SameBox.shift {q : ℕ} {A : Type} {r s : ℕ} {f g : Delta q → A} {x y : Delta q}
    (h : SameBox (r+s) f g x y) (d : Delta q)
    (hd : ∀ i, -(s:ℤ) ≤ d i ∧ d i ≤ s) :
    SameBox r f g (fun i=>x i+d i) (fun i=>y i+d i) := by
  intro e he
  have hh:=h (fun i=>d i+e i) (by
    intro i
    have hh:=hd i
    have hh':=he i
    push_cast
    omega)
  simpa only [add_assoc] using hh

theorem lattice_context_eq {q s : ℕ} (O : Offsets q s) {ids ids' : Delta q → ℕ}
    {x y : Delta q} (h : SameBox s ids ids' x y) :
    (latticeNetwork O).context ids x=(latticeNetwork O).context ids' y := by
  change PortLocal.Context.mk _ _ = PortLocal.Context.mk _ _
  congr 1
  · exact h.zero
  · funext p
    exact h _ (O.bounded _ (enumeration O p).property)

theorem lattice_run_locality {q s : ℕ} (O : Offsets q s) {In Out : Type}
    (P : PortLocal.Program In Out) {ids ids' : Delta q→ℕ}
    {a a' : Delta q→In} {x y : Delta q}
    (hi : SameBox (s*(P.rounds+1)) ids ids' x y)
    (ha : SameBox (s*P.rounds) a a' x y) :
    P.run (latticeNetwork O) ids a x=P.run (latticeNetwork O) ids' a' y := by
  induction P generalizing x y with
  | «local» f =>
    have hc := lattice_context_eq O (hi.mono (by simp [PortLocal.Program.rounds]))
    exact congrArg₂ (f O.values.card) hc ha.zero
  | round R =>
    change R.update _ _ _ _ = R.update _ _ _ _
    have hc := lattice_context_eq O (hi.mono (by simp [PortLocal.Program.rounds];omega))
    rw [hc,ha.zero]
    congr 1
    funext p
    have hb := O.bounded _ (enumeration O p).property
    have hi' : SameBox (s+s) ids ids' x y := by
      simpa only [PortLocal.Program.rounds, mul_add, mul_one] using hi
    have hs := hi'.shift _ hb
    have ha' : SameBox s a a' x y := by
      simpa only [PortLocal.Program.rounds,mul_one] using ha
    have hh := ha' _ hb
    have hctx := lattice_context_eq O hs
    change R.send O.values.card ((latticeNetwork O).context ids (fun i=>x i+(enumeration O p).val i)) (a (fun i=>x i+(enumeration O p).val i)) (reversePort O p) =
      R.send O.values.card ((latticeNetwork O).context ids' (fun i=>y i+(enumeration O p).val i)) (a' (fun i=>y i+(enumeration O p).val i)) (reversePort O p)
    rw [hctx,hh]
  | seq P Q ihP ihQ =>
    apply ihQ
    · exact hi.mono (by simp only [PortLocal.Program.rounds];nlinarith)
    · intro d hd
      apply ihP
      · have he : s*((PortLocal.Program.seq P Q).rounds+1)=s*(P.rounds+1)+s*Q.rounds := by
          simp only [PortLocal.Program.rounds];ring
        rw [he] at hi
        exact hi.shift d hd
      · have he : s*(PortLocal.Program.seq P Q).rounds=s*P.rounds+s*Q.rounds := by
          simp only [PortLocal.Program.rounds];ring
        rw [he] at ha
        exact ha.shift d hd

theorem lattice_run_unit {q s : ℕ} (O : Offsets q s)
    (P : PortLocal.Program Unit Bool) {ids ids' : Delta q → ℕ} {x y : Delta q}
    (hi : SameBox (s*(P.rounds+1)) ids ids' x y) :
    P.run (latticeNetwork O) ids (fun _=>()) x=
      P.run (latticeNetwork O) ids' (fun _=>()) y :=
  lattice_run_locality O P hi (by intro d hd; rfl)

theorem lattice_translation {q s : ℕ} (O : Offsets q s)
    {In Out : Type} (P : PortLocal.Program In Out) (ids : Delta q→ℕ)
    (a : Delta q→In) (x d : Delta q) :
    P.run (latticeNetwork O) ids a (fun i=>x i+d i)=
    P.run (latticeNetwork O) (fun z=>ids (fun i=>z i+d i))
      (fun z=>a (fun i=>z i+d i)) x := by
  apply lattice_run_locality O P
  · intro e he
    congr 1
    funext i
    ring
  · intro e he
    congr 1
    funext i
    ring
end Paper.LatticeBlock
#print axioms Paper.LatticeBlock.lattice_run_locality
