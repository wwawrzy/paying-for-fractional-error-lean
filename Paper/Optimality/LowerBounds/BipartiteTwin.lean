import Paper.Optimality.LowerBounds.PortLocal
namespace Paper.BipartiteTwin

def pairRound {In Out Msg : Type} (R : PortLocal.Round In Out Msg) :
    PortLocal.Round (In × In) (Out × Out) (Msg × Msg) where
  send d C s p := (R.send d C s.1 p,R.send d C s.2 p)
  update d C s msg := (R.update d C s.1 (fun p => (msg p).2),R.update d C s.2 (fun p => (msg p).1))
def translate {In Out : Type} : PortLocal.Program In Out → PortLocal.Program (In × In) (Out × Out)
  | .local f => .local fun d C s => (f d C s.1,f d C s.2)
  | .round R => .round (pairRound R)
  | .seq P Q => .seq (translate P) (translate Q)
theorem rounds {In Out : Type} (P : PortLocal.Program In Out) : (translate P).rounds=P.rounds := by
  induction P with
  | «local» f => rfl
  | round R => rfl
  | seq P Q hP hQ => exact congrArg₂ (·+·) hP hQ

def mix {V X : Type} (color : V → Bool) (x y : V → X) (v : V) : X × X :=
  if color v then (x v,y v) else (y v,x v)

theorem run_mix {V In Out : Type} (N : PortLocal.Network V) (ids : V → ℕ)
    (color : V → Bool) (hcolor : ∀ v p, color (N.neighbor v p)=!(color v))
    (P : PortLocal.Program In Out) (x y : V → In) :
    (translate P).run N ids (mix color x y)=mix color (P.run N ids x) (P.run N ids y) := by
  induction P with
  | «local» f =>
    funext v
    cases hv : color v <;> simp [translate,PortLocal.Program.run,mix,hv]
  | round R =>
    funext v
    have hn := hcolor v
    cases hv : color v <;> simp [translate,PortLocal.Program.run,pairRound,mix,hv,hn]
  | seq P Q hP hQ =>
    simp only [translate,PortLocal.Program.run]
    rw [hP]
    exact hQ (P.run N ids x) (P.run N ids y)

/-- Two executions on opposite bipartitions can be run without supplying a
bipartition: exchange the two message channels at every physical edge. -/
def program (P : PortLocal.Program Bool Bool) : PortLocal.Program Unit Bool :=
  .seq (.local fun _ _ _ => (true,false))
    (.seq (translate P) (.local fun _ _ s => s.1 || s.2))
theorem program_rounds (P : PortLocal.Program Bool Bool) : (program P).rounds=P.rounds := by
  simp [program,PortLocal.Program.rounds,rounds]
theorem run_eq {V : Type} (N : PortLocal.Network V) (ids : V → ℕ)
    (color : V → Bool) (hcolor : ∀ v p, color (N.neighbor v p)=!(color v))
    (P : PortLocal.Program Bool Bool) :
    (program P).run N ids (fun _ => ()) = fun v =>
      P.run N ids color v || P.run N ids (fun u => !(color u)) v := by
  have hm : (fun _ => (true,false))=mix color color (fun v => !(color v)) := by
    funext v
    cases hv : color v <;> simp [mix,hv]
  simp only [program,PortLocal.Program.run]
  rw [hm,run_mix N ids color hcolor]
  funext v
  cases hv : color v <;> simp [mix,hv,Bool.or_comm]
end Paper.BipartiteTwin
#print axioms Paper.BipartiteTwin.run_eq
