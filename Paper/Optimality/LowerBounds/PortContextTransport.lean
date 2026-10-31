import Paper.Optimality.LowerBounds.PortLocal
namespace Paper.PortLocal

def Context.transport {d e : ℕ} (h : d=e) (c : Context d) : Context e :=
  ⟨c.ident, fun p=>c.neighbors (Fin.cast h.symm p)⟩

theorem local_transport {In Out : Type} (f : (d : ℕ) → Context d → In → Out)
    {d e : ℕ} (h : d=e) (c : Context d) (a : In) :
    f d c a=f e (c.transport h) a := by subst e;rfl

theorem send_transport {In Out Msg : Type} (R : Round In Out Msg)
    {d e : ℕ} (h : d=e) (c : Context d) (a : In) (p : Fin d) :
    R.send d c a p=R.send e (c.transport h) a (Fin.cast h p) := by subst e;rfl

theorem update_transport {In Out Msg : Type} (R : Round In Out Msg)
    {d e : ℕ} (h : d=e) (c : Context d) (a : In) (msgs : Fin d → Msg) :
    R.update d c a msgs=R.update e (c.transport h) a (fun p=>msgs (Fin.cast h.symm p)) := by
  subst e;rfl
end Paper.PortLocal
#print axioms Paper.PortLocal.update_transport
