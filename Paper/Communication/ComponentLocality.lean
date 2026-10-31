import Paper.Communication.EncodedProgram

/-! Programs executed on one graph cannot inspect inputs in another component.
This permits componentwise correctness proofs for one parallel execution,
without giving the program a component identifier or a global vertex list. -/
namespace Paper.ComponentLocality
open BroadcastModel

variable {V : Type} [Fintype V] [DecidableEq V]
variable (I : SimpleGraph V) [DecidableRel I.Adj]

/-- Agreement on a neighbor-closed set is preserved by every broadcast program. -/
theorem run_agreement {In Out : Type} (P : Program V In Out) (H : Set V)
    (hclosed : ∀ v ∈ H, ∀ w, I.Adj v w → w ∈ H) :
    ∀ (s t : V → In), (∀ v ∈ H, s v = t v) →
      ∀ v ∈ H, P.run I s v = P.run I t v := by
  induction P with
  | «local» f =>
    intro s t hs v hv
    change f v (I.neighborFinset v) (s v) = f v (I.neighborFinset v) (t v)
    rw [hs v hv]
  | broadcast b C R =>
    intro s t hs v hv
    change R.update v (I.neighborFinset v) (s v)
      (fun u => R.send u.val (I.neighborFinset u.val) (s u.val)) =
      R.update v (I.neighborFinset v) (t v)
        (fun u => R.send u.val (I.neighborFinset u.val) (t u.val))
    rw [hs v hv]
    congr 1
    funext u
    rw [hs u.val (hclosed v hv u.val (I.mem_neighborFinset v u.val |>.mp u.property))]
  | seq P Q ihP ihQ =>
    intro s t hs v hv
    exact ihQ (P.run I s) (P.run I t) (ihP s t hs) v hv

/-- The same independence holds for the literal encoded execution. -/
theorem encoded_agreement {In Out : Type} (P : Program V In Out) (H : Set V)
    (hclosed : ∀ v ∈ H, ∀ w, I.Adj v w → w ∈ H)
    (s t : V → In) (hs : ∀ v ∈ H, s v = t v) :
    ∀ v ∈ H, P.runEncoded I s v = P.runEncoded I t v := by
  simpa only [Program.runEncoded_eq_run] using run_agreement I P H hclosed s t hs

/-- Inputs outside the reachable component of v do not affect its output. -/
theorem component_agreement {In Out : Type} (P : Program V In Out)
    (s t : V → In) (v : V) (hs : ∀ w, I.Reachable v w → s w = t w) :
    P.runEncoded I s v = P.runEncoded I t v := by
  apply encoded_agreement I P {w | I.Reachable v w}
    (fun x hx y hxy => hx.trans hxy.reachable) s t hs v
  exact SimpleGraph.Reachable.refl v

end Paper.ComponentLocality

#print axioms Paper.ComponentLocality.run_agreement
#print axioms Paper.ComponentLocality.encoded_agreement
#print axioms Paper.ComponentLocality.component_agreement
