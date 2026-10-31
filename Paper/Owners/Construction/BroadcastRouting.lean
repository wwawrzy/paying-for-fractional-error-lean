import Paper.Communication.BroadcastModel

/-! Receiver-independent packets with a public target header. Every
neighbor receives the same packet and locally keeps a matching target.
The sum of all received masses equals the sum of all sent masses. -/
namespace Paper.BroadcastRouting
variable {V A : Type} [DecidableEq V] [AddCommMonoid A]

def payload (target : V) (packet : Option (V × A)) : A :=
  match packet with
  | none => 0
  | some p => if p.1 = target then p.2 else 0

def mass (packet : Option (V × A)) : A :=
  match packet with
  | none => 0
  | some p => p.2

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def received (packets : V → Option (V × A)) (v : V) : A :=
  ∑ w ∈ G.neighborFinset v, payload v (packets w)

theorem conservation (packets : V → Option (V × A))
    (hedge : ∀ v u a, packets v = some (u, a) → G.Adj v u) :
    ∑ v, received G packets v = ∑ v, mass (packets v) := by
  have he (v : V) : received G packets v =
      ∑ w, if G.Adj v w then payload v (packets w) else 0 := by
    rw [received, ← Finset.sum_filter]
    congr 1
    ext w
    simp
  simp only [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  cases hp : packets w with
  | none => simp [payload, mass]
  | some p =>
    obtain ⟨u, a⟩ := p
    have hu : G.Adj u w := (hedge w u a hp).symm
    simp only [payload, mass]
    rw [Finset.sum_eq_single u]
    · simp [hu]
    · intro v _ hv
      simp [Ne.symm hv]
    · simp
end Paper.BroadcastRouting
