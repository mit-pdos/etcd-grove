/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/D4.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

D4 (the protocol unit's riskiest point): can the invariant's facts on `preds` (the replicas'
predicted execution sequences, D2 refined) be established and used to place RMWs?

A prophecy's value is arbitrary when it is created (`NewProph`: `∀ pvs, proph p pvs -∗ ...`); a
resolution only shows that what *this* replica executes is a prefix of *its own* prediction
(`ResolveU64`: `pvs = #x :: pvs'`). The lemma below is the pure core of the answer (no): any rule
that reads an RMW's place off the three predictions is wrong in some continuation that no
resolution ever contradicts. Two continuations from one state: replica 0 predicted `[a]`, replica
1 predicted `[b]` (the other order of the same two RMWs), replica 2 nothing; in one, replica 0
executes `a` first and replica 1 never executes; in the other, replica 1 executes `b` first and
replica 0 never executes. Each replica's executions are a prefix of its prediction and the executed
sequences agree (EPaxos), so neither continuation is ever refuted, yet the first chain entry (the
RMW's place) differs. The full argument (why both continuations are reachable from one protocol
state at the moment the frontier passes the RMW's place, before it is committed) is in
`notes/hub-requests.md` (H-U4-1).
-/
module

public import Dsverify.Proof.gryff.Proto.Model

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.proto.d4

/-- A continuation consistent with the predictions `pvs`: each replica's executed sequence `ex k`
is a prefix of its prediction (what resolutions check), and executed sequences agree (EPaxos). -/
def Consistent {E : Type} (pvs ex : Nat → List E) : Prop :=
  (∀ k, ex k <+: pvs k) ∧ ∀ k k', ex k <+: ex k' ∨ ex k' <+: ex k

/-- **No placement rule from the predictions is sound**: a rule `place` giving the first chain
entry from the predictions cannot equal the first entry executed in every consistent
continuation. -/
theorem prediction_placement_impossible {E : Type} (a b : E) (hab : a ≠ b)
    (place : (Nat → List E) → Option E) :
    ¬ ∀ (pvs ex : Nat → List E), Consistent pvs ex →
        ∀ k e rest, ex k = e :: rest → place pvs = some e := by
  intro h
  let pvs : Nat → List E := fun k => if k = 0 then [a] else if k = 1 then [b] else []
  let ex1 : Nat → List E := fun k => if k = 0 then [a] else []
  let ex2 : Nat → List E := fun k => if k = 1 then [b] else []
  have c1 : Consistent pvs ex1 := by
    refine ⟨fun k => ?_, fun k k' => ?_⟩
    · by_cases h0 : k = 0 <;> simp [pvs, ex1, h0]
    · by_cases h0 : k = 0 <;> by_cases h0' : k' = 0 <;> simp [ex1, h0, h0']
  have c2 : Consistent pvs ex2 := by
    refine ⟨fun k => ?_, fun k k' => ?_⟩
    · by_cases h1 : k = 1 <;> simp [pvs, ex2, h1]
    · by_cases h1 : k = 1 <;> by_cases h1' : k' = 1 <;> simp [ex2, h1, h1']
  have e1 := h pvs ex1 c1 0 a [] (by simp [ex1])
  have e2 := h pvs ex2 c2 1 b [] (by simp [ex2])
  rw [e1] at e2
  exact hab (Option.some.inj e2)

end Perennial.gryff.proto.d4
