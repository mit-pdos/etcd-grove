/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Pure/Run.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Runs of the global model (stage 2, the pure layer's common vocabulary): a run's labels, each
replica's state after a list of its events, a step's result and outputs at a replica's event or at
a run's label, the executor's result in a step's outputs.

A run is a list of labels `(replica, event)` (`kahn.GRun (Cfg.init gNet) l c`); replica `r`'s
events in it are `proj l r`. Everything about one replica is a function of its events (the model is
deterministic): `stOf r es` is its state after `es`. In a run every label's step is `.ok`
(`kahn.GStep`), so `stOf` never falls back to its default there.
-/
module

public import Dsverify.Proof.gryff.Model.Step

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn

/-- A run's label: a replica and the event it takes. -/
abbrev Label := Fin 3 × Ev

/-- Replica `r`'s events among labels `l` (`kahn.proj`). -/
noncomputable abbrev projR (l : List Label) (r : Fin 3) : List Ev := proj (N := gNet) l r

/-- A configuration reachable from the initial one. -/
def Reachable (c : Cfg gNet) : Prop := ∃ l, GRun (Cfg.init gNet) l c

/-- Replica `r`'s state after its events `es` (`kahn.runP`; `RState.init r` if some step fails,
which never happens for a run's projection). -/
noncomputable def stOf (r : Fin 3) (es : List Ev) : RState :=
  match runP gNet r es with
  | some (s, _) => s
  | none => RState.init r.val

/-- The result of replica `r`'s `j`-th event in `es` (from its state after the first `j`). -/
noncomputable def resOf (r : Fin 3) (es : List Ev) (j : Nat) : StepRes :=
  match es[j]? with
  | some e => stepR r (stOf r (es.take j)) e
  | none => .error .never

/-- The outputs of replica `r`'s `j`-th event in `es` (`[]` if its step fails). -/
noncomputable def outsOf (r : Fin 3) (es : List Ev) (j : Nat) : List Out :=
  match resOf r es j with
  | .ok (_, o) => o
  | .error _ => []

/-- The external outputs among `o`. -/
def extsIn (o : List Out) : List Ext :=
  o.filterMap fun x => match x with
    | .ext x => some x
    | .send _ _ => none

/-- The outputs of a run's label `n` (`[]` past the end). -/
noncomputable def outsAt (l : List Label) (n : Nat) : List Out :=
  match l[n]? with
  | some (r, e) =>
    match stepR r (stOf r (projR (l.take n) r)) e with
    | .ok (_, o) => o
    | .error _ => []
  | none => []

/-- The external outputs (client replies) of a run's label `n`. -/
noncomputable def extsAt (l : List Label) (n : Nat) : List Ext := extsIn (outsAt l n)

/-- The executor's result among a step's outputs: the `(v, t)` of its `ExecuteOverwrite` (only an
execution with a command has one). -/
def execRes (o : List Out) : Option ValTag :=
  o.findSome? fun x => match x with
    | .send _ (.executeOverwrite m) => some ⟨m.v, m.t⟩
    | _ => none

/-- A replica id as the model's word (`RState.id` of replica `r`). -/
def rid32 (r : Fin 3) : w32 := BitVec.ofNat 32 r.val

/-- Replica `r`'s state after the first `k` labels of `l`. -/
noncomputable def cutSt (l : List Label) (k : Nat) (r : Fin 3) : RState := stOf r (projR (l.take k) r)

end Perennial.gryff.pure
