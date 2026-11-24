/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Pure/Totality.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Totality (stage 2, unit A): in every reachable configuration, the step of every event a replica can
actually be offered is defined, except a free event whose guard fails.

* A message in flight to replica `r` (an unconsumed copy some replica sent it): its handler's
  step is `.ok` — neither `never` (every message kind and field the model sends is of the system's
  shape) nor `dead` (every `-- dead:` branch of the handlers is unreachable) nor `disabled` (only free
  events have guards).
* A free event (`recv = none`: a client request, the forced-write ticker, a recovery trigger, an
  execution) of the system's shape (`Ev.Producible`: client requests of the system's shape, key 0,
  no dependency (`D.Key < 0`, Go's own test), a client id ≥ 0): `.ok` or `disabled` (budget, a
  repeated key, the recovery trigger's and the execution's guards).

The handlers' refinement proofs (unit H*) refute a `dead` branch with these, from the facts that the
event is enabled in reality (its message's receive token, or a free event's guard).

No hypothesis on clients is needed: the model's client-request guard (`RState.used`, ghost) makes
a coordinator's keys `(client id, request id)` fresh; without it, a repeated key reaches a `dead`
branch (two leftover `Write2Reply`s of two completed writes with key K reach a third write with key K
before its `Write2`s are sent: `writeTag = nil` at `HandleWrite2Reply`'s quorum; see
`notes/stage2-pure-statements.md`).
-/
module

public import Dsverify.Proof.gryff.Pure.Run
public import Dsverify.Proof.gryff.Pure.Lin
import Dsverify.Proof.gryff.PureT.Total

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn

/-- A free event the system produces: client requests of the system's shape (key 0, no
dependency: `D.Key < 0`, Go's own test (`participant.go`: `if dep.Key >= 0`), the dependency's
other fields arbitrary; a client id ≥ 0: client ids are below 2^31). Stage 1's client grammar
(`Proto/WireDefs.reqBytesD`: `K' = 0`, `D'.Key' = -1`, `ClientId' = hs`) and the handshake's
`hs < peerMark` give each conjunct. Any timer, recovery trigger or execution. -/
def _root_.Perennial.gryff.model.Ev.Producible : Ev → Prop
  | .read _ cid k d => k = 0 ∧ sint.Z d.key < 0 ∧ 0 ≤ sint.Z cid
  | .write _ cid k _ d => k = 0 ∧ sint.Z d.key < 0 ∧ 0 ≤ sint.Z cid
  | .rmw _ cid k d _ _ => k = 0 ∧ sint.Z d.key < 0 ∧ 0 ≤ sint.Z cid
  | _ => True

/-- **Totality for messages.** A message in flight to replica `r` in a reachable configuration is
handled: its step is `.ok`. -/
theorem total_msg {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    (m : Msg) (hm : m ∈ c.inflight r) :
    ∃ s' o, stepR r (c.st r) (.msg m) = .ok (s', o) :=
  tot.total_msg' h r m hm

theorem total_msg_ne_never {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (r : Fin 3) (m : Msg) (hm : m ∈ c.inflight r) :
    stepR r (c.st r) (.msg m) ≠ .error .never := by
  obtain ⟨s', o, e⟩ := total_msg h r m hm
  rw [e]; intro h'; cases h'

theorem total_msg_ne_dead {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c)
    (r : Fin 3) (m : Msg) (hm : m ∈ c.inflight r) :
    stepR r (c.st r) (.msg m) ≠ .error .dead := by
  obtain ⟨s', o, e⟩ := total_msg h r m hm
  rw [e]; intro h'; cases h'

/-- **Totality for free events.** A free event of the system's shape is `.ok` or `disabled` at
every replica in a reachable configuration. -/
theorem total_free {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (r : Fin 3)
    (e : Ev) (he : e.recv = none) (hp : e.Producible) :
    (∃ s' o, stepR r (c.st r) e = .ok (s', o)) ∨ stepR r (c.st r) e = .error .disabled := by
  refine tot.total_free' h r e he (fun rid cid k d hk => ?_)
  rcases hk with rfl | ⟨v, rfl⟩ | ⟨oldV, newV, rfl⟩ <;> exact hp

/-! ## The free events' guards (per kind)

`disabled` is returned only by the free events' guards (the first lines of `stepClientRead`,
`stepClientWrite`, `stepClientRMW`, `stepRecover`, `stepExec`), so with the guard shown each step
is not `disabled` in any state; with `total_free` (not `never`, not `dead`) and `stepR_ok_of_ne`
it is `.ok`. `Proto2/Laws.lean`'s `step_ok_req` / `step_ok_recover` / `step_ok_exec` are their
Iris-level forms at a replica's trace. -/

/-- A step result that is none of the three failures is `.ok`. -/
theorem stepR_ok_of_ne {r : StepRes} (h1 : r ≠ .error .never) (h2 : r ≠ .error .disabled)
    (h3 : r ≠ .error .dead) : ∃ s' o, r = .ok (s', o) := by
  match r with
  | .ok (s', o) => exact ⟨s', o, rfl⟩
  | .error .never => exact absurd rfl h1
  | .error .disabled => exact absurd rfl h2
  | .error .dead => exact absurd rfl h3

/-- The forced-write ticker's step is always `.ok` (and changes nothing). -/
theorem stepR_forceWrite (k : Fin 3) (s : RState) : stepR k s .forceWrite = .ok (s, []) := rfl

/-- **A client request** with a fresh key (`(cid, rid) ∉ used`) under the budget is not
`disabled`. -/
theorem stepReq_ne_disabled (k : Fin 3) (s : RState) (e : Ev) {cid rid : w32}
    {i : dsverify_lab.harness.RegInput w64} (hr : e.clientReq = some (cid, rid, i)) (hu : (cid, rid) ∉ s.used)
    (hb : s.nReqs < 24) : stepR k s e ≠ .error .disabled :=
  tot.stepReq_ne_disabled' k s e hr hu hb

/-- **The recovery trigger** `(q, i)` with its guard (`q` a row, `0 ≤ i < crtInstance[q]`) is not
`disabled`. -/
theorem stepRecover_ne_disabled (k : Fin 3) (s : RState) (q i : w32) (hq : rowOk q = true)
    (h0 : 0 ≤ sint.Z i) (hc : sint.Z i < sint.Z (s.crt q)) :
    stepR k s (.recover q i) ≠ .error .disabled :=
  tot.stepRecover_ne_disabled' k s q i hq h0 hc

/-- **The execution** of `(q, i)` with its guard (in the box, committed, `execGuard`: a member of
the component the executor's search popped) is not `disabled`. -/
theorem stepExec_ne_disabled (k : Fin 3) (s : RState) (q i : w32) (c : Copy)
    (hb : inBox q i = true) (hc : s.inst q i = some c) (hs : c.status = St.COMMITTED)
    (hg : execGuard s (sint.Z q, sint.Z i)) :
    stepR k s (.exec q i) ≠ .error .disabled :=
  tot.stepExec_ne_disabled' k s q i c hb hc hs hg

end Perennial.gryff.pure
